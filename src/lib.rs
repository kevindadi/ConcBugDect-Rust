//! The general rustc plugin framework.
//! Inspired by <https://github.com/facebookexperimental/MIRAI/blob/9cf3067309d591894e2d0cd9b1ee6e18d0fdd26c/checker/src/main.rs>
//!
//! `RUSTC_LOG` is rustc's own logger (`init_rustc_env_logger`).
//! `SPN_LOG` and `SPN_LOG_STYLE` are this crate's `env_logger`.
//! The two systems do not share a filter.
#![feature(deref_patterns)]
#![feature(rustc_private)]

pub mod analysis;
pub mod cache;
pub mod callback;
pub mod config;
pub mod display;
pub mod options;
pub mod pipeline;
pub mod report;
pub mod translate;
pub mod util;

extern crate rustc_abi;
extern crate rustc_attr_ir;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_symbol_mangling;

use callback::SpnCallbacks;
use log::debug;
use options::Options;
use rustc_session::{EarlyDiagCtxt, config::ErrorOutputType};
use std::process::ExitCode;
use std::sync::Mutex;

/// Crate name attached to an ICE note. Filled from `-p` when that flag is
/// present, then overwritten with `tcx.crate_name` once the session exists.
/// A poisoned lock is ignored: this runs from a panic hook.
static ICE_CRATE_NAME: Mutex<String> = Mutex::new(String::new());

pub(crate) fn note_ice_crate_name(name: &str) {
    if let Ok(mut slot) = ICE_CRATE_NAME.lock() {
        *slot = name.to_string();
    }
}

pub fn run() -> ExitCode {
    // Direct `spn --help` prints the analyzer flags. A rustc-wrapper
    // invocation starts with the `rustc` argv, so its `--help` stays rustc's.
    if std::env::args()
        .nth(1)
        .is_some_and(|arg| arg == "--help" || arg == "-h")
    {
        options::print_help();
        println!();
        return ExitCode::SUCCESS;
    }

    // Initialize loggers.
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    if std::env::var("RUSTC_LOG").is_ok() {
        rustc_driver::init_rustc_env_logger(&handler);
    }

    if std::env::var("SPN_LOG").is_ok() {
        let e = env_logger::Env::new()
            .filter("SPN_LOG")
            .write_style("SPN_LOG_STYLE");
        env_logger::init_from_env(e);
    }
    // Get any options specified via the SPN_FLAGS environment variable
    let mut options = Options::default();
    options.parse_from_str(&std::env::var("SPN_FLAGS").unwrap_or_default(), &handler);
    debug!("SPN options from environment: {options:?}");
    let mut args = std::env::args_os()
        .enumerate()
        .map(|(i, arg)| {
            arg.into_string().unwrap_or_else(|arg| {
                handler.early_fatal(format!("Argument {i} is not valid Unicode: {arg:?}"))
            })
        })
        .collect::<Vec<_>>();
    assert!(!args.is_empty());

    // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we remove it if present.
    if args.len() > 1 && std::path::Path::new(&args[1]).file_stem() == Some("rustc".as_ref()) {
        args.remove(1);
    }

    // Also accept `--export-concir-net` / `--codegen-map` directly on the CLI
    // (or `spn <spn_flags> -- <rustc_args>`) in addition to `SPN_FLAGS`.
    if let Some(sep) = args.iter().position(|a| a == "--") {
        let spn_cli = args[1..sep].to_vec();
        if !spn_cli.is_empty() {
            let mut merged_args = Vec::new();
            if let Ok(env_flags) = std::env::var("SPN_FLAGS") {
                if !env_flags.trim().is_empty() {
                    merged_args.extend(shellwords::split(&env_flags).unwrap_or_else(|e| {
                        handler.early_fatal(format!("Cannot parse argument string: {e:?}"))
                    }));
                }
            }
            merged_args.extend(spn_cli);
            options.parse_from_args(&merged_args);
        }
        let mut rest = Vec::with_capacity(args.len() - sep);
        rest.push(args[0].clone());
        rest.extend_from_slice(&args[sep + 1..]);
        args = rest;
    } else {
        let mut i = 1;
        let mut stripped = Vec::with_capacity(args.len());
        stripped.push(args[0].clone());
        while i < args.len() {
            if args[i] == "--export-concir-net" && i + 1 < args.len() {
                options.export_concir_net = Some(std::path::PathBuf::from(&args[i + 1]));
                options.config.reduce_net = false;
                i += 2;
            } else if let Some(val) = args[i].strip_prefix("--export-concir-net=") {
                options.export_concir_net = Some(std::path::PathBuf::from(val));
                options.config.reduce_net = false;
                i += 1;
            } else if args[i] == "--codegen-map" && i + 1 < args.len() {
                options.codegen_map = Some(std::path::PathBuf::from(&args[i + 1]));
                i += 2;
            } else if let Some(val) = args[i].strip_prefix("--codegen-map=") {
                options.codegen_map = Some(std::path::PathBuf::from(val));
                i += 1;
            } else {
                stripped.push(args[i].clone());
                i += 1;
            }
        }
        args = stripped;
    }

    let mut rustc_command_line_arguments = args;
    if options.export_concir_net.is_some() {
        options.infer_crate_name_from_rustc_args(&rustc_command_line_arguments);
        options.crate_name = options.crate_name.replace('-', "_");
    }
    if !options.crate_name.is_empty() {
        note_ice_crate_name(&options.crate_name);
    }
    // One hook. `panic::update_hook` chains, so a second call would print a
    // second banner. `ice_extra_info` must not panic.
    rustc_driver::install_ice_hook(
        "https://github.com/kevindadi/SymbolicPetriNet/issues/new",
        ice_extra_info,
    );

    rustc_driver::catch_with_exit_code(|| {
        let print = "--print=";
        if rustc_command_line_arguments
            .iter()
            .any(|arg| arg.starts_with(print))
        {
            // If a --print option is given on the command line we wont get called to analyze anything.
        } else {
            let sysroot = "--sysroot";
            if !rustc_command_line_arguments
                .iter()
                .any(|arg| arg.starts_with(sysroot))
            {
                // Tell compiler where to find the std library and so on.
                rustc_command_line_arguments.push(format!("{sysroot}={}", find_sysroot()));
            }

            let always_encode_mir = "always-encode-mir";
            if !rustc_command_line_arguments
                .iter()
                .any(|arg| arg.ends_with(always_encode_mir))
            {
                // Tell compiler to emit MIR into crate for every function with a body.
                rustc_command_line_arguments.push(format!("-Z{always_encode_mir}"));
            }
        }

        let mut callbacks = SpnCallbacks::new(options);
        debug!("rustc_command_line_arguments {rustc_command_line_arguments:?}");
        rustc_driver::compiler_entrypoint(&rustc_command_line_arguments, &mut callbacks);
    })
}

fn ice_extra_info(dcx: rustc_errors::DiagCtxtHandle<'_>) {
    let flags = std::env::var("SPN_FLAGS").unwrap_or_default();
    let crate_name = ICE_CRATE_NAME
        .lock()
        .map(|slot| slot.clone())
        .unwrap_or_default();
    let mut text = format!("SPN_FLAGS: {flags}");
    if !crate_name.is_empty() {
        text.push_str("\ncrate: ");
        text.push_str(&crate_name);
    }
    let _ = dcx.struct_note(text).emit();
}

fn find_sysroot() -> String {
    // Prefer the environment of the *running* process so the driver follows the
    // toolchain it is actually invoked under; the values baked in at build time
    // are only a fallback (they can point at the machine/toolchain name that
    // built the binary).
    fn var(name: &str, baked: Option<&'static str>) -> Option<String> {
        std::env::var(name)
            .ok()
            .or_else(|| baked.map(str::to_owned))
    }

    let home = var("RUSTUP_HOME", option_env!("RUSTUP_HOME"));
    let toolchain = var("RUSTUP_TOOLCHAIN", option_env!("RUSTUP_TOOLCHAIN"));
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => var("RUST_SYSROOT", option_env!("RUST_SYSROOT")).expect(
            "Could not find sysroot. Specify the RUST_SYSROOT environment variable, \
                 or use rustup to set the compiler to use for LOCKBUD",
        ),
    }
}
