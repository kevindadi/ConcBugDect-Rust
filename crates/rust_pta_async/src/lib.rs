//! RustPTA async extension library.
//!
//! Async alias analysis, extended MIR translation, and related features live here.
//! The core package [`rust_petri_net_analysis`] under `/src` is treated as frozen baseline logic.

#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

pub mod callback;
pub mod detect;
pub mod memory;
pub mod translate;
pub mod transition;

use callback::AsyncPTACallbacks;
use log::debug;
use rustc_session::{EarlyDiagCtxt, config::ErrorOutputType};
use rust_petri_net_analysis::options::Options;
use std::process::ExitCode;

/// Re-export commonly used core types so async code does not deep-import paths.
pub use rust_petri_net_analysis::{
    analysis, callback as core_callback, concurrency, config, detect as core_detect,
    memory as core_memory, net, options, report, translate as core_translate, util,
};

pub fn run() -> ExitCode {
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    if std::env::var("RUSTC_LOG").is_ok() {
        rustc_driver::init_rustc_env_logger(&handler);
    }
    if std::env::var("PN_LOG").is_ok() {
        let e = env_logger::Env::new()
            .filter("PN_LOG")
            .write_style("PN_LOG_STYLE");
        env_logger::init_from_env(e);
    }

    let mut options = Options::default();
    options.parse_from_str(&std::env::var("PN_FLAGS").unwrap_or_default(), &handler);
    debug!("PN-ASYNC options from environment: {options:?}");

    let mut args = std::env::args_os()
        .enumerate()
        .map(|(i, arg)| {
            arg.into_string().unwrap_or_else(|arg| {
                handler.early_fatal(format!("Argument {i} is not valid Unicode: {arg:?}"))
            })
        })
        .collect::<Vec<_>>();
    assert!(!args.is_empty());

    if args.len() > 1 && std::path::Path::new(&args[1]).file_stem() == Some("rustc".as_ref()) {
        args.remove(1);
    }

    let mut rustc_command_line_arguments = args;
    rustc_driver::install_ice_hook("petri net async", |_| ());

    rustc_driver::catch_with_exit_code(|| {
        let print = "--print=";
        if !rustc_command_line_arguments
            .iter()
            .any(|arg| arg.starts_with(print))
        {
            let sysroot = "--sysroot";
            if !rustc_command_line_arguments
                .iter()
                .any(|arg| arg.starts_with(sysroot))
            {
                rustc_command_line_arguments
                    .push(format!("{sysroot}={}", core_util_sysroot()));
            }

            let always_encode_mir = "always-encode-mir";
            if !rustc_command_line_arguments
                .iter()
                .any(|arg| arg.ends_with(always_encode_mir))
            {
                rustc_command_line_arguments.push(format!("-Z{always_encode_mir}"));
            }
        }

        let mut callbacks = AsyncPTACallbacks::new(options);
        debug!("rustc_command_line_arguments {rustc_command_line_arguments:?}");
        rustc_driver::run_compiler(&rustc_command_line_arguments, &mut callbacks);
    })
}

fn core_util_sysroot() -> String {
    let home = option_env!("RUSTUP_HOME");
    let toolchain = option_env!("RUSTUP_TOOLCHAIN");
    #[allow(clippy::option_env_unwrap)]
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("Could not find sysroot. Set RUST_SYSROOT or use rustup.")
            .to_owned(),
    }
}
