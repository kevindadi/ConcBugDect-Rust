use std::env;
use std::ffi::OsString;
use std::process::Command;

const CARGO_PN_ASYNC_HELP: &str = r#"RustPTA async — Petri Net analysis for async Rust (experimental)

USAGE:
    cargo pn-async [OPTIONS] [-- <rustc-args>...]

This wrapper sets RUSTC_WRAPPER=pn-async and forwards PN_FLAGS to the async driver.
Core `cargo pn` / `pn` remain unchanged.

OPTIONS:
    -h, --help                     Print help information
    (all other flags are forwarded to pn-async; see `pn-async --help`)

EXAMPLES:
    cargo pn-async -m deadlock -p your_crate --viz-petrinet
"#;

fn show_help() {
    println!("{}", CARGO_PN_ASYNC_HELP);
}

fn cargo() -> Command {
    Command::new(env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo")))
}

fn has_arg_flag(name: &str) -> bool {
    let mut args = std::env::args().take_while(|val| val != "--");
    args.any(|val| val == name)
}

fn main() {
    if has_arg_flag("-h") || has_arg_flag("--help") {
        show_help();
        return;
    }

    let mut cmd = cargo();
    cmd.arg("build");
    cmd.env("RUSTC_WRAPPER", "pn-async");
    cmd.env("RUST_BACKTRACE", "full");

    const PN_LOG: &str = "PN_LOG";
    let log_level = env::var(PN_LOG).ok();
    cmd.env(PN_LOG, log_level.as_deref().unwrap_or("info"));

    let mut args = std::env::args().skip(2);
    let flags: Vec<_> = args.by_ref().take_while(|arg| arg != "--").collect();
    cmd.env("PN_FLAGS", flags.join(" "));

    let exit_status = cmd
        .args(args)
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo");
    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1));
    }
}
