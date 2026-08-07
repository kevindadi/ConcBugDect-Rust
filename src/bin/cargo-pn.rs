use std::env;
use std::ffi::OsString;
use std::process::Command;

const CARGO_PN_HELP: &str = r#"Petri Net-based Analysis Tool for Rust Programs

USAGE:
    cargo pn [OPTIONS] [-- <rustc-args>...]

OPTIONS:
    -h, --help                     Print help information
    -V, --version                  Print version information
    -m, --mode <TYPE>              Analysis mode:
                                   - deadlock: Deadlock detection
                                   - datarace: Data race detection
                                   - atomic: Atomicity Violation detection
                                   - pointsto: Standalone pointer analysis
                                   - [default: deadlock]
    -p, --pn-crate <NAME>          Target crate for analysis
    --pn-analysis-dir=<PATH>       Directory for Petri net analysis outputs
    --report-level <LEVEL>         Report audience: developer or research [default: developer]
    --full                         Translate all functions (disables entry-reachable and concurrent-roots filtering)
    --no-concurrent-roots          Disable translating functions that use locks/atomics/condvars/channels (and their callees)

VISUALIZATION OPTIONS:
        --viz-callgraph            Generate call graph visualization
        --viz-petrinet             Generate Petri net visualization
        --viz-stategraph           Generate state graph visualization
        --viz-unsafe               Generate unsafe operations report
        --viz-pointsto             Generate points-to relations report

EXAMPLES:
    cargo pn -m datarace -t my_crate
    cargo pn -m all -o results.json --viz-petrinet
    cargo pn -t my_lib --type library --api-spec apis.json
"#;

fn show_help() {
    println!("{}", CARGO_PN_HELP);
}

fn show_version() {
    println!("PetriNet for detecting concurrency bugs 0.0.1");
}

fn cargo() -> Command {
    Command::new(env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo")))
}

fn has_arg_flag(name: &str) -> bool {
    let mut args = std::env::args().take_while(|val| val != "--");
    args.any(|val| val == name)
}

fn in_cargo_pta() {
    let mut cmd = cargo();
    cmd.arg("build");
    cmd.env("RUSTC_WRAPPER", "pn");
    cmd.env("RUST_BACKTRACE", "full");

    // Pass PN_LOG if specified by the user. Default to info if not specified.
    const PN_LOG: &str = "PN_LOG";
    let log_level = env::var(PN_LOG).ok();
    cmd.env(PN_LOG, log_level.as_deref().unwrap_or("info"));

    let mut args = std::env::args().skip(2);

    let flags: Vec<_> = args.by_ref().take_while(|arg| arg != "--").collect();
    let flags = flags.join(" ");
    let contains_target_crate = flags.contains("-p");
    if !contains_target_crate {
        eprintln!("Target crate is required");
        return;
    }
    cmd.env("PN_FLAGS", flags);

    let exit_status = cmd
        .args(args)
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo?");
    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1))
    };
}

fn main() {
    if has_arg_flag("--help") || has_arg_flag("-h") {
        show_help();
        return;
    }

    if has_arg_flag("--version") || has_arg_flag("-V") {
        show_version();
        return;
    }

    if let Some("pn") = std::env::args().nth(1).as_deref() {
        in_cargo_pta();
    }
}
