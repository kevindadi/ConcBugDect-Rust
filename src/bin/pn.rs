#![feature(rustc_private)]
#![warn(non_snake_case)]

fn main() -> std::process::ExitCode {
    conc_bug_detector::run()
}
