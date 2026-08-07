#![feature(rustc_private)]

//! Export a minimal CIR JSON from stdin args (framework CLI).
//!
//! Future: accept Petri-net snapshot path or integrate with analysis output directory.

use std::env;
use std::process::ExitCode;

use rust_petri_net_analysis::net::Net;
use rust_petri_net_analysis::net::structure::{Place, PlaceType, Transition, TransitionType};
use rust_pta_cir::{PnToCirOptions, convert_net_to_cir, write_cir_json_pretty};

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 || args.iter().any(|a| a == "-h" || a == "--help") {
        eprintln!("Usage: pn-cir-export <output.json> [program_name]");
        eprintln!();
        eprintln!("Framework stub: emits a demo CIR JSON converted from a built-in sample net.");
        eprintln!("Validate: ceir <output.json>");
        return ExitCode::from(if args.len() < 2 { 2 } else { 0 });
    }

    let out = &args[1];
    let program_name = args.get(2).map(String::as_str).unwrap_or("demo");

    let net = demo_net();
    let (program, report) = convert_net_to_cir(&net, PnToCirOptions::new(program_name));
    log::info!(
        "converted {} places, {} transitions → {} resources, {} functions",
        report.place_count,
        report.transition_count,
        report.resource_count,
        report.function_count
    );

    if let Err(err) = write_cir_json_pretty(&program, out) {
        eprintln!("error writing CIR: {err}");
        return ExitCode::from(1);
    }
    println!("wrote {out}");
    ExitCode::SUCCESS
}

fn demo_net() -> Net {
    let mut net = Net::empty();
    let main_start = net.add_place(Place::new(
        "main_start",
        1,
        1,
        PlaceType::FunctionStart,
        String::new(),
    ));
    let _main_end = net.add_place(Place::new(
        "main_end",
        0,
        1,
        PlaceType::FunctionEnd,
        String::new(),
    ));
    let worker_start = net.add_place(Place::new(
        "worker_start",
        0,
        1,
        PlaceType::FunctionStart,
        String::new(),
    ));
    let mtx = net.add_place(Place::new("mtx", 1, 1, PlaceType::Resources, String::new()));

    let spawn = net.add_transition(Transition::new_with_transition_type(
        "main_spawn",
        TransitionType::Spawn("worker".into()),
    ));
    let join = net.add_transition(Transition::new_with_transition_type(
        "main_join",
        TransitionType::Join("worker".into()),
    ));
    let lock = net.add_transition(Transition::new_with_transition_type(
        "worker_lock",
        TransitionType::Lock(0),
    ));

    net.add_input_arc(main_start, spawn, 1);
    net.add_output_arc(worker_start, spawn, 1);
    net.add_input_arc(main_start, join, 1);
    net.add_input_arc(mtx, lock, 1);

    net
}
