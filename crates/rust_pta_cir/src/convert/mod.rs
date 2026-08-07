//! Petri net → CIR conversion pipeline.

mod functions;
mod ops;
mod resources;

use rust_petri_net_analysis::net::Net;

use crate::ast::Program;

pub use functions::{build_functions, discover_functions};
pub use ops::transition_to_op;
pub use resources::{concurrency_transition_ids, extract_resources};

/// Options for Petri-net → CIR conversion.
#[derive(Debug, Clone)]
pub struct PnToCirOptions {
    pub program_name: String,
    pub entry: Option<String>,
}

impl PnToCirOptions {
    pub fn new(program_name: impl Into<String>) -> Self {
        Self {
            program_name: program_name.into(),
            entry: None,
        }
    }

    pub fn with_entry(mut self, entry: impl Into<String>) -> Self {
        self.entry = Some(entry.into());
        self
    }
}

/// Metadata produced during conversion (for logging / diagnostics).
#[derive(Debug, Default, Clone)]
pub struct ConvertReport {
    pub place_count: usize,
    pub transition_count: usize,
    pub resource_count: usize,
    pub function_count: usize,
    pub notes: Vec<String>,
}

/// Convert a RustPTA Petri net into a CIR [`Program`].
///
/// Current implementation (framework):
/// - extracts shared resources from resource places + transition types;
/// - builds per-function stub bodies from concurrency-related transitions;
/// - leaves `protection` / `fn_summaries` empty (filled in later milestones).
pub fn convert_net_to_cir(net: &Net, options: PnToCirOptions) -> (Program, ConvertReport) {
    let mut report = ConvertReport {
        place_count: net.places.len(),
        transition_count: net.transitions.len(),
        notes: vec![
            "stub conversion: statement order follows transition scan, not full CFG".into(),
        ],
        ..Default::default()
    };

    let entry = resolve_entry(net, &options);
    let resources = extract_resources(net);
    report.resource_count = resources.len();

    let functions = build_functions(net, &entry);
    report.function_count = functions.len();

    let program = Program {
        program: options.program_name,
        resources,
        protection: Vec::new(),
        functions,
        fn_summaries: Vec::new(),
        entry,
    };

    (program, report)
}

fn resolve_entry(net: &Net, options: &PnToCirOptions) -> String {
    if let Some(ref e) = options.entry {
        return e.clone();
    }
    discover_functions(net)
        .into_iter()
        .find(|(_, is_main)| *is_main)
        .map(|(n, _)| n)
        .or_else(|| discover_functions(net).first().map(|(n, _)| n.clone()))
        .unwrap_or_else(|| "main".into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_petri_net_analysis::net::Net;
    use rust_petri_net_analysis::net::structure::{Place, PlaceType, Transition, TransitionType};

    fn sample_net() -> Net {
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
        let lock = net.add_place(Place::new(
            "Mutex_guard",
            1,
            1,
            PlaceType::Resources,
            String::new(),
        ));
        let _ = (main_start, worker_start, lock);

        let spawn = net.add_transition(Transition::new_with_transition_type(
            "main_0_call",
            TransitionType::Spawn("worker".into()),
        ));
        let join = net.add_transition(Transition::new_with_transition_type(
            "main_1_join",
            TransitionType::Join("worker".into()),
        ));
        let lock_t = net.add_transition(Transition::new_with_transition_type(
            "worker_0_lock",
            TransitionType::Lock(0),
        ));
        net.add_input_arc(main_start, spawn, 1);
        net.add_input_arc(main_start, join, 1);
        net.add_input_arc(lock, lock_t, 1);
        let _ = (spawn, join, lock_t);

        net
    }

    #[test]
    fn convert_extracts_resources_and_functions() {
        let net = sample_net();
        let (program, report) = convert_net_to_cir(&net, PnToCirOptions::new("test_prog"));
        assert_eq!(program.program, "test_prog");
        assert!(!program.resources.is_empty());
        assert!(program.functions.len() >= 2);
        assert_eq!(report.function_count, program.functions.len());
        assert!(program.resources.iter().any(|r| r.name.contains("Mutex")));
    }

    #[test]
    fn entry_defaults_to_main() {
        let net = sample_net();
        let (program, _) = convert_net_to_cir(&net, PnToCirOptions::new("p"));
        assert_eq!(program.entry, "main");
    }
}
