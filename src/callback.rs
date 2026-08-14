extern crate rustc_driver;
extern crate rustc_hir;

use crate::config::ReportLevel;
use crate::detect::atomicity_violation::AtomicityViolationDetector;
use crate::detect::datarace::DataRaceDetector;
use crate::detect::deadlock::DeadlockDetector;
use crate::options::{DetectorKind, Options, StopAfter};
use crate::report::{AtomicReport, DeadlockReport, RaceReport};
use crate::translate::callgraph::CallGraph;
use crate::translate::petri_net::PetriNet;
use crate::util::mem_watcher::MemoryWatcher;
use log::{debug, error, info};
use rayon::join;
use rustc_driver::Compilation;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_interface::interface;
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::{Instance, TyCtxt};
use serde::Serialize;
use std::fmt::{Debug, Formatter, Result};
use std::path::PathBuf;
use std::time::Instant;
use unipn::analysis::pt::reachability::{StateGraph, StateGraphConfig};

#[derive(Clone)]
pub struct PTACallbacks {
    pub options: Options,
    pub output_directory: PathBuf,
    test_run: bool,
}

impl PTACallbacks {
    pub fn new(options: Options) -> Self {
        let diagnostics_output = options.analysis_output_dir();

        Self {
            options,
            output_directory: diagnostics_output,
            test_run: false,
        }
    }

    fn ensure_output_directory(&self) {
        std::fs::create_dir_all(&self.output_directory).unwrap_or_else(|e| {
            log::debug!("Warning: Failed to create output directory: {}", e);
        });
    }

    fn is_research_report(&self) -> bool {
        self.options.config.report_level == ReportLevel::Research
    }
}

impl Debug for PTACallbacks {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "PTACallbacks".fmt(f)
    }
}

impl Default for PTACallbacks {
    fn default() -> Self {
        Self::new(Options::default())
    }
}

impl rustc_driver::Callbacks for PTACallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.opts.optimize = rustc_session::config::OptLevel::No;
        config.opts.debuginfo = rustc_session::config::DebugInfo::None;

        if config.opts.test {
            debug!("in test only mode");
        }
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        compiler.sess.dcx().abort_if_errors();
        if self
            .output_directory
            .to_str()
            .expect("valid string")
            .contains("/build/")
        {
            return Compilation::Continue;
        }

        // Stop after MIR dump (before analysis).
        if self.options.stop_after == StopAfter::AfterMir {
            log::info!("Stopping analysis after MIR output");
            return Compilation::Stop;
        }

        self.analyze_with_pta(compiler, tcx);

        // When a stop point is set, stop compilation after analysis.
        if self.options.stop_after != StopAfter::None || self.test_run {
            Compilation::Stop
        } else {
            Compilation::Continue
        }
    }
}

impl PTACallbacks {
    fn analyze_with_pta<'tcx>(&mut self, _compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) {
        let mut mem_watcher = MemoryWatcher::new();
        mem_watcher.start();

        if tcx.sess.opts.unstable_opts.no_codegen || !tcx.sess.opts.output_types.should_codegen() {
            return;
        }

        let current_crate_name = tcx.crate_name(LOCAL_CRATE).to_string();

        if !self.options.targets_current_crate(&current_crate_name) {
            debug!(
                "skip Petri net construction for crate {} (target crate: {})",
                current_crate_name, self.options.crate_name
            );
            return;
        }

        self.output_directory = self.options.analysis_output_dir();
        self.ensure_output_directory();

        let cgus = tcx.collect_and_partition_mono_items(()).codegen_units;
        let instances: Vec<Instance<'tcx>> = cgus
            .iter()
            .flat_map(|cgu| {
                cgu.items().iter().filter_map(|(mono_item, _)| {
                    if let MonoItem::Fn(instance) = mono_item {
                        Some(*instance)
                    } else {
                        None
                    }
                })
            })
            .collect();

        let mut callgraph = CallGraph::new();
        let key_api_regex = crate::translate::structure::KeyApiRegex::new(&self.options.config);
        callgraph.analyze(instances.clone(), tcx, &key_api_regex);

        // Emit MIR dot when requested.
        if self.options.dump_options.dump_mir {
            self.dump_mir_dots(tcx, &instances);
        }

        // Stop after call graph construction.
        if self.options.stop_after == StopAfter::AfterCallGraph {
            log::info!("Stopping analysis after call graph construction");
            return;
        }

        let mut pn = PetriNet::new(self.options.clone(), tcx, &callgraph);
        let net_construct_start = Instant::now();
        pn.construct();
        let net_construct_time = net_construct_start.elapsed();
        log::info!("Petri net constructed in {:?}", net_construct_time);

        let (mut net, mut marking) = pn.builder.snapshot();

        let mut reduced_stage_written = false;
        if self.options.dump_options.dump_petri_net {
            if let Err(err) = pn
                .builder
                .write_dot(self.output_directory.join("petrinet_raw.dot"))
            {
                error!("failed to write raw Petri net dot file: {err}");
            } else {
                info!("raw petri net dot exported");
            }
        }

        let mut net_reduce_time = None::<std::time::Duration>;
        if self.options.config.reduce_net {
            use unipn::analysis::pt::reduce::{ReductionOptions, reduce_in_place};
            let reduce_start = Instant::now();
            match reduce_in_place(&net, &marking, ReductionOptions::default()) {
                Ok(result) => {
                    net_reduce_time = Some(reduce_start.elapsed());
                    net = result.net;
                    marking = result.marking;
                    log::info!(
                        "Petri net reduced in {:?}: {} steps (loops/sequences/intermediate)",
                        net_reduce_time,
                        result.steps.len()
                    );
                    if self.options.dump_options.dump_petri_net {
                        if let Err(err) = result
                            .stage_nets
                            .after_loop
                            .write_dot(self.output_directory.join("petrinet_reduce_1_loop.dot"))
                        {
                            error!("failed to write stage-1 reduced Petri net: {err}");
                        }
                        if let Err(err) = result
                            .stage_nets
                            .after_sequence
                            .write_dot(self.output_directory.join("petrinet_reduce_2_sequence.dot"))
                        {
                            error!("failed to write stage-2 reduced Petri net: {err}");
                        }
                        if let Err(err) = result.stage_nets.after_intermediate.write_dot(
                            self.output_directory
                                .join("petrinet_reduce_3_intermediate.dot"),
                        ) {
                            error!("failed to write stage-3 reduced Petri net: {err}");
                        }
                        reduced_stage_written = true;
                    }
                }
                Err(e) => {
                    log::warn!(
                        "Petri net reduction failed: {}, continuing without reduction",
                        e
                    );
                }
            }
        }
        if self.options.dump_options.dump_petri_net && !reduced_stage_written {
            let raw = self.output_directory.join("petrinet_raw.dot");
            let s1 = self.output_directory.join("petrinet_reduce_1_loop.dot");
            let s2 = self.output_directory.join("petrinet_reduce_2_sequence.dot");
            let s3 = self
                .output_directory
                .join("petrinet_reduce_3_intermediate.dot");
            for path in [s1, s2, s3] {
                if let Err(err) = std::fs::copy(&raw, &path) {
                    error!(
                        "failed to initialize reduction stage file {:?}: {err}",
                        path
                    );
                }
            }
        }

        if self.is_research_report() {
            pn.builder.log_diagnostics();
        }

        if self.is_research_report() && self.options.dump_options.dump_petri_net {
            let report = pn.builder.diagnose_connectivity();
            if report.has_issues() {
                let report_path = self.output_directory.join("petri_net_diagnostics.txt");
                if let Err(err) = report.save_to_file(report_path.to_str().unwrap_or("")) {
                    error!("failed to save diagnostic report: {err}");
                }
            }
        }

        // Stop after pointer analysis (or points-to-only mode).
        if self.options.stop_after == StopAfter::AfterPointsTo
            || matches!(self.options.detector_kind, DetectorKind::PointsTo)
        {
            log::info!("Stopping analysis after pointer analysis");
            let sg_config = StateGraphConfig {
                state_limit: self.options.config.state_limit,
                include_zero_tokens: false,
                use_por: self.options.config.por_enabled,
            };
            let sg_build_start = Instant::now();
            let sg = StateGraph::with_config(&net, marking.clone(), sg_config);
            let sg_build_time = sg_build_start.elapsed();
            log::info!("State graph built in {:?}", sg_build_time);
            self.handle_visualizations(&callgraph, &pn, &sg);
            if self.is_research_report() {
                self.write_summary(
                    &callgraph,
                    &pn,
                    &sg,
                    net_construct_time,
                    net_reduce_time,
                    sg_build_time,
                );
            }
            return;
        }

        let sg_config = StateGraphConfig {
            state_limit: self.options.config.state_limit,
            include_zero_tokens: false,
            use_por: self.options.config.por_enabled,
        };
        let sg_build_start = Instant::now();
        let state_graph = StateGraph::with_config(&net, marking.clone(), sg_config);
        let sg_build_time = sg_build_start.elapsed();
        log::info!("State graph built in {:?}", sg_build_time);
        if state_graph.truncated {
            log::warn!(
                "State space truncated (limit={:?}); results may be incomplete",
                self.options.config.state_limit
            );
        }

        // Stop after state graph construction.
        if self.options.stop_after == StopAfter::AfterStateGraph {
            log::info!("Stopping analysis after state graph construction");
            self.handle_visualizations(&callgraph, &pn, &state_graph);
            if self.is_research_report() {
                self.write_summary(
                    &callgraph,
                    &pn,
                    &state_graph,
                    net_construct_time,
                    net_reduce_time,
                    sg_build_time,
                );
            }
            return;
        }

        self.handle_visualizations(&callgraph, &pn, &state_graph);
        if self.is_research_report() {
            self.write_summary(
                &callgraph,
                &pn,
                &state_graph,
                net_construct_time,
                net_reduce_time,
                sg_build_time,
            );
        }
        self.run_detectors(&state_graph);

        mem_watcher.stop();
    }

    fn handle_visualizations<'analysis, 'tcx>(
        &self,
        callgraph: &CallGraph<'tcx>,
        pn: &PetriNet<'analysis, 'tcx>,
        state_graph: &StateGraph,
    ) {
        let dump = &self.options.dump_options;

        if dump.dump_call_graph {
            if let Err(err) = callgraph.write_dot(self.output_directory.join("callgraph.dot")) {
                error!("failed to write call graph dot file: {err}");
            } else {
                info!("call graph dot exported");
            }
        }

        if dump.dump_state_graph {
            if let Err(err) = state_graph.write_dot(self.output_directory.join("stategraph.dot")) {
                error!("failed to write state graph dot file: {err}");
            } else {
                info!("state graph dot exported");
            }
        }

        if dump.dump_petri_net {
            if let Err(err) = pn
                .builder
                .write_dot(self.output_directory.join("petrinet.dot"))
            {
                error!("failed to write Petri net dot file: {err}");
            } else {
                info!("petri net dot exported");
            }
        }
        if dump.dump_unsafe_info {
            todo!()
        }
        if dump.dump_points_to || matches!(self.options.detector_kind, DetectorKind::PointsTo) {
            let report = pn.alias.borrow().format_points_to_report();
            let path = self.output_directory.join("points_to_report.txt");
            if let Err(err) = std::fs::write(&path, report) {
                error!("failed to write points-to report to {:?}: {err}", path);
            } else {
                info!("points-to report exported to {:?}", path);
            }
        }
    }

    fn dump_mir_dots<'tcx>(&self, tcx: TyCtxt<'tcx>, instances: &[Instance<'tcx>]) {
        use crate::util::mir_dot::write_mir_dot;

        let mir_dir = self.output_directory.join("mir");
        std::fs::create_dir_all(&mir_dir).unwrap_or_else(|e| {
            error!("Failed to create MIR output directory: {}", e);
        });

        for instance in instances {
            let def_id = instance.def_id();
            if !tcx.is_mir_available(def_id) {
                continue;
            }

            let body = tcx.optimized_mir(def_id);
            if body.source.promoted.is_some() {
                continue;
            }

            let fn_name = crate::util::format_name(def_id);
            let safe_fn_name = fn_name
                .replace(':', "_")
                .replace('-', "_")
                .replace('.', "_")
                .replace('/', "_");
            let mir_path = mir_dir.join(format!("{}.dot", safe_fn_name));

            if let Err(err) = write_mir_dot(tcx, def_id, body, &mir_path) {
                error!("Failed to write MIR dot for {}: {}", fn_name, err);
            } else {
                info!("MIR dot exported: {}", mir_path.display());
            }
        }
    }

    fn run_detectors(&self, state_graph: &StateGraph) {
        match self.options.detector_kind {
            DetectorKind::Deadlock => {
                self.run_deadlock_detector(state_graph);
            }
            DetectorKind::DataRace => {
                self.run_datarace_detector(state_graph);
            }
            DetectorKind::PointsTo => {
                // Points-to mode returns early; this arm is unreachable
            }
            DetectorKind::AtomicityViolation => {
                self.run_atomic_detector(state_graph);
            }
            DetectorKind::All => {
                log::info!(
                    "Data-race and atomicity analyses are mutually exclusive; `--mode all` runs data-race analysis by default. Use `--mode atomic` for atomicity analysis."
                );
                join(
                    || self.run_deadlock_detector(state_graph),
                    || self.run_datarace_detector(state_graph),
                );
            }
        }
    }

    fn run_deadlock_detector(&self, state_graph: &StateGraph) {
        let report = DeadlockDetector::new(state_graph).detect();
        self.log_deadlock(&report);
        self.write_report(self.output_directory.join("deadlock_report.txt"), |path| {
            report.save_to_file(path)
        });
    }

    fn run_datarace_detector(&self, state_graph: &StateGraph) {
        let report = DataRaceDetector::new(state_graph).detect();
        self.log_datarace(&report);
        self.write_report(self.output_directory.join("datarace_report.txt"), |path| {
            report.save_to_file(path)
        });
    }

    fn run_atomic_detector(&self, state_graph: &StateGraph) {
        let report = AtomicityViolationDetector::new(state_graph).detect();
        self.log_atomic(&report);
        self.write_report(self.output_directory.join("atomicity_report.txt"), |path| {
            report.save_to_file(path)
        });
    }

    fn write_report<F>(&self, path: PathBuf, write: F)
    where
        F: FnOnce(&str) -> std::io::Result<()>,
    {
        if let Some(parent) = path.parent() {
            if let Err(err) = std::fs::create_dir_all(parent) {
                error!("failed to create report directory {:?}: {err}", parent);
                return;
            }
        }

        match path.to_str() {
            Some(path_str) => {
                if let Err(err) = write(path_str) {
                    error!("failed to persist report {:?}: {err}", path);
                }
            }
            None => error!("report path contains invalid UTF-8: {:?}", path),
        }
    }

    fn write_summary<'analysis, 'tcx>(
        &self,
        callgraph: &CallGraph<'tcx>,
        pn: &PetriNet<'analysis, 'tcx>,
        state_graph: &StateGraph,
        net_construct_time: std::time::Duration,
        net_reduce_time: Option<std::time::Duration>,
        sg_build_time: std::time::Duration,
    ) {
        #[derive(Serialize)]
        struct SummaryMetrics {
            callable_functions: usize,
            places: usize,
            transitions: usize,
            state_classes: usize,
            state_edges: usize,
            deadlock_states: usize,
            truncated: bool,
            net_construct_time_ms: u64,
            net_reduce_time_ms: Option<u64>,
            state_graph_build_time_ms: u64,
        }

        #[derive(Serialize)]
        struct SummaryArtifacts {
            callgraph_dot: &'static str,
            petrinet_dot: &'static str,
            petrinet_raw_dot: &'static str,
            petrinet_reduce_1_loop_dot: &'static str,
            petrinet_reduce_2_sequence_dot: &'static str,
            petrinet_reduce_3_intermediate_dot: &'static str,
            stategraph_dot: &'static str,
            deadlock_report: &'static str,
            datarace_report: &'static str,
            atomicity_report: &'static str,
            points_to_report: &'static str,
        }

        #[derive(Serialize)]
        struct Summary {
            crate_name: String,
            mode: String,
            reduced: bool,
            metrics: SummaryMetrics,
            artifacts: SummaryArtifacts,
        }

        let stats = state_graph.stats();
        let mode = match self.options.detector_kind {
            DetectorKind::All => "all",
            DetectorKind::Deadlock => "deadlock",
            DetectorKind::AtomicityViolation => "atomic",
            DetectorKind::DataRace => "datarace",
            DetectorKind::PointsTo => "pointsto",
        }
        .to_string();

        let summary = Summary {
            crate_name: self.options.crate_name.clone(),
            mode,
            reduced: self.options.config.reduce_net,
            metrics: SummaryMetrics {
                callable_functions: callgraph.graph.node_count(),
                places: pn.builder.places_len(),
                transitions: pn.builder.transitions_len(),
                state_classes: stats.state_count,
                state_edges: stats.edge_count,
                deadlock_states: stats.deadlock_count,
                truncated: stats.truncated,
                net_construct_time_ms: net_construct_time.as_millis() as u64,
                net_reduce_time_ms: net_reduce_time.map(|t| t.as_millis() as u64),
                state_graph_build_time_ms: sg_build_time.as_millis() as u64,
            },
            artifacts: SummaryArtifacts {
                callgraph_dot: "callgraph.dot",
                petrinet_dot: "petrinet.dot",
                petrinet_raw_dot: "petrinet_raw.dot",
                petrinet_reduce_1_loop_dot: "petrinet_reduce_1_loop.dot",
                petrinet_reduce_2_sequence_dot: "petrinet_reduce_2_sequence.dot",
                petrinet_reduce_3_intermediate_dot: "petrinet_reduce_3_intermediate.dot",
                stategraph_dot: "stategraph.dot",
                deadlock_report: "deadlock_report.txt",
                datarace_report: "datarace_report.txt",
                atomicity_report: "atomicity_report.txt",
                points_to_report: "points_to_report.txt",
            },
        };

        let path = self.output_directory.join("summary.json");
        match serde_json::to_vec_pretty(&summary) {
            Ok(buf) => {
                if let Err(err) = std::fs::write(&path, buf) {
                    error!("failed to write summary {:?}: {err}", path);
                }
            }
            Err(err) => error!("failed to serialize summary: {err}"),
        }
    }

    fn log_deadlock(&self, report: &DeadlockReport) {
        if report.has_deadlock {
            info!(
                "deadlock analysis detected {} deadlocks",
                report.deadlock_count
            );
        } else {
            info!("deadlock analysis completed: no deadlocks detected");
        }
    }

    fn log_datarace(&self, report: &RaceReport) {
        if report.has_race {
            info!(
                "data race analysis detected {} potential races",
                report.race_count
            );
        } else {
            info!("data race analysis completed: no races detected");
        }
    }

    #[allow(dead_code)]
    fn log_atomic(&self, report: &AtomicReport) {
        if report.has_violation {
            info!(
                "atomicity analysis detected {} violation patterns",
                report.violation_count
            );
        } else {
            info!("atomicity analysis completed: no violations detected");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn callbacks_new_does_not_create_output_directory() {
        let output_root = std::env::temp_dir().join(format!(
            "rustpta_callbacks_new_no_create_{}",
            std::process::id()
        ));
        let output_dir = output_root.join("target_crate");
        let _ = std::fs::remove_dir_all(&output_root);

        let options = Options {
            crate_name: "target_crate".to_string(),
            output: Some(output_root.clone()),
            ..Options::default()
        };

        let callbacks = PTACallbacks::new(options);

        assert_eq!(callbacks.output_directory, PathBuf::from(&output_dir));
        assert!(!output_dir.exists());

        let _ = std::fs::remove_dir_all(&output_root);
    }
}
