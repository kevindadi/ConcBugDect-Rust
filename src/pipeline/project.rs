//! Write the analysis JSON and the optional dot / points-to dumps.

use log::{error, info};
use std::time::Instant;
use unipn::analysis::pt::reachability::StateGraph;

use crate::analysis::callgraph::CallGraph;
use crate::options::{DetectorKind, StopAfter};
use crate::translate::construct::PetriNet;

use super::{Constructed, Explored, RunCtx};

pub fn project<'a, 'tcx>(
    ctx: &RunCtx<'_, 'tcx>,
    constructed: &Constructed<'a, 'tcx>,
    explored: &Explored,
) {
    let started = Instant::now();
    let petri = &constructed.petri;
    let raw_net = &constructed.raw_net;
    let net = &constructed.net;
    let provenance = &constructed.provenance;
    let state_graph = &explored.results[0].state_graph;
    let slice_layout = explored.results[0].slice_layout.as_ref();
    let reduce_trace = explored.reduce_trace.as_ref();

    // Deadlock counterexample report (`deadlocks.json`): the fixed default
    // output of the deadlock and all modes. It is written before the
    // `--stop-after stategraph` early return, so a stopped run still gets
    // it; a write failure is logged and does not fail the build.
    if matches!(ctx.options.detector_kind, DetectorKind::Deadlock) {
        let deadlocks = state_graph.deadlock_states(net);
        log::info!(
            "deadlock report: {} deadlocks / {} blocked / truncated={}",
            deadlocks.len(),
            state_graph.blocked.len(),
            state_graph.truncated
        );
        // Candidate-level refinements (`--exclude-candidates`): report
        // side only, read fail-open, never touching the net or the graph.
        let refinements = match &ctx.options.exclude_candidates {
            Some(path) => crate::report::refinements::load_refinements(path, &ctx.crate_name),
            None => crate::report::refinements::Refinements::default(),
        };
        if !refinements.is_empty() {
            let remaining = deadlocks
                .iter()
                .filter(|state| !refinements.excluded.contains(state))
                .count();
            log::info!(
                "candidate exclusions: {} applied, {} remaining reported (of {} deadlocks)",
                refinements.excluded.len(),
                remaining.min(crate::report::MAX_REPORTED_DEADLOCKS),
                deadlocks.len(),
            );
        }
        let inputs = crate::report::ReportInputs {
            crate_name: &ctx.crate_name,
            raw_net,
            net,
            state_graph,
            reduce_trace,
            excluded: &refinements.excluded,
            entry_mode: petri.entry_mode.as_str(),
            slice_layout,
        };
        if let Err(err) = crate::report::write_deadlock_report(&inputs, &ctx.output_dir) {
            log::error!("failed to write deadlock report: {err}");
        }
        // Path predicates Φ(σ): the structured input for the later
        // LLM-backed stage; written next to deadlocks.json and never
        // allowed to fail the build.
        match crate::report::predicates::write_predicates(&inputs, provenance, &ctx.output_dir) {
            Ok(stats) => log::info!(
                "path predicates: {} candidates / {} guards (switch {}, assert {}) / verified {} / unverified {}",
                stats.candidates,
                stats.guards,
                stats.switches,
                stats.asserts,
                stats.verified,
                stats.unverified
            ),
            Err(err) => log::error!("failed to write path predicates: {err}"),
        }
        // Event sites (`events.json`) and the expected replay traces
        // (`expected-trace.json`) of the controlled replay. Both
        // enumerate the *original* net, so `site_id`s stay stable across
        // reductions, while σ comes from the same reduced-net state graph
        // the other reports use. Write failures never fail the build.
        match crate::report::events::write_events(
            &ctx.crate_name,
            raw_net,
            provenance,
            &ctx.output_dir,
        ) {
            Ok(count) => log::info!("event sites: {count}"),
            Err(err) => log::error!("failed to write event sites: {err}"),
        }
        match crate::report::expected_trace::write_expected_traces(
            &inputs,
            provenance,
            &ctx.output_dir,
        ) {
            Ok(stats) => log::info!(
                "expected traces: {} candidates / {} events / {} null hints",
                stats.candidates,
                stats.events,
                stats.null_hints
            ),
            Err(err) => log::error!("failed to write expected traces: {err}"),
        }
    }
    if let Err(err) = crate::report::coverage::write_coverage_report(
        &ctx.crate_name,
        &petri.coverage,
        &ctx.output_dir,
    ) {
        log::error!("failed to write translation coverage report: {err}");
    }
    if let Err(err) = crate::translate::net::subnets::write_subnets(
        &ctx.output_dir,
        raw_net,
        provenance,
        &petri.subnets,
    ) {
        log::error!("failed to write subnets.json: {err}");
    }
    if ctx.options.dump_options.dump_projected_subnets {
        if let Err(err) = crate::translate::net::subnets::write_projected_subnets(
            &ctx.output_dir,
            raw_net,
            provenance,
            &petri.subnets,
        ) {
            log::error!("failed to write subnets-projected.json: {err}");
        }
    }
    if let Some(export_path) = &ctx.options.export_concir_net {
        let codegen_map = ctx.options.codegen_map.as_deref().and_then(|map_path| {
            match crate::report::concir_net::CodegenMap::load_from_file(map_path) {
                Ok(map) => Some(map),
                Err(err) => {
                    log::error!("failed to load --codegen-map {:?}: {err}", map_path);
                    None
                }
            }
        });
        let place_field_hints = crate::report::concir_net::collect_place_field_hints(petri);
        let unsafe_spans = if codegen_map.is_some() {
            crate::report::concir_net::collect_unsafe_spans(petri, &ctx.crate_name)
        } else {
            Vec::new()
        };
        let concir_inputs = crate::report::concir_net::ConcirNetInputs {
            crate_name: &ctx.crate_name,
            entry_mode: petri.entry_mode.as_str(),
            net,
            initial_marking: &constructed.marking,
            state_graph,
            provenance,
            subnets: &petri.subnets,
            codegen_map: codegen_map.as_ref(),
            place_field_hints: &place_field_hints,
            focus_module: ctx.options.focus_module.as_deref(),
            unsafe_spans: &unsafe_spans,
        };
        if let Err(err) = crate::report::concir_net::write_concir_net(&concir_inputs, export_path)
        {
            log::error!(
                "failed to write ConcIR impl net to {:?}: {err}",
                export_path
            );
        } else {
            log::info!("ConcIR impl net exported to {:?}", export_path);
        }
    }

    // Stop after state graph construction.
    if ctx.options.stop_after == StopAfter::AfterStateGraph {
        log::info!("Stopping analysis after state graph construction");
    }
    handle_visualizations(ctx, petri.callgraph(), petri, state_graph);
    log::info!("report finished in {:?}", started.elapsed());
}

pub(crate) fn handle_visualizations<'a, 'tcx>(
    ctx: &RunCtx<'_, 'tcx>,
    callgraph: &CallGraph<'tcx>,
    petri: &PetriNet<'a, 'tcx>,
    state_graph: &StateGraph,
) {
    let dump = &ctx.options.dump_options;

    if dump.dump_call_graph {
        if let Err(err) = callgraph.write_dot(ctx.output_dir.join("callgraph.dot")) {
            error!("failed to write call graph dot file: {err}");
        } else {
            info!("call graph dot exported");
        }
    }

    if dump.dump_state_graph {
        if let Err(err) = state_graph.write_dot(ctx.output_dir.join("stategraph.dot")) {
            error!("failed to write state graph dot file: {err}");
        } else {
            info!("state graph dot exported");
        }
    }

    if dump.dump_unsafe_info {
        write_unsafe_report(ctx, callgraph, petri);
    }
    if dump.dump_points_to {
        let report = petri.alias.borrow().format_points_to_report();
        let path = ctx.output_dir.join("points_to_report.txt");
        if let Err(err) = std::fs::write(&path, report) {
            error!("failed to write points-to report to {:?}: {err}", path);
        } else {
            info!("points-to report exported to {:?}", path);
        }
    }
}

/// Write `unsafe_report.json`: one entry per analysed function with its
/// unsafe blocks and unsafe places. The analysis is recomputed on demand
/// (only when `--viz-unsafe` is passed); functions are sorted by name and
/// places by local so the report is deterministic.
fn write_unsafe_report<'a, 'tcx>(
    ctx: &RunCtx<'_, 'tcx>,
    callgraph: &CallGraph<'tcx>,
    petri: &PetriNet<'a, 'tcx>,
) {
    use crate::analysis::memory::unsafe_memory::{UnsafeInfo, UnsafePlaceInfo};
    use crate::analysis::unsafe_scan::UnsafeAnalyzer;

    let analyzer = UnsafeAnalyzer::new(petri.tcx(), callgraph, petri.options().crate_name.clone());
    let (unsafe_info, _) = analyzer.analyze();

    let mut functions: Vec<(String, &UnsafeInfo)> = unsafe_info
        .iter()
        .map(|(def_id, info)| (crate::util::format_name(*def_id), info))
        .collect();
    functions.sort_by(|a, b| a.0.cmp(&b.0));

    let functions: Vec<serde_json::Value> = functions
        .iter()
        .map(|(name, info)| {
            let mut places: Vec<&UnsafePlaceInfo> = info.unsafe_places.values().collect();
            places.sort_by_key(|place| place.local);
            serde_json::json!({
                "function": name,
                "is_unsafe_fn": info.is_unsafe_fn,
                "unsafe_blocks": info.unsafe_blocks,
                "unsafe_places": places,
            })
        })
        .collect();

    let report = serde_json::json!({ "functions": functions });
    let path = ctx.output_dir.join("unsafe_report.json");
    match serde_json::to_string_pretty(&report) {
        Ok(text) => {
            if let Err(err) = std::fs::write(&path, text) {
                error!("failed to write unsafe report to {:?}: {err}", path);
            } else {
                info!("unsafe operations report exported to {:?}", path);
            }
        }
        Err(err) => error!("failed to serialize unsafe report: {err}"),
    }
}
