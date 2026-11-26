//! Reduce the net, then build one state graph (joint or sliced).

use std::time::Instant;

use log::{error, info};
use unipn::analysis::pt::reachability::{StateGraph, StateGraphConfig};
use unipn::analysis::pt::reduce::ReductionTrace;

use super::{Constructed, Explored, PhaseStop, RunCtx, SliceOutcome, SlicePlan};
use crate::config::ReportLevel;
use crate::options::StopAfter;

pub fn explore<'a, 'tcx>(
    ctx: &RunCtx<'_, 'tcx>,
    constructed: &mut Constructed<'a, 'tcx>,
    plan: &SlicePlan,
) -> Explored {
    let started = Instant::now();
    let net = &mut constructed.net;
    let marking = &mut constructed.marking;
    let petri = &constructed.petri;
    let library_roots = &constructed.library_roots;
    let slice_groups = plan.slices.as_slice();
    let mut reduce_trace: Option<ReductionTrace> = None;

    let mut reduced_stage_written = false;
    if ctx.options.dump_options.dump_petri_net {
        if let Err(err) =
            crate::display::write_petri_net_dot(net, ctx.output_dir.join("petrinet_raw.dot"))
        {
            error!("failed to write raw Petri net dot file: {err}");
        } else {
            info!("raw petri net dot exported");
        }
    }

    // When `--export-concir-net` is active, disable net reduction so
    // `state_graph` transitions correspond 1-to-1 to `raw_net` transition IDs
    // and provenance without observable sync transitions being merged away.
    if ctx.options.config.reduce_net && ctx.options.export_concir_net.is_none() {
        use unipn::analysis::pt::reduce::{ReductionOptions, reduce_in_place};
        let reduce_start = Instant::now();
        match reduce_in_place(net, marking, ReductionOptions::default()) {
            Ok(result) => {
                let net_reduce_time = reduce_start.elapsed();
                log::info!(
                    "Petri net reduced in {:?}: {} steps (loops/sequences/intermediate)",
                    net_reduce_time,
                    result.steps.len()
                );
                if ctx.options.dump_options.dump_petri_net {
                    if let Err(err) = crate::display::write_petri_net_dot(
                        &result.stage_nets.after_loop,
                        ctx.output_dir.join("petrinet_reduce_1_loop.dot"),
                    ) {
                        error!("failed to write stage-1 reduced Petri net: {err}");
                    }
                    if let Err(err) = crate::display::write_petri_net_dot(
                        &result.stage_nets.after_sequence,
                        ctx.output_dir.join("petrinet_reduce_2_sequence.dot"),
                    ) {
                        error!("failed to write stage-2 reduced Petri net: {err}");
                    }
                    if let Err(err) = crate::display::write_petri_net_dot(
                        &result.stage_nets.after_intermediate,
                        ctx.output_dir.join("petrinet_reduce_3_intermediate.dot"),
                    ) {
                        error!("failed to write stage-3 reduced Petri net: {err}");
                    }
                    reduced_stage_written = true;
                }
                *net = result.net;
                *marking = result.marking;
                reduce_trace = Some(result.trace);
            }
            Err(e) => {
                log::warn!(
                    "Petri net reduction failed: {}, continuing without reduction",
                    e
                );
            }
        }
    }
    if ctx.options.dump_options.dump_petri_net && !reduced_stage_written {
        let raw = ctx.output_dir.join("petrinet_raw.dot");
        let s1 = ctx.output_dir.join("petrinet_reduce_1_loop.dot");
        let s2 = ctx.output_dir.join("petrinet_reduce_2_sequence.dot");
        let s3 = ctx.output_dir.join("petrinet_reduce_3_intermediate.dot");
        for path in [s1, s2, s3] {
            if let Err(err) = std::fs::copy(&raw, &path) {
                error!(
                    "failed to initialize reduction stage file {:?}: {err}",
                    path
                );
            }
        }
    }

    if ctx.options.dump_options.dump_petri_net {
        if let Err(err) =
            crate::display::write_petri_net_dot(net, ctx.output_dir.join("petrinet.dot"))
        {
            error!("failed to write Petri net dot file: {err}");
        } else {
            info!("petri net dot exported");
        }
    }

    if ctx.options.config.report_level == ReportLevel::Research {
        petri.net.log_diagnostics();
    }

    if ctx.options.config.report_level == ReportLevel::Research
        && ctx.options.dump_options.dump_petri_net
    {
        let report = petri.net.diagnose_connectivity();
        if report.has_issues() {
            let report_path = ctx.output_dir.join("petri_net_diagnostics.txt");
            if let Err(err) = report.save_to_file(report_path.to_str().unwrap_or("")) {
                error!("failed to save diagnostic report: {err}");
            }
        }
    }

    let sg_config = StateGraphConfig {
        state_limit: ctx.options.config.state_limit,
        include_zero_tokens: false,
        use_por: ctx.options.config.por_enabled,
    };

    // Stop after pointer analysis (or points-to-only mode).
    if ctx.options.stop_after == StopAfter::AfterPointsTo {
        log::info!("Stopping analysis after pointer analysis");
        let sg_build_start = Instant::now();
        let sg = StateGraph::with_config(net, marking.clone(), sg_config);
        let sg_build_time = sg_build_start.elapsed();
        log::info!("State graph built in {:?}", sg_build_time);
        super::handle_visualizations(ctx, petri.callgraph(), petri, &sg);
        log::info!("explore finished in {:?}", started.elapsed());
        return Explored {
            results: vec![SliceOutcome {
                state_graph: sg,
                slice_layout: None,
            }],
            reduce_trace,
            stop: PhaseStop::AfterPointsTo,
        };
    }

    let sg_build_start = Instant::now();
    let mut slice_layout = None;
    let state_graph = if slice_groups.is_empty() {
        StateGraph::with_config(net, marking.clone(), sg_config)
    } else {
        // Switch off every root token but the slice's own on the *same*
        // reduced net: the translation, resource places and reduction are
        // shared, only the initial marking and the reachability filter
        // differ.
        let mapping = super::slices::reduced_place_of(net, reduce_trace.as_ref());
        let untranslatable = super::slices::untranslatable_roots(library_roots, &mapping);
        let starts: Vec<unipn::PlaceId> = library_roots
            .iter()
            .filter_map(|root| mapping.get(&root.start.index()).copied())
            .collect();
        let bad_starts: Vec<String> =
            if untranslatable.is_empty() && starts.len() == library_roots.len() {
                library_roots
                    .iter()
                    .zip(&starts)
                    .filter(|&(_, &start)| marking.tokens(start) != 1)
                    .map(|(root, _)| root.name.clone())
                    .collect()
            } else {
                Vec::new()
            };
        if !untranslatable.is_empty() || !bad_starts.is_empty() {
            log::warn!(
                "library slicing disabled: root start place not switchable (no place: [{}], token != 1: [{}]); exploring the joint initial marking",
                untranslatable.join(", "),
                bad_starts.join(", ")
            );
            StateGraph::with_config(net, marking.clone(), sg_config)
        } else {
            let sliced = super::slices::slice_state_graphs(
                net,
                marking,
                library_roots,
                &starts,
                slice_groups,
                sg_config.state_limit,
                ctx.options.config.slice_state_budget,
                sg_config.include_zero_tokens,
                sg_config.use_por,
            );
            for slice in &sliced.layout.slices {
                log::info!(
                    "library slice [{}]: {} states / {} edges / {} blocked / {} deadlocks / truncated={}",
                    slice.entry_roots.join(" + "),
                    slice.states,
                    slice.edges,
                    slice.blocked,
                    slice.deadlocks,
                    slice.truncated
                );
            }
            log::info!(
                "state graph sliced into {} slice(s) ({} unexplored, budget {:?}): {} states / {} edges total",
                sliced.layout.slices.len(),
                sliced.layout.unexplored_slices,
                ctx.options.config.slice_state_budget,
                sliced.graph.states.len(),
                sliced.graph.edges.len()
            );
            slice_layout = Some(sliced.layout);
            sliced.graph
        }
    };
    let sg_build_time = sg_build_start.elapsed();
    log::info!("State graph built in {:?}", sg_build_time);
    log::info!("explore finished in {:?}", started.elapsed());
    if state_graph.truncated {
        log::warn!(
            "State space truncated (limit={:?}); results may be incomplete",
            ctx.options.config.state_limit
        );
    }

    Explored {
        results: vec![SliceOutcome {
            state_graph,
            slice_layout,
        }],
        reduce_trace,
        stop: PhaseStop::None,
    }
}
