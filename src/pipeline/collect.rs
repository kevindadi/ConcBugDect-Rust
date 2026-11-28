//! Collect mono items, build the call graph, and optionally dump MIR dots.

use std::time::Instant;

use log::error;
use log::info;
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::{Instance, TyCtxt};

use crate::analysis::api_patterns::KeyApiRegex;
use crate::analysis::callgraph::CallGraph;
use crate::options::StopAfter;

use super::{Collected, RunCtx};

pub fn collect<'tcx>(ctx: &RunCtx<'_, 'tcx>) -> Collected<'tcx> {
    let started = Instant::now();
    let instances = mono_fn_instances(ctx.tcx);

    let mut callgraph = CallGraph::new();
    let key_api = KeyApiRegex::new(&ctx.options.config);
    callgraph.analyze(instances.clone(), ctx.tcx, &key_api, ctx.options);

    // Emit MIR dot when requested.
    if ctx.options.dump_options.dump_mir {
        dump_mir_dots(ctx, &instances);
    }

    // Stop after call graph construction.
    let stop = ctx.options.stop_after == StopAfter::AfterCallGraph;
    if stop {
        log::info!("Stopping analysis after call graph construction");
    }
    log::info!("collect finished in {:?}", started.elapsed());

    Collected {
        instances,
        callgraph,
        stop,
    }
}

/// Write one Graphviz dot per monomorphized function under `output_dir/mir`.
/// `--stop-after mir` calls this directly; a full run calls it for `--viz-mir`.
pub(crate) fn emit_mir_dots<'tcx>(ctx: &RunCtx<'_, 'tcx>) {
    dump_mir_dots(ctx, &mono_fn_instances(ctx.tcx));
}

fn mono_fn_instances<'tcx>(tcx: TyCtxt<'tcx>) -> Vec<Instance<'tcx>> {
    let cgus = tcx.collect_and_partition_mono_items(()).codegen_units;
    cgus.iter()
        .flat_map(|cgu| {
            cgu.items().iter().filter_map(|(mono_item, _)| {
                if let MonoItem::Fn(instance) = mono_item {
                    Some(*instance)
                } else {
                    None
                }
            })
        })
        .collect()
}

fn dump_mir_dots<'tcx>(ctx: &RunCtx<'_, 'tcx>, instances: &[Instance<'tcx>]) {
    use crate::util::mir_dot::write_mir_dot;

    let tcx: TyCtxt<'tcx> = ctx.tcx;
    let mir_dir = ctx.output_dir.join("mir");
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
