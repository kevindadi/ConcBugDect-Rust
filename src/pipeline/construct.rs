//! Build the Petri net and take the pre-reduction snapshot.

use std::time::Instant;

use crate::translate::construct::PetriNet;

use super::analyze::ResourceAnalysis;
use super::{Collected, Constructed, RunCtx};

pub fn construct<'a, 'tcx>(
    ctx: &RunCtx<'_, 'tcx>,
    collected: &'a Collected<'tcx>,
    analysis: ResourceAnalysis<'tcx>,
) -> Constructed<'a, 'tcx> {
    let started = Instant::now();
    let mut petri = PetriNet::new(
        ctx.options.clone(),
        ctx.tcx,
        &collected.callgraph,
        analysis.alias,
        analysis.plan,
    );
    let net_construct_start = Instant::now();
    petri.build();
    let net_construct_time = net_construct_start.elapsed();
    log::info!("Petri net constructed in {:?}", net_construct_time);

    let (net, marking) = petri.net.snapshot();

    // Pre-reduction snapshot for the deadlock report: the report lifts σ
    // through the reduction trace and resolves the lifted transition names
    // on the original net, so the driver keeps a full copy (one extra net
    // clone per analysed crate, cheap next to the exploration itself).
    // The provenance table is indexed like that snapshot and is taken
    // along with it.
    let raw_net = net.clone();
    let provenance = petri.net.provenance().clone();
    let library_roots = petri.library_root_entries();
    log::info!("construct finished in {:?}", started.elapsed());

    Constructed {
        petri,
        net,
        marking,
        raw_net,
        provenance,
        library_roots,
    }
}
