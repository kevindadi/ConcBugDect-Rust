//! Alias-query facade for the Petri-net translation.
//!
//! Wraps the single whole-program, field-sensitive, k-CFA pointer-analysis
//! engine ([`PtaAliasAnalysis`]) behind the `AliasId`-based query surface
//! (`alias` / `alias_atomic` / `points_to`) returning
//! [`ApproximateAliasKind`]. Consumers are agnostic to the backing engine, and
//! new call models (async, macro-expanded code, …) are registered on the
//! engine's [`ModelRegistry`] without touching these call sites.

extern crate rustc_middle;

use rustc_middle::ty::{Instance, TyCtxt};

use crate::config::PnConfig;
use crate::memory::pointsto::{AliasId, ApproximateAliasKind};
use crate::memory::pta::PtaAliasAnalysis;
use crate::translate::callgraph::CallGraph;

pub struct AliasEngine<'a, 'tcx> {
    /// Whole-program field-sensitive / k-CFA engine (already solved).
    pta: PtaAliasAnalysis<'a, 'tcx>,
}

impl<'a, 'tcx> AliasEngine<'a, 'tcx> {
    /// Construct the engine with the configured call-site sensitivity (`k`).
    /// The PTA is built (constraints solved) eagerly here so subsequent queries
    /// are cheap.
    pub fn new(tcx: TyCtxt<'tcx>, callgraph: &'a CallGraph<'tcx>, config: &PnConfig) -> Self {
        let mut pta = PtaAliasAnalysis::with_k(tcx, callgraph, config.pta_k);
        pta.build();
        Self { pta }
    }

    pub fn alias(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        self.pta.alias(aid1, aid2)
    }

    pub fn alias_atomic(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        self.pta.alias_atomic(aid1, aid2)
    }

    pub fn points_to(&mut self, pointer: AliasId, pointee: AliasId) -> ApproximateAliasKind {
        self.pta.points_to(pointer, pointee)
    }

    /// The PTA engine is built whole-program, so no lazy pre-fill is needed.
    /// Kept for API stability with the previous on-demand engine.
    pub fn ensure_pts_for_instances(&mut self, _instances: &[Instance<'tcx>]) {}

    /// Human-readable points-to dump from the engine.
    pub fn format_points_to_report(&self) -> String {
        self.pta.format_report()
    }
}
