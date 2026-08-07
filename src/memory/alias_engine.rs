//! Alias-query engine selector.
//!
//! [`AliasEngine`] lets the Petri-net translation choose, at runtime, between
//! the legacy flow-/context-insensitive [`AliasAnalysis`] and the new
//! field-sensitive, k-CFA [`PtaAliasAnalysis`] without changing any call site.
//! The legacy engine remains the default so the new engine can be validated
//! differentially (`points_to_report.txt` vs `points_to_report_pta.txt`).
//!
//! Both variants expose the same `AliasId`-based query surface
//! (`alias` / `alias_atomic` / `points_to`) returning [`ApproximateAliasKind`],
//! so consumers are agnostic to the backing implementation.

extern crate rustc_middle;

use rustc_middle::ty::{Instance, TyCtxt};

use crate::config::PnConfig;
use crate::memory::pointsto::{AliasAnalysis, AliasId, ApproximateAliasKind};
use crate::memory::pta::PtaAliasAnalysis;
use crate::translate::callgraph::CallGraph;

pub enum AliasEngine<'a, 'tcx> {
    /// Legacy on-demand Andersen analysis (default).
    Legacy(AliasAnalysis<'a, 'tcx>),
    /// New whole-program field-sensitive / k-CFA engine (already solved).
    Pta(PtaAliasAnalysis<'a, 'tcx>),
}

impl<'a, 'tcx> AliasEngine<'a, 'tcx> {
    /// Construct the engine selected by `config.pta_engine`. The PTA engine is
    /// built (constraints solved) eagerly here so subsequent queries are cheap.
    pub fn new(tcx: TyCtxt<'tcx>, callgraph: &'a CallGraph<'tcx>, config: &PnConfig) -> Self {
        if config.pta_engine {
            let mut pta = PtaAliasAnalysis::with_k(tcx, callgraph, config.pta_k);
            pta.build();
            AliasEngine::Pta(pta)
        } else {
            AliasEngine::Legacy(AliasAnalysis::new(tcx, callgraph))
        }
    }

    pub fn alias(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        match self {
            AliasEngine::Legacy(a) => a.alias(aid1, aid2),
            AliasEngine::Pta(a) => a.alias(aid1, aid2),
        }
    }

    pub fn alias_atomic(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        match self {
            AliasEngine::Legacy(a) => a.alias_atomic(aid1, aid2),
            AliasEngine::Pta(a) => a.alias_atomic(aid1, aid2),
        }
    }

    pub fn points_to(&mut self, pointer: AliasId, pointee: AliasId) -> ApproximateAliasKind {
        match self {
            AliasEngine::Legacy(a) => a.points_to(pointer, pointee),
            AliasEngine::Pta(a) => a.points_to(pointer, pointee),
        }
    }

    /// Pre-fill points-to information for the given instances (legacy lazily
    /// computes per query; the PTA engine is already fully built).
    pub fn ensure_pts_for_instances(&mut self, instances: &[Instance<'tcx>]) {
        if let AliasEngine::Legacy(a) = self {
            a.ensure_pts_for_instances(instances);
        }
    }

    /// Human-readable points-to dump from whichever engine is active.
    pub fn format_points_to_report(&self) -> String {
        match self {
            AliasEngine::Legacy(a) => a.format_points_to_report(),
            AliasEngine::Pta(a) => a.format_report(),
        }
    }
}
