//! Alias queries (`alias`, `alias_atomic`, `points_to`) for translation.
//! Callers see `ApproximateAliasKind` and not the pointer-analysis engine.
//! It does not build the Petri net.

extern crate rustc_middle;

use rustc_data_structures::fx::FxHashSet;
use rustc_middle::ty::{Instance, TyCtxt};
use smallvec::SmallVec;

use crate::analysis::memory::pointsto::{AliasId, ApproximateAliasKind};
use crate::analysis::memory::pta::PtaAliasAnalysis;
use crate::analysis::memory::pta::context::Context;
use crate::analysis::memory::pta::loc::CiKey;
use crate::config::PnConfig;

pub struct AliasEngine<'tcx> {
    /// Whole-program field-sensitive / k-CFA engine (already solved).
    pta: PtaAliasAnalysis<'tcx>,
}

impl<'tcx> AliasEngine<'tcx> {
    /// Construct the engine with the configured call-site sensitivity (`k`).
    /// The engine is built (constraints solved) eagerly here so subsequent queries
    /// are cheap.
    pub fn new(tcx: TyCtxt<'tcx>, instances: Vec<Instance<'tcx>>, config: &PnConfig) -> Self {
        let mut pta = PtaAliasAnalysis::with_k(tcx, instances, config.pta_k);
        pta.build();
        Self { pta }
    }

    /// Whether the solved engine entered this instance's body.
    pub fn instance_built(&self, instance: Instance<'tcx>) -> bool {
        self.pta.instance_built(instance)
    }

    /// Whether `local` received a node while that body was built.
    pub fn local_built(&self, instance: Instance<'tcx>, local: u32) -> bool {
        self.pta.local_built(instance, local)
    }

    pub fn alias(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        self.pta.alias(aid1, aid2)
    }

    pub fn alias_atomic(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        self.pta.alias_atomic(aid1, aid2)
    }

    /// Lock-grouping alias query: compares acquisition receivers per call-site
    /// context (P3), falling back to [`Self::alias`] when the per-context
    /// comparison is inconclusive. The fallback is the collapsed may-alias
    /// result, which is the sound direction under the conservative policy.
    /// Only lock grouping uses this; all other alias queries keep the
    /// context-collapsed semantics.
    pub fn alias_lock_group_with_fallback(
        &mut self,
        aid1: AliasId,
        aid2: AliasId,
    ) -> ApproximateAliasKind {
        self.pta.alias_lock_group_with_fallback(aid1, aid2)
    }

    pub fn points_to(&mut self, pointer: AliasId, pointee: AliasId) -> ApproximateAliasKind {
        self.pta.points_to(pointer, pointee)
    }

    /// Distinct proven-constant argument vectors at the call sites
    /// that resolved to `instance`.
    pub fn call_arg_const_vectors(
        &self,
        instance: Instance<'tcx>,
    ) -> &[SmallVec<[Option<u64>; 4]>] {
        self.pta.call_arg_const_vectors(instance)
    }

    /// Proven-constant argument vectors of the concrete call site
    /// `(caller, bb)`.
    pub fn call_site_arg_const_vectors(
        &self,
        caller: Instance<'tcx>,
        bb: u32,
    ) -> &[SmallVec<[Option<u64>; 4]>] {
        self.pta.call_site_arg_const_vectors(caller, bb)
    }

    /// Proven-constant parameter vectors per k-CFA context.
    pub fn param_values_by_context(
        &self,
        instance: Instance<'tcx>,
    ) -> Vec<(Context, SmallVec<[Option<u64>; 4]>)> {
        self.pta.param_values_by_context(instance)
    }

    /// Per-context receiver points-to identity for a lock receiver.
    pub fn receiver_keys_by_context(&mut self, aid: AliasId) -> Vec<(Context, FxHashSet<CiKey>)> {
        self.pta.receiver_keys_by_context(aid)
    }

    /// Is the key an exact object (no dynamic `Index` summary)?
    pub fn ci_key_is_exact(&self, key: &CiKey) -> bool {
        self.pta.ci_key_is_exact(key)
    }

    /// Object identity names of a receiver key set under one proven
    /// constant vector (`None`: empty or inexact).
    pub fn guard_object_identity_names(&self, keys: &[CiKey]) -> Option<Vec<String>> {
        self.pta.guard_object_identity_names(keys)
    }

    /// The engine is built whole-program, so no lazy pre-fill is needed.
    /// Kept for API stability with the previous on-demand engine.
    pub fn ensure_pts_for_instances(&mut self, _instances: &[Instance<'tcx>]) {}

    /// Human-readable points-to dump from the engine.
    pub fn format_points_to_report(&self) -> String {
        self.pta.format_report()
    }
}
