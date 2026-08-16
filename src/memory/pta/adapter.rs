//! Compatibility shim bridging the new engine to the legacy alias-query API.
//!
//! [`PtaAliasAnalysis`] reuses the existing [`AliasId`] / [`ApproximateAliasKind`]
//! types and exposes `alias` / `alias_atomic` / `points_to` backed by the new
//! [`PointerAnalysis`]. This lets Petri-net construction switch to the new
//! engine without changing call sites (migration happens in a later task).
//!
//! `AliasId::array_index` (which distinguishes `arr[0]` from `arr[1]`) is not
//! honored: the engine merges array indices, a sound over-approximation that
//! can only widen alias results relative to the legacy analysis.

extern crate rustc_middle;

use rustc_middle::mir::Local;
use rustc_middle::ty::Instance;
use rustc_middle::ty::TypingEnv;

use super::analysis::PointerAnalysis;
use super::result::PointsToResult;
use crate::memory::pointsto::{AliasId, ApproximateAliasKind};
use crate::translate::callgraph::CallGraph;

pub struct PtaAliasAnalysis<'a, 'tcx> {
    pta: PointerAnalysis<'tcx>,
    callgraph: &'a CallGraph<'tcx>,
    result: Option<PointsToResult>,
}

impl<'a, 'tcx> PtaAliasAnalysis<'a, 'tcx> {
    /// Context-insensitive (`k = 0`) shim. Prefer [`Self::with_k`].
    pub fn new(tcx: rustc_middle::ty::TyCtxt<'tcx>, callgraph: &'a CallGraph<'tcx>) -> Self {
        Self::with_k(tcx, callgraph, 0)
    }

    /// Shim using call-site sensitivity depth `k` (k-CFA).
    pub fn with_k(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        callgraph: &'a CallGraph<'tcx>,
        k: usize,
    ) -> Self {
        Self {
            pta: PointerAnalysis::with_k(tcx, k),
            callgraph,
            result: None,
        }
    }

    /// Build constraints for all call-graph instances and solve. Idempotent-ish:
    /// re-solving simply recomputes from the accumulated constraints.
    pub fn build(&mut self) {
        let roots: Vec<Instance<'tcx>> = self
            .callgraph
            .graph
            .node_indices()
            .filter_map(|idx| self.callgraph.index_to_instance(idx))
            .map(|node| *node.instance())
            .collect();
        self.pta.build_reachable(roots);
        self.result = Some(self.pta.solve());
    }

    fn instance_of(&self, aid: AliasId) -> Option<Instance<'tcx>> {
        Some(
            *self
                .callgraph
                .index_to_instance(aid.instance_id)?
                .instance(),
        )
    }

    /// Check if two locals may alias via the type-parameter heuristic: if both
    /// locals point to parameters of the same index and the same type, they may
    /// be the same object (e.g., two `&Mutex<T>` parameters could be the same).
    /// This mirrors the legacy engine's `point_to_same_type_param` heuristic.
    fn may_alias_via_type_param(
        &self,
        a: Instance<'tcx>,
        a_local: Local,
        b: Instance<'tcx>,
        b_local: Local,
    ) -> bool {
        // Get body for instance A
        let body_a = if self.pta.tcx().is_mir_available(a.def_id()) {
            let body = self.pta.tcx().instance_mir(a.def);
            if body.source.promoted.is_some() {
                return false;
            }
            body
        } else {
            return false;
        };
        // Get body for instance B
        let body_b = if self.pta.tcx().is_mir_available(b.def_id()) {
            let body = self.pta.tcx().instance_mir(b.def);
            if body.source.promoted.is_some() {
                return false;
            }
            body
        } else {
            return false;
        };

        // Check if locals are function parameters
        let param_idx_a = body_a.args_iter().position(|l| l == a_local);
        let param_idx_b = body_b.args_iter().position(|l| l == b_local);

        let param_idx_a = match param_idx_a {
            Some(i) => i,
            None => return false,
        };
        let param_idx_b = match param_idx_b {
            Some(i) => i,
            None => return false,
        };

        // Parameter indices must match (same position) unless same function
        let same_func = a.def_id() == b.def_id();
        if !same_func && param_idx_a != param_idx_b {
            return false;
        }

        // Types must match exactly
        let typing_env_a = TypingEnv::post_analysis(self.pta.tcx(), a.def_id());
        let ty_a = a.instantiate_mir_and_normalize_erasing_regions(
            self.pta.tcx(),
            typing_env_a,
            rustc_middle::ty::EarlyBinder::bind(body_a.local_decls[a_local].ty),
        );
        let typing_env_b = TypingEnv::post_analysis(self.pta.tcx(), b.def_id());
        let ty_b = b.instantiate_mir_and_normalize_erasing_regions(
            self.pta.tcx(),
            typing_env_b,
            rustc_middle::ty::EarlyBinder::bind(body_b.local_decls[b_local].ty),
        );

        ty_a == ty_b
    }

    /// May `aid1` and `aid2` alias? Uses context-collapsed points-to sets so the
    /// result is sound regardless of the configured k-CFA depth. Also applies
    /// the type-parameter heuristic: two parameters of the same type and index
    /// in different functions may alias.
    pub fn alias(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        // Same instance and local - check array_index and field for disambiguation
        if aid1.instance_id == aid2.instance_id && aid1.local == aid2.local {
            // If both have field values, they must match for aliasing
            match (aid1.field, aid2.field) {
                (Some(f1), Some(f2)) => {
                    return if f1 == f2 {
                        ApproximateAliasKind::Probably
                    } else {
                        ApproximateAliasKind::Unlikely
                    };
                }
                (Some(_), None) | (None, Some(_)) => {
                    // One has field, one doesn't - conservative: they could be same
                    return ApproximateAliasKind::Possibly;
                }
                (None, None) => {}
            }
            // If both have array indices, they must match
            if let (Some(i), Some(j)) = (aid1.array_index, aid2.array_index) {
                return if i == j {
                    ApproximateAliasKind::Probably
                } else {
                    ApproximateAliasKind::Unlikely
                };
            }
            // If neither has array index, they definitely alias
            if aid1.array_index.is_none() && aid2.array_index.is_none() {
                return ApproximateAliasKind::Probably;
            }
            // One has array_index, one doesn't - conservative: they could be same
            return ApproximateAliasKind::Possibly;
        }

        // Different instance but same local. We cannot conclude that different
        // `field`s disallow aliasing here: the two locals may belong to distinct
        // closure environments / receivers whose field indexes are unrelated
        // (e.g. `(env_a).0` vs `(env_b).1`), so a syntactic field mismatch is
        // unsound. Fall through to the points-to query, which projects the field
        // and compares the actual pointees (this is what keeps `self.mu` apart
        // from `self.rw1` while still merging the same field across functions).

        // Different instance or local - use points-to analysis
        let ia = self.instance_of(aid1);
        let ib = self.instance_of(aid2);
        match (ia, ib, &self.result) {
            (Some(ia), Some(ib), Some(result)) => {
                if self.pta.collapsed_may_alias_receiver(
                    result,
                    ia,
                    aid1.local.as_u32(),
                    aid1.field,
                    ib,
                    aid2.local.as_u32(),
                    aid2.field,
                ) {
                    return ApproximateAliasKind::Probably;
                }
                // Type-parameter heuristic: parameters of same type/index may
                // alias. Only applies when the field projections are compatible —
                // `self.a` and `self.b` (same `&Foo` parameter) are different
                // fields of one object and must not be merged.
                if self.may_alias_via_type_param(ia, aid1.local, ib, aid2.local) {
                    match (aid1.field, aid2.field) {
                        (Some(f1), Some(f2)) if f1 != f2 => {}
                        _ => return ApproximateAliasKind::Possibly,
                    }
                }
                ApproximateAliasKind::Unlikely
            }
            _ => ApproximateAliasKind::Unknown,
        }
    }

    /// Atomic-context alias query. Same semantics as [`Self::alias`] under the
    /// unified engine (the legacy split was an artifact of the heuristic layer).
    pub fn alias_atomic(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        self.alias(aid1, aid2)
    }

    /// Human-readable dump of the solved points-to relation (for differential
    /// comparison against the legacy engine). Call after [`Self::build`].
    pub fn format_report(&self) -> String {
        match &self.result {
            Some(r) => self.pta.format_report(r),
            None => String::from("=== PTA Points-To Report (unsolved) ===\n"),
        }
    }

    /// May `pointer` point to `pointee`?
    pub fn points_to(&mut self, pointer: AliasId, pointee: AliasId) -> ApproximateAliasKind {
        let ip = self.instance_of(pointer);
        let it = self.instance_of(pointee);
        match (ip, it, &self.result) {
            (Some(ip), Some(it), Some(result)) => {
                if self.pta.collapsed_points_to_local(
                    result,
                    ip,
                    pointer.local.as_u32(),
                    it,
                    pointee.local.as_u32(),
                ) {
                    ApproximateAliasKind::Probably
                } else {
                    ApproximateAliasKind::Unlikely
                }
            }
            _ => ApproximateAliasKind::Unknown,
        }
    }
}
