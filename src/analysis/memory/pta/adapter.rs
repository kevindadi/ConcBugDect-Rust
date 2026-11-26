//! Maps the pointer analysis onto the legacy `AliasId` query API.
//! Petri-net construction calls this surface and not the solver directly.
//! It does not change alias results beyond what the engine already computed.

extern crate rustc_middle;

use rustc_middle::mir::Local;
use rustc_middle::ty::Instance;
use rustc_middle::ty::TypingEnv;

use super::analysis::PointerAnalysis;
use super::context::Context;
use super::loc::{CiKey, ProjElem};
use super::result::PointsToResult;
use crate::analysis::memory::pointsto::{AliasId, ApproximateAliasKind, PathStep};
use rustc_data_structures::fx::FxHashSet;
use smallvec::SmallVec;

fn path_steps_to_proj(steps: &[PathStep]) -> Vec<ProjElem> {
    steps
        .iter()
        .map(|s| match s {
            PathStep::Deref => ProjElem::Deref,
            PathStep::Field(f) => ProjElem::Field(*f),
            PathStep::Index => ProjElem::Index,
            PathStep::ConstIndex(i) => ProjElem::ConstIndex(*i),
        })
        .collect()
}

/// Alias verdict for two known projection paths of the *same* local. Equal
/// paths are the same slot; paths that differ only where one has a dynamic
/// `Index` may still coincide; anything else denotes a different field or
/// element and is disjoint.
fn alias_from_paths(a: &[PathStep], b: &[PathStep]) -> ApproximateAliasKind {
    if a == b {
        return ApproximateAliasKind::Probably;
    }
    let may_overlap = a.len() == b.len()
        && a.iter().zip(b.iter()).all(|(x, y)| match (x, y) {
            (PathStep::Field(fa), PathStep::Field(fb)) => fa == fb,
            (PathStep::Deref, PathStep::Deref) => true,
            (PathStep::Index, PathStep::Index)
            | (PathStep::Index, PathStep::ConstIndex(_))
            | (PathStep::ConstIndex(_), PathStep::Index) => true,
            (PathStep::ConstIndex(i), PathStep::ConstIndex(j)) => i == j,
            _ => false,
        });
    if may_overlap {
        ApproximateAliasKind::Possibly
    } else {
        ApproximateAliasKind::Unlikely
    }
}

pub struct PtaAliasAnalysis<'tcx> {
    pta: PointerAnalysis<'tcx>,
    /// Instances in call-graph node-index order. `instances[id.index()]` is
    /// the instance `index_to_instance` used to return.
    instances: Vec<Instance<'tcx>>,
    result: Option<PointsToResult>,
}

impl<'tcx> PtaAliasAnalysis<'tcx> {
    /// Context-insensitive (`k = 0`) shim. Prefer [`Self::with_k`].
    pub fn new(tcx: rustc_middle::ty::TyCtxt<'tcx>, instances: Vec<Instance<'tcx>>) -> Self {
        Self::with_k(tcx, instances, 0)
    }

    /// Shim using call-site sensitivity depth `k` (k-CFA).
    pub fn with_k(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        instances: Vec<Instance<'tcx>>,
        k: usize,
    ) -> Self {
        Self {
            pta: PointerAnalysis::with_k(tcx, k),
            instances,
            result: None,
        }
    }

    /// Build constraints for all call-graph instances and solve. Idempotent-ish:
    /// re-solving simply recomputes from the accumulated constraints.
    pub fn build(&mut self) {
        let roots = self.instances.clone();
        self.pta.build_reachable(roots);
        self.result = Some(self.pta.solve());
    }

    /// Whether constraint generation entered `instance`. A miss means the
    /// pointer analysis has no identity for that body.
    pub fn instance_built(&self, instance: Instance<'tcx>) -> bool {
        self.pta.func_id(instance).is_some()
    }

    /// Whether `local` has a context-qualified node in a built body.
    /// Empty means the engine never named that local, so a caller must not
    /// invent an alias id from a span or a type name.
    pub fn local_built(&self, instance: Instance<'tcx>, local: u32) -> bool {
        !self.pta.var_nodes(instance, local).is_empty()
    }

    fn instance_of(&self, aid: AliasId) -> Option<Instance<'tcx>> {
        self.instances.get(aid.instance_id.index()).copied()
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
            rustc_middle::ty::EarlyBinder::bind(self.pta.tcx(), body_a.local_decls[a_local].ty),
        );
        let typing_env_b = TypingEnv::post_analysis(self.pta.tcx(), b.def_id());
        let ty_b = b.instantiate_mir_and_normalize_erasing_regions(
            self.pta.tcx(),
            typing_env_b,
            rustc_middle::ty::EarlyBinder::bind(self.pta.tcx(), body_b.local_decls[b_local].ty),
        );

        ty_a == ty_b
    }

    /// May `aid1` and `aid2` alias? Uses context-collapsed points-to sets so the
    /// result is sound regardless of the configured k-CFA depth. Also applies
    /// the type-parameter heuristic: two parameters of the same type and index
    /// in different functions may alias.
    pub fn alias(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        // Same instance and local - compare the full projection paths when
        // both are known; fall back to the legacy field/array-index rules
        // otherwise (the additive path is optional).
        if aid1.instance_id == aid2.instance_id && aid1.local == aid2.local {
            if let (Some(p1), Some(p2)) = (aid1.receiver_path, aid2.receiver_path) {
                return alias_from_paths(&p1.steps(), &p2.steps());
            }
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
                // Full projection paths (when both sides have one) let the
                // query distinguish deep fields and constant indices; the
                // legacy single-field query remains for path-less ids so their
                // behavior is unchanged.
                let alias = match (aid1.receiver_path, aid2.receiver_path) {
                    (Some(p1), Some(p2)) => {
                        let s1 = path_steps_to_proj(&p1.steps());
                        let s2 = path_steps_to_proj(&p2.steps());
                        self.pta.collapsed_may_alias_receiver_path(
                            result,
                            ia,
                            aid1.local.as_u32(),
                            &s1,
                            ib,
                            aid2.local.as_u32(),
                            &s2,
                        )
                    }
                    _ => self.pta.collapsed_may_alias_receiver(
                        result,
                        ia,
                        aid1.local.as_u32(),
                        aid1.field,
                        ib,
                        aid2.local.as_u32(),
                        aid2.field,
                    ),
                };
                match alias {
                    // Intersecting sets: the receivers may be the same object.
                    Some(true) => return ApproximateAliasKind::Probably,
                    // Both sets are non-empty and disjoint: provable no-alias.
                    Some(false) => {}
                    // An empty receiver set is unresolved, not an absence.
                    // Fall through to the unknown policy: Conservative merges
                    // the lock sites (may-alias), Optimistic keeps them apart.
                    None => return ApproximateAliasKind::Unknown,
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

    /// Lock-grouping alias query (P3 call-site sensitivity).
    ///
    /// Compares the two acquisition receivers per k-CFA context instead of on
    /// the context-collapsed union: only contexts in which both sites run are
    /// compared, so two sites reaching different objects in every shared
    /// context are reported disjoint even when the collapsed union intersects.
    ///
    /// Only the different-`(instance, local)` case with full projection paths
    /// on both sides is evaluated this way. When the per-context query is
    /// inconclusive (`None`: no shared context, or an unresolved receiver in a
    /// shared context) it falls back to [`Self::alias`], which keeps the sound
    /// collapsed result and the configured unknown policy.
    pub fn alias_lock_group_with_fallback(
        &mut self,
        aid1: AliasId,
        aid2: AliasId,
    ) -> ApproximateAliasKind {
        if aid1.instance_id != aid2.instance_id || aid1.local != aid2.local {
            if let (Some(p1), Some(p2)) = (aid1.receiver_path, aid2.receiver_path) {
                let ia = self.instance_of(aid1);
                let ib = self.instance_of(aid2);
                let classification =
                    if let (Some(ia), Some(ib), Some(result)) = (ia, ib, &self.result) {
                        let s1 = path_steps_to_proj(&p1.steps());
                        let s2 = path_steps_to_proj(&p2.steps());
                        let ca = self.pta.receiver_points_to_path_by_context(
                            result,
                            ia,
                            aid1.local.as_u32(),
                            &s1,
                        );
                        let cb = self.pta.receiver_points_to_path_by_context(
                            result,
                            ib,
                            aid2.local.as_u32(),
                            &s2,
                        );
                        self.pta.classify_receiver_alias_by_context(&ca, &cb)
                    } else {
                        None
                    };
                match classification {
                    // Shared precise context, field keys overlap.
                    Some(true) => return ApproximateAliasKind::Probably,
                    // Shared precise context, field keys are disjoint.
                    Some(false) => return ApproximateAliasKind::Unlikely,
                    // No solved pointee. The receiver paths still name slots:
                    // `(*p).0` and `(*p).1` are different fields, so they stay
                    // apart. Equal paths and index wildcards fall through to
                    // the collapsed query.
                    None => {
                        if alias_from_paths(&p1.steps(), &p2.steps())
                            == ApproximateAliasKind::Unlikely
                        {
                            return ApproximateAliasKind::Unlikely;
                        }
                        return self.alias(aid1, aid2);
                    }
                }
            }
        }
        self.alias(aid1, aid2)
    }

    /// Human-readable dump of the solved points-to relation (for differential
    /// comparison against the legacy engine). Call after [`Self::build`].
    pub fn format_report(&self) -> String {
        match &self.result {
            Some(r) => self.pta.format_report(r),
            None => String::from("=== Spn Points-To Report (unsolved) ===\n"),
        }
    }

    /// Distinct proven-constant argument vectors observed at the
    /// call sites that resolved to `instance`.
    pub fn call_arg_const_vectors(
        &self,
        instance: Instance<'tcx>,
    ) -> &[SmallVec<[Option<u64>; 4]>] {
        self.pta.call_arg_const_vectors(instance)
    }

    /// Proven-constant argument vectors recorded for the concrete
    /// call site `(caller, bb)`.
    pub fn call_site_arg_const_vectors(
        &self,
        caller: Instance<'tcx>,
        bb: u32,
    ) -> &[SmallVec<[Option<u64>; 4]>] {
        self.pta.call_site_arg_const_vectors(caller, bb)
    }

    /// Proven-constant parameter vectors per k-CFA context for
    /// `instance`.
    pub fn param_values_by_context(
        &self,
        instance: Instance<'tcx>,
    ) -> Vec<(Context, SmallVec<[Option<u64>; 4]>)> {
        self.pta.param_values_by_context(instance)
    }

    /// Per-context receiver points-to identity for a lock receiver
    /// (full projection path on the `AliasId`). Empty when the id carries no
    /// path or the instance is unknown.
    pub fn receiver_keys_by_context(&mut self, aid: AliasId) -> Vec<(Context, FxHashSet<CiKey>)> {
        let Some(path) = aid.receiver_path else {
            return Vec::new();
        };
        let Some(instance) = self.instance_of(aid) else {
            return Vec::new();
        };
        let Some(result) = self.result.as_ref() else {
            return Vec::new();
        };
        let steps = path_steps_to_proj(&path.steps());
        self.pta
            .receiver_points_to_path_by_context(result, instance, aid.local.as_u32(), &steps)
    }

    /// Is the key an exact object (no dynamic `Index` summary
    /// element)? See `PointerAnalysis::ci_key_is_exact`.
    pub fn ci_key_is_exact(&self, key: &CiKey) -> bool {
        self.pta.ci_key_is_exact(key)
    }

    /// Object identity names of a receiver key set under one proven
    /// constant vector (`None`: empty or inexact). See
    /// `PointerAnalysis::guard_object_identity_names`.
    pub fn guard_object_identity_names(&self, keys: &[CiKey]) -> Option<Vec<String>> {
        self.pta.guard_object_identity_names(keys)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_paths_are_the_same_slot() {
        let p = [PathStep::Deref, PathStep::Field(0), PathStep::ConstIndex(1)];
        assert_eq!(alias_from_paths(&p, &p), ApproximateAliasKind::Probably);
    }

    #[test]
    fn distinct_fields_and_const_indices_are_disjoint() {
        assert_eq!(
            alias_from_paths(&[PathStep::Field(0)], &[PathStep::Field(1)]),
            ApproximateAliasKind::Unlikely
        );
        assert_eq!(
            alias_from_paths(
                &[PathStep::Deref, PathStep::ConstIndex(0)],
                &[PathStep::Deref, PathStep::ConstIndex(1)]
            ),
            ApproximateAliasKind::Unlikely
        );
        // Different lengths (field vs sub-field) are different slots.
        assert_eq!(
            alias_from_paths(
                &[PathStep::Field(0)],
                &[PathStep::Field(0), PathStep::Field(0)]
            ),
            ApproximateAliasKind::Unlikely
        );
    }

    #[test]
    fn different_fields_of_one_receiver_stay_disjoint_without_pointees() {
        // `AccountPair.primary` / `.secondary`. The points-to sets can be
        // empty; the paths still name two slots, so the lock query must not
        // collapse them.
        let primary = [PathStep::Deref, PathStep::Field(0)];
        let secondary = [PathStep::Deref, PathStep::Field(1)];
        assert_eq!(
            alias_from_paths(&primary, &secondary),
            ApproximateAliasKind::Unlikely
        );
        assert_eq!(
            alias_from_paths(&primary, &primary),
            ApproximateAliasKind::Probably
        );
    }

    #[test]
    fn dynamic_index_may_alias_a_constant_index() {
        assert_eq!(
            alias_from_paths(
                &[PathStep::Deref, PathStep::Index],
                &[PathStep::Deref, PathStep::ConstIndex(3)]
            ),
            ApproximateAliasKind::Possibly
        );
    }

    #[test]
    fn path_steps_map_onto_projection_elements() {
        let steps = [
            PathStep::Deref,
            PathStep::Field(2),
            PathStep::Index,
            PathStep::ConstIndex(5),
        ];
        assert_eq!(
            path_steps_to_proj(&steps),
            vec![
                ProjElem::Deref,
                ProjElem::Field(2),
                ProjElem::Index,
                ProjElem::ConstIndex(5)
            ]
        );
    }
}
