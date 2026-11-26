//! One union-find for synchronization sites.
//!
//! Pairwise rule ([`same_object`]):
//!
//! 1. Different [`SiteKind`]s never merge. A mutex and an atomic are different
//!    objects even when a pointer analysis says the locals may alias.
//! 2. [`type_compatible`] must hold. Different structs, including the
//!    protected types of two locks (`Chan<T>` versus `Option<T>`), stay apart.
//! 3. A definite alias (`Probably` or `Possibly`) merges.
//! 4. `Unknown` follows [`AliasUnknownPolicy`]: conservative merges, optimistic
//!    does not. `Unlikely` never merges.
//!
//! Lock guards merge when the receiver query `may_alias`s under the policy.
//! `group_lock_guards` is that walk plus a type check.

use rustc_data_structures::fx::FxHashMap;

use crate::analysis::memory::alias_engine::AliasEngine;
use crate::analysis::memory::pointsto::{AliasId, ApproximateAliasKind};
use crate::analysis::primitives::blocking::LockGuardId;
use crate::config::AliasUnknownPolicy;

use super::ty::{TypeKey, type_compatible, type_keys_compatible};
use super::{SiteKind, SyncSite};

/// The pairwise predicate, on structural types so tests do not need a `TyCtxt`.
pub fn same_object(
    kind_a: SiteKind,
    kind_b: SiteKind,
    ty_a: &TypeKey,
    ty_b: &TypeKey,
    alias: ApproximateAliasKind,
    policy: AliasUnknownPolicy,
) -> bool {
    kind_a == kind_b && type_keys_compatible(ty_a, ty_b) && alias.may_alias(policy)
}

/// Group lock guards. `same_type` is the type half of [`same_object`].
/// Callers that build places must iterate `values()` and must not sort it:
/// the root-discovery order is what names `Mutex_N` / `RwLock_N`.
pub(crate) fn group_lock_guards(
    lockid_vec: &[LockGuardId],
    alias_id_for: impl Fn(&LockGuardId) -> AliasId,
    mut fallback: impl FnMut(AliasId, AliasId) -> ApproximateAliasKind,
    policy: AliasUnknownPolicy,
    mut same_type: impl FnMut(&LockGuardId, &LockGuardId) -> bool,
) -> FxHashMap<LockGuardId, Vec<LockGuardId>> {
    let mut union_find: FxHashMap<LockGuardId, LockGuardId> = FxHashMap::default();
    for lock_id in lockid_vec {
        union_find.insert(*lock_id, *lock_id);
    }

    // Two guards belong to the same lock resource when the lock objects
    // they protect may alias. We compare the acquiring receivers, not the
    // guards: distinct guards of one mutex are different objects.
    for i in 0..lockid_vec.len() {
        for j in i + 1..lockid_vec.len() {
            if !same_type(&lockid_vec[i], &lockid_vec[j]) {
                continue;
            }
            let ri = alias_id_for(&lockid_vec[i]);
            let rj = alias_id_for(&lockid_vec[j]);
            let result = fallback(ri, rj);
            if result.may_alias(policy) {
                union_guard(&mut union_find, &lockid_vec[i], &lockid_vec[j]);
            }
        }
    }

    let mut temp_groups: FxHashMap<LockGuardId, Vec<LockGuardId>> = FxHashMap::default();
    for lock_id in lockid_vec {
        let root = find_guard(&union_find, lock_id);
        temp_groups.entry(root).or_default().push(*lock_id);
    }
    temp_groups
}

fn find_guard(union_find: &FxHashMap<LockGuardId, LockGuardId>, x: &LockGuardId) -> LockGuardId {
    let mut current = x;
    while union_find[current] != *current {
        current = &union_find[current];
    }
    current.clone()
}

fn union_guard(
    union_find: &mut FxHashMap<LockGuardId, LockGuardId>,
    x: &LockGuardId,
    y: &LockGuardId,
) {
    let root_x = find_guard(union_find, x);
    let root_y = find_guard(union_find, y);
    if root_x != root_y {
        union_find.insert(root_y, root_x);
    }
}

/// Equivalence classes of `sites` under [`same_object`], plus the lock-style
/// unknown bridge when both sites are locks. Condition-variable sites are
/// left singleton: each mailbox place carries one initial token, and merging
/// them would change that token count. Alias lookup at the call site still
/// connects notify and wait.
pub(crate) fn partition_indices<'a, 'tcx>(
    sites: &[SyncSite<'tcx>],
    alias: &mut AliasEngine<'tcx>,
    policy: AliasUnknownPolicy,
) -> Vec<Vec<usize>> {
    let n = sites.len();
    let mut parent: Vec<usize> = (0..n).collect();
    for i in 0..n {
        for j in i + 1..n {
            if !pair_merges(&sites[i], &sites[j], alias, policy) {
                continue;
            }
            let ri = find_index(&parent, i);
            let rj = find_index(&parent, j);
            if ri != rj {
                parent[rj] = ri;
            }
        }
    }
    let mut groups: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for i in 0..n {
        groups.entry(find_index(&parent, i)).or_default().push(i);
    }
    let mut ordered: Vec<Vec<usize>> = groups.into_values().collect();
    ordered.sort_by_key(|group| group[0]);
    ordered
}

fn find_index(parent: &[usize], mut x: usize) -> usize {
    while parent[x] != x {
        x = parent[x];
    }
    x
}

fn pair_merges<'a, 'tcx>(
    a: &SyncSite<'tcx>,
    b: &SyncSite<'tcx>,
    alias: &mut AliasEngine<'tcx>,
    policy: AliasUnknownPolicy,
) -> bool {
    if a.kind != b.kind || !type_compatible(a.ty, b.ty) {
        return false;
    }
    // One mailbox token per collected condvar. See `partition_indices`.
    if a.kind == SiteKind::Condvar {
        return false;
    }
    if a.object == b.object {
        return true;
    }
    // Lock place groups, including the unknown-bridge guard, are built by
    // `group_lock_guards` so `Mutex_N` keeps its previous root order. This
    // index partition is the atomic / unsafe / custom-lock pass.
    may_alias_pair(alias, a, b).may_alias(policy)
}

fn may_alias_pair<'a, 'tcx>(
    alias: &mut AliasEngine<'tcx>,
    a: &SyncSite<'tcx>,
    b: &SyncSite<'tcx>,
) -> ApproximateAliasKind {
    match a.kind {
        SiteKind::Mutex | SiteKind::RwLock => {
            alias.alias_lock_group_with_fallback(a.object, b.object)
        }
        SiteKind::Atomic => alias.alias_atomic(a.object, b.object),
        SiteKind::Unsafe | SiteKind::Condvar => alias.alias(a.object, b.object),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::NodeIndex;
    use rustc_middle::mir::Local;

    fn adt(path: &str) -> TypeKey {
        TypeKey::Adt {
            path: path.to_string(),
            args: Vec::new(),
        }
    }

    fn guard(local: u32) -> LockGuardId {
        LockGuardId::new(NodeIndex::new(0), Local::from_u32(local))
    }

    fn receiver(local: u32) -> AliasId {
        AliasId::new(NodeIndex::new(1), Local::from_u32(local))
    }

    #[test]
    fn different_kinds_do_not_merge() {
        let ty = adt("std::sync::Mutex");
        assert!(!same_object(
            SiteKind::Mutex,
            SiteKind::Condvar,
            &ty,
            &ty,
            ApproximateAliasKind::Probably,
            AliasUnknownPolicy::Conservative,
        ));
    }

    #[test]
    fn different_types_do_not_merge() {
        assert!(!same_object(
            SiteKind::Mutex,
            SiteKind::Mutex,
            &adt("flume::Chan"),
            &adt("core::option::Option"),
            ApproximateAliasKind::Probably,
            AliasUnknownPolicy::Conservative,
        ));
    }

    #[test]
    fn definite_alias_merges() {
        let ty = adt("u64");
        assert!(same_object(
            SiteKind::Atomic,
            SiteKind::Atomic,
            &ty,
            &ty,
            ApproximateAliasKind::Probably,
            AliasUnknownPolicy::Optimistic,
        ));
        assert!(same_object(
            SiteKind::Atomic,
            SiteKind::Atomic,
            &ty,
            &ty,
            ApproximateAliasKind::Possibly,
            AliasUnknownPolicy::Optimistic,
        ));
    }

    #[test]
    fn unknown_follows_policy() {
        let ty = adt("u64");
        assert!(same_object(
            SiteKind::Atomic,
            SiteKind::Atomic,
            &ty,
            &ty,
            ApproximateAliasKind::Unknown,
            AliasUnknownPolicy::Conservative,
        ));
        assert!(!same_object(
            SiteKind::Atomic,
            SiteKind::Atomic,
            &ty,
            &ty,
            ApproximateAliasKind::Unknown,
            AliasUnknownPolicy::Optimistic,
        ));
        assert!(!same_object(
            SiteKind::Atomic,
            SiteKind::Atomic,
            &ty,
            &ty,
            ApproximateAliasKind::Unlikely,
            AliasUnknownPolicy::Conservative,
        ));
    }

    #[test]
    fn type_filter_splits_a_lock_group_the_alias_would_merge() {
        let guards = [guard(1), guard(2)];
        let groups = group_lock_guards(
            &guards,
            |_| receiver(10),
            |_, _| ApproximateAliasKind::Probably,
            AliasUnknownPolicy::Conservative,
            |a, b| a.local == b.local,
        );
        assert_eq!(groups.len(), 2);
    }

    #[test]
    fn same_type_and_alias_still_merge_locks() {
        let guards = [guard(1), guard(2)];
        let groups = group_lock_guards(
            &guards,
            |_| receiver(10),
            |_, _| ApproximateAliasKind::Probably,
            AliasUnknownPolicy::Conservative,
            |_, _| true,
        );
        assert_eq!(groups.len(), 1);
    }
}
