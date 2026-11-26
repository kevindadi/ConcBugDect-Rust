//! Lock alias grouping. Place creation stays in `translate`.

use std::cell::RefCell;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;

use crate::analysis::callgraph::{CallGraph, InstanceId};
use crate::analysis::memory::alias_engine::AliasEngine;
use crate::analysis::memory::ownership::{CustomLockMethod, CustomLockMode};
use crate::analysis::memory::pointsto::{AliasId, ApproximateAliasKind};
use crate::analysis::primitives::blocking::{LockGuardId, LockGuardInfo, LockGuardMap};
use crate::config::AliasUnknownPolicy;

/// One recognized guard-less custom lock method instance, before
/// grouping. `receiver` is the `arg0` (`&self`) lock object the method
/// operates on; grouping compares those.
pub struct CustomLockSite<'tcx> {
    pub(crate) instance_id: InstanceId,
    pub(crate) instance: rustc_middle::ty::Instance<'tcx>,
    pub(crate) receiver: AliasId,
    pub(crate) method: CustomLockMethod,
    pub(crate) name: String,
    pub(crate) def_id: DefId,
}

/// Guard maps and custom-lock methods rebuilt from collected sites.
///
/// Guard read/write types come from `guard_info` recorded when the site was
/// built. A missing entry is a coverage gap.
pub(crate) fn lock_records_from_sites<'tcx>(
    sites: &[crate::analysis::sync::SyncSite<'tcx>],
    guard_info: &FxHashMap<LockGuardId, LockGuardInfo<'tcx>>,
    callgraph: &CallGraph<'tcx>,
) -> (
    FxHashMap<InstanceId, LockGuardMap<'tcx>>,
    FxHashMap<LockGuardId, AliasId>,
    Vec<CustomLockSite<'tcx>>,
) {
    use crate::analysis::sync::SiteKind;

    let mut lockguards: FxHashMap<InstanceId, LockGuardMap<'tcx>> = FxHashMap::default();
    let mut lock_objects: FxHashMap<LockGuardId, AliasId> = FxHashMap::default();
    let mut seen_guards = 0usize;
    for site in sites {
        if !matches!(site.kind, SiteKind::Mutex | SiteKind::RwLock) {
            continue;
        }
        let Some(id) = site.origin.guard() else {
            continue;
        };
        let Some(info) = guard_info.get(&id) else {
            panic!(
                "guard site {}:{} has no LockGuardInfo; collect_sync_sites did not cover it",
                id.instance_id.index(),
                id.local.as_u32()
            );
        };
        seen_guards += 1;
        lockguards
            .entry(site.instance)
            .or_default()
            .insert(id, info.clone());
        lock_objects.insert(id, site.object);
    }
    if seen_guards != guard_info.len() {
        panic!(
            "guard site coverage mismatch: sites={seen_guards} types={}",
            guard_info.len()
        );
    }

    let mut custom_sites = Vec::new();
    for site in sites {
        let Some((mode, op)) = site.origin.custom() else {
            continue;
        };
        let Some(node) = callgraph.index_to_instance(site.instance) else {
            panic!(
                "custom lock site instance {} is not in the callgraph; collect_sync_sites did not cover it",
                site.instance.index()
            );
        };
        let instance = *node.instance();
        let def_id = instance.def_id();
        custom_sites.push(CustomLockSite {
            instance_id: site.instance,
            instance,
            receiver: site.object,
            method: CustomLockMethod { mode, op },
            name: crate::util::format_name(def_id),
            def_id,
        });
    }
    custom_sites.sort_by(|left, right| {
        left.name.cmp(&right.name).then_with(|| {
            left.receiver
                .local
                .index()
                .cmp(&right.receiver.local.index())
        })
    });
    (lockguards, lock_objects, custom_sites)
}

/// The lock union-find `ResourceBinder::bind` used to run while creating
/// places. The resource phase runs it once; place installation only iterates
/// the groups.
pub(crate) fn discover_guard_groups<'analysis, 'tcx>(
    guards: &FxHashMap<InstanceId, LockGuardMap<'tcx>>,
    lock_objects: &FxHashMap<LockGuardId, AliasId>,
    alias: &mut AliasEngine<'tcx>,
    policy: AliasUnknownPolicy,
    lock_grouper: crate::config::LockGrouper,
) -> Vec<Vec<LockGuardId>> {
    let mut info: FxHashMap<LockGuardId, LockGuardInfo<'tcx>> = FxHashMap::default();
    for (_, map) in guards.iter() {
        info.extend(map.clone());
    }
    let lockid_vec: Vec<LockGuardId> = info.clone().into_keys().collect();
    let alias_id_for = |guard: &LockGuardId| -> AliasId {
        lock_objects
            .get(guard)
            .copied()
            .unwrap_or_else(|| guard.clone().into())
    };
    let alias = RefCell::new(alias);
    let temp_groups = match lock_grouper {
        crate::config::LockGrouper::Ported => crate::analysis::sync::partition::group_lock_guards(
            &lockid_vec,
            &alias_id_for,
            |ri, rj| alias.borrow_mut().alias_lock_group_with_fallback(ri, rj),
            policy,
            |_, _| true,
        ),
        crate::config::LockGrouper::Typed => crate::analysis::sync::partition::group_lock_guards(
            &lockid_vec,
            &alias_id_for,
            |ri, rj| alias.borrow_mut().alias_lock_group_with_fallback(ri, rj),
            policy,
            |left, right| {
                crate::analysis::sync::type_compatible(
                    crate::analysis::sync::guard_protected_ty(&info[left].lockguard_ty),
                    crate::analysis::sync::guard_protected_ty(&info[right].lockguard_ty),
                )
            },
        ),
        crate::config::LockGrouper::Original => group_guards(
            &lockid_vec,
            &alias_id_for,
            |ri, rj| alias.borrow_mut().alias_lock_group_with_fallback(ri, rj),
            policy,
        ),
    };
    let _alias = alias.into_inner();
    temp_groups.into_values().collect()
}

/// Custom-lock classes in the order `construct_custom_lock_groups` creates
/// places. Indices refer to `sites`.
pub(crate) fn discover_custom_groups<'analysis, 'tcx>(
    sites: &[CustomLockSite<'tcx>],
    alias: &mut AliasEngine<'tcx>,
    policy: AliasUnknownPolicy,
) -> Vec<Vec<usize>> {
    if sites.is_empty() {
        return Vec::new();
    }
    fn find_root(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    let rwlock_family = |mode: CustomLockMode| {
        matches!(
            mode,
            CustomLockMode::RwLockRead | CustomLockMode::RwLockWrite
        )
    };
    let n = sites.len();
    let mut parent: Vec<usize> = (0..n).collect();
    for i in 0..n {
        for j in i + 1..n {
            if rwlock_family(sites[i].method.mode) != rwlock_family(sites[j].method.mode) {
                continue;
            }
            let result = alias.alias_lock_group_with_fallback(sites[i].receiver, sites[j].receiver);
            log::debug!(
                "[custom-lock-group] {} rx={:?} vs {} rx={:?} => {:?}",
                sites[i].name,
                sites[i].receiver,
                sites[j].name,
                sites[j].receiver,
                result
            );
            if result.may_alias(policy) {
                let ri = find_root(&mut parent, i);
                let rj = find_root(&mut parent, j);
                if ri != rj {
                    parent[rj] = ri;
                }
            }
        }
    }
    let mut groups: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for i in 0..n {
        let root = find_root(&mut parent, i);
        groups.entry(root).or_default().push(i);
    }
    let mut ordered: Vec<Vec<usize>> = groups.into_values().collect();
    for group in &mut ordered {
        group.sort_unstable();
    }
    ordered.sort_by_key(|group| group[0]);
    ordered
}

fn find(union_find: &FxHashMap<LockGuardId, LockGuardId>, x: &LockGuardId) -> LockGuardId {
    let mut current = x;
    while union_find[current] != *current {
        current = &union_find[current];
    }
    current.clone()
}

fn union(union_find: &mut FxHashMap<LockGuardId, LockGuardId>, x: &LockGuardId, y: &LockGuardId) {
    let root_x = find(union_find, x);
    let root_y = find(union_find, y);
    if root_x != root_y {
        union_find.insert(root_y, root_x);
    }
}

/// Group lock guards. Place construction uses this union-find.
///
/// Two guards merge when `fallback` says their receivers `may_alias` under
/// `policy`. The returned map is in root-discovery order. Callers that create
/// places must iterate `values()` and must not sort it.
///
/// `group_lock_guards` is the same walk plus a type check. Installing that
/// check (`--resource-lock-grouper typed`) pulls flume's `lock::{closure#0}`
/// out of the merged lock class and the candidate count goes from 5 to 7.
/// The default places stay on this function. The shadow still reports the
/// type-split classes.
pub(crate) fn group_guards(
    lockid_vec: &[LockGuardId],
    alias_id_for: impl Fn(&LockGuardId) -> AliasId,
    mut fallback: impl FnMut(AliasId, AliasId) -> ApproximateAliasKind,
    policy: AliasUnknownPolicy,
) -> FxHashMap<LockGuardId, Vec<LockGuardId>> {
    let mut union_find: FxHashMap<LockGuardId, LockGuardId> = FxHashMap::default();
    for lock_id in lockid_vec {
        union_find.insert(*lock_id, *lock_id);
    }

    // Two guards belong to the same lock resource when the lock objects
    // they protect may alias. We compare the *acquiring receivers* (the
    // `&Mutex` passed to `lock()`), captured by `BlockingCollector`, rather
    // than the guard objects themselves: distinct guards of the same mutex
    // are different objects (so guard aliasing misses them), while their
    // receivers both point at the same lock. When a receiver is unknown we
    // fall back to guard aliasing to stay sound.
    for i in 0..lockid_vec.len() {
        for j in i + 1..lockid_vec.len() {
            let ri = alias_id_for(&lockid_vec[i]);
            let rj = alias_id_for(&lockid_vec[j]);
            let result = fallback(ri, rj);
            log::debug!(
                "[lockgroup] guard {:?}(inst={:?},local={:?}) rx={:?} vs guard {:?}(inst={:?},local={:?}) rx={:?} => {:?}",
                lockid_vec[i],
                lockid_vec[i].instance_id,
                lockid_vec[i].local,
                ri,
                lockid_vec[j],
                lockid_vec[j].instance_id,
                lockid_vec[j].local,
                rj,
                result,
            );
            if result.may_alias(policy) {
                log::debug!(
                    "Locks {:?} and {:?} may alias",
                    lockid_vec[i],
                    lockid_vec[j]
                );
                union(&mut union_find, &lockid_vec[i], &lockid_vec[j]);
            }
        }
    }

    let mut temp_groups: FxHashMap<LockGuardId, Vec<LockGuardId>> = FxHashMap::default();
    for lock_id in lockid_vec {
        let root = find(&union_find, lock_id);
        temp_groups.entry(root).or_default().push(*lock_id);
    }
    temp_groups
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::NodeIndex;
    use rustc_middle::mir::Local;

    fn guard(local: u32) -> LockGuardId {
        LockGuardId::new(NodeIndex::new(0), Local::from_u32(local))
    }

    fn receiver(local: u32) -> AliasId {
        AliasId::new(NodeIndex::new(1), Local::from_u32(local))
    }

    fn group_count(groups: &FxHashMap<LockGuardId, Vec<LockGuardId>>) -> usize {
        groups.len()
    }

    #[test]
    fn same_receiver_merges() {
        let guards = [guard(1), guard(2)];
        let shared = receiver(10);
        let groups = group_guards(
            &guards,
            |_| shared,
            |_, _| ApproximateAliasKind::Probably,
            AliasUnknownPolicy::Conservative,
        );
        assert_eq!(group_count(&groups), 1);
        assert_eq!(groups.values().next().unwrap().len(), 2);
    }

    #[test]
    fn different_receivers_do_not_merge() {
        let guards = [guard(1), guard(2)];
        let groups = group_guards(
            &guards,
            |guard| {
                if guard.local.index() == 1 {
                    receiver(10)
                } else {
                    receiver(11)
                }
            },
            |_, _| ApproximateAliasKind::Unlikely,
            AliasUnknownPolicy::Conservative,
        );
        assert_eq!(group_count(&groups), 2);
    }

    #[test]
    fn unknown_alias_merges_under_conservative_policy() {
        let guards = [guard(1), guard(2)];
        let groups = group_guards(
            &guards,
            |guard| receiver(guard.local.index() as u32),
            |_, _| ApproximateAliasKind::Unknown,
            AliasUnknownPolicy::Conservative,
        );
        assert_eq!(group_count(&groups), 1);
        assert_eq!(groups.values().next().unwrap().len(), 2);
    }
}
