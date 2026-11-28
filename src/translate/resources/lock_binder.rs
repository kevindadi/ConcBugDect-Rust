//! Lock binder: turns already-grouped lock classes into `Mutex_N` / `RwLock_N`
//! places. Alias grouping lives in `analysis::sync::group_locks`;
//! the broader resource places (atomics, unsafe, condvars) live in
//! `bind_resources`.

use crate::translate::net::NetBuilder;
use rustc_data_structures::fx::FxHashMap;

use crate::analysis::callgraph::{CallGraph, InstanceId};
use crate::analysis::memory::pointsto::AliasId;
use crate::analysis::primitives::blocking::{
    LockGuardId, LockGuardInfo, LockGuardMap, LockGuardTy,
};
use crate::analysis::sync::group_locks::CustomLockSite;
use crate::translate::net::ResourceRegistry;

pub struct BinderInput<'a, 'tcx> {
    pub guards: &'a FxHashMap<InstanceId, LockGuardMap<'tcx>>,
    pub lock_objects: &'a FxHashMap<LockGuardId, AliasId>,
    pub custom_sites: &'a [CustomLockSite<'tcx>],
    pub callgraph: &'a CallGraph<'tcx>,
    /// Guard classes in root-discovery order. This order names `Mutex_N`.
    pub guard_groups: &'a [Vec<LockGuardId>],
    /// Indices into `custom_sites`, already ordered for place creation.
    pub custom_groups: &'a [Vec<usize>],
}

/// Guard classes in the order places were created. `count` includes custom-lock
/// classes, matching the old slot list.
pub struct ResourceBinder {
    groups: Vec<Vec<LockGuardId>>,
    count: usize,
}

impl ResourceBinder {
    pub(crate) fn empty() -> Self {
        Self {
            groups: Vec::new(),
            count: 0,
        }
    }

    pub(crate) fn group_count(&self) -> usize {
        self.count
    }

    pub(crate) fn groups(&self) -> &[Vec<LockGuardId>] {
        &self.groups
    }

    pub fn bind<'tcx>(
        input: BinderInput<'_, 'tcx>,
        builder: &mut NetBuilder<'_>,
        resources: &mut ResourceRegistry,
    ) -> Self {
        let BinderInput {
            guards,
            lock_objects,
            custom_sites,
            callgraph,
            guard_groups,
            custom_groups,
        } = input;

        let mut info: FxHashMap<LockGuardId, LockGuardInfo<'tcx>> = FxHashMap::default();
        for (_, map) in guards.iter() {
            info.extend(map.clone());
        }

        let alias_id_for = |guard: &LockGuardId| -> AliasId {
            lock_objects
                .get(guard)
                .copied()
                .unwrap_or_else(|| guard.clone().into())
        };

        let mut groups = Vec::new();
        let mut group_id = 0;
        for group in guard_groups {
            groups.push(group.clone());
            let rx_names: Vec<String> = group
                .iter()
                .map(|g| {
                    let rx = alias_id_for(g);
                    let fn_name = callgraph
                        .index_to_instance(rx.instance_id)
                        .map(|n| crate::util::format_name(n.instance().def_id()))
                        .unwrap_or_default();
                    let fn_name = fn_name.rsplit("::").take(2).collect::<Vec<_>>().join("::");
                    format!(
                        "{}::_{:?}(rx{}f{:?})",
                        fn_name,
                        g.local,
                        rx.local.index(),
                        rx.field
                    )
                })
                .collect();
            log::warn!(
                "[lockgroup-detail] group{} {:?} = {}",
                group_id,
                rx_names,
                match &info[&group[0]].lockguard_ty {
                    LockGuardTy::StdMutex(_) => "StdMutex",
                    LockGuardTy::ParkingLotMutex(_) => "ParkingLotMutex",
                    LockGuardTy::SpinMutex(_) => "SpinMutex",
                    _ => "RwLock",
                }
            );
            let rwlock = !matches!(
                info[&group[0]].lockguard_ty,
                LockGuardTy::StdMutex(_)
                    | LockGuardTy::ParkingLotMutex(_)
                    | LockGuardTy::SpinMutex(_)
            );
            log::debug!(
                "Creating {} node: {}_{}",
                if rwlock { "RwLock" } else { "Mutex" },
                if rwlock { "RwLock" } else { "Mutex" },
                group_id
            );
            let lock_node = crate::translate::resources::add_lock_place(builder, group_id, rwlock);
            for lock in group {
                let alias_id = lock.get_alias_id();
                resources.locks_mut().insert(alias_id, lock_node);
            }
            group_id += 1;
        }
        crate::translate::resources::install_custom_lock_groups(
            custom_sites,
            custom_groups,
            builder,
            resources,
            &mut group_id,
        );
        Self {
            groups,
            count: group_id,
        }
    }
}
