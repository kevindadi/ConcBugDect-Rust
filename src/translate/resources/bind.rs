//! Library resource places: locks, atomics, unsafe groups, condvars.

use crate::analysis::api_patterns::RWLOCK_CAPACITY;
use crate::analysis::memory::ownership::CustomLockMode;
use crate::analysis::primitives::atomic::AtomicOrdering;
use crate::analysis::primitives::blocking::LockGuardId;
use crate::analysis::sync::group_locks::{CustomLockSite, lock_records_from_sites};
use crate::analysis::sync::{SlotId, SyncSite};
use crate::pipeline::analyze::ClassKind;
use crate::translate::construct::PetriNet;
use crate::translate::net::CustomLockEntry;
use crate::translate::net::{NetBuilder, PlaceClass, PlaceId};
use crate::translate::resources::lock_binder::{BinderInput, ResourceBinder};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use std::sync::Arc;

impl<'analysis, 'tcx> PetriNet<'analysis, 'tcx> {
    fn classes_of(&self, kind: ClassKind) -> Vec<Vec<usize>> {
        self.plan
            .classes
            .iter()
            .filter(|class| class.kind == kind)
            .map(|class| class.members.clone())
            .collect()
    }

    pub fn construct_atomic_places(&mut self) {
        if self.options.config.resource_atomic_partition == crate::config::PartitionSwitch::Legacy {
            self.construct_atomic_resources_legacy();
            return;
        }
        let classes = self.classes_of(ClassKind::Atomic);
        if classes.is_empty() {
            log::warn!("Not Found Atomic Variables In This Crate");
            return;
        }
        for members in classes {
            let place = add_atomic_place(&mut self.net, &self.plan.sites[members[0]]);
            for index in members {
                let site = &self.plan.sites[index];
                let Some(alias_id) = site.origin.alias() else {
                    continue;
                };
                if let Some(order) = site.atomic_order() {
                    self.resources.atomic_orders_mut().insert(alias_id, order);
                } else {
                    log::warn!(
                        "atomic variable {:?} has no recorded operations; ordering fallback to Relaxed",
                        alias_id
                    );
                    self.resources
                        .atomic_orders_mut()
                        .insert(alias_id, AtomicOrdering::Relaxed);
                }
                self.resources
                    .atomic_places_mut()
                    .insert(alias_id, vec![place]);
            }
        }
    }

    pub(crate) fn construct_unsafe_places(&mut self) {
        // No Petri-net place: the class id is what `UnsafeAccess` records.
        // Adding an unconnected place would change every net's place count.
        let classes = self.classes_of(ClassKind::Unsafe);
        if classes.is_empty() {
            log::debug!("Not Found Unsafe Blocks In This Crate");
            return;
        }
        for (group_id, class) in classes.iter().enumerate() {
            for &index in class {
                if let Some(alias) = self.plan.sites[index].origin.alias() {
                    self.resources
                        .unsafe_groups_mut()
                        .insert(alias, group_id as u32);
                }
            }
        }
    }

    pub fn construct_lock_places(&mut self) {
        let guard_info = self.plan.inputs.guard_info.clone();
        let condvars = self.plan.inputs.condvars.clone();
        let (lockguards, lock_objects, custom_sites) =
            lock_records_from_sites(&self.plan.sites, &guard_info, self.callgraph);
        let guard_groups = self.guard_groups_from_classes();
        let custom_groups = self.custom_groups_from_classes(&custom_sites);
        self.install_condvar_places(condvars);
        for guards in lockguards.values() {
            Arc::make_mut(&mut self.lock_info).extend(guards.clone());
        }
        if lockguards.is_empty() && custom_sites.is_empty() {
            log::debug!("Not Found Lockguards In This Crate");
            return;
        }

        let output = ResourceBinder::bind(
            BinderInput {
                guards: &lockguards,
                lock_objects: &lock_objects,
                custom_sites: &custom_sites,
                callgraph: self.callgraph,
                guard_groups: &guard_groups,
                custom_groups: &custom_groups,
            },
            &mut self.net,
            &mut self.resources,
        );
        self.resource_binder = output;
        log::debug!(
            "Total lock groups discovered: {}",
            self.resource_binder.group_count()
        );
        self.record_lock_shadow(&lockguards, &lock_objects);
    }

    /// Guard classes in the order the resource phase discovered them.
    fn guard_groups_from_classes(&self) -> Vec<Vec<LockGuardId>> {
        self.classes_of(ClassKind::Lock)
            .into_iter()
            .map(|members| {
                members
                    .iter()
                    .map(|&index| {
                        self.plan.sites[index]
                            .origin
                            .guard()
                            .expect("lock class member is a guard site")
                    })
                    .collect()
            })
            .collect()
    }

    /// Indices into the sorted custom-lock list, in class order.
    fn custom_groups_from_classes(&self, custom_sites: &[CustomLockSite<'tcx>]) -> Vec<Vec<usize>> {
        let mut pos = FxHashMap::default();
        for (index, site) in custom_sites.iter().enumerate() {
            pos.insert(site.instance_id, index);
        }
        self.classes_of(ClassKind::CustomLock)
            .into_iter()
            .map(|members| {
                members
                    .iter()
                    .map(|&index| {
                        let instance = self.plan.sites[index].instance;
                        *pos.get(&instance)
                            .expect("custom class member is a custom-lock site")
                    })
                    .collect()
            })
            .collect()
    }

    pub(crate) fn fill_resource_map(&mut self) {
        use crate::analysis::sync::{ResourceMap, SiteKind, SlotId};

        let mut assignment = FxHashMap::default();
        let mut slot_place: Vec<Option<PlaceId>> = Vec::new();
        let mut place_slot: FxHashMap<PlaceId, u32> = FxHashMap::default();
        let mut unsafe_slot: FxHashMap<u32, u32> = FxHashMap::default();
        for site in &self.plan.sites.clone() {
            if site.kind == SiteKind::Unsafe {
                if let Some(alias) = site.origin.alias() {
                    if let Some(&group) = self.resources.unsafe_groups().get(&alias) {
                        let slot = if let Some(slot) = unsafe_slot.get(&group) {
                            *slot
                        } else {
                            let slot = slot_place.len() as u32;
                            slot_place.push(None);
                            unsafe_slot.insert(group, slot);
                            slot
                        };
                        assignment.insert(site.key(), SlotId(slot));
                        continue;
                    }
                }
            }
            let found = self.registry_place(site);
            let slot = if let Some(place) = found {
                if let Some(slot) = place_slot.get(&place) {
                    *slot
                } else {
                    let slot = slot_place.len() as u32;
                    slot_place.push(Some(place));
                    place_slot.insert(place, slot);
                    slot
                }
            } else {
                let slot = slot_place.len() as u32;
                slot_place.push(None);
                slot
            };
            assignment.insert(site.key(), SlotId(slot));
        }
        let map = ResourceMap::from_assignment(slot_place.len(), assignment);
        let mut binding = PlaceBinding::new(slot_place.len());
        for (slot, place) in slot_place.into_iter().enumerate() {
            if let Some(place) = place {
                binding.set(SlotId(slot as u32), place);
            }
        }
        self.resource_map = map;
        self.place_binding = binding;
    }

    fn registry_place(&self, site: &crate::analysis::sync::SyncSite<'tcx>) -> Option<PlaceId> {
        use crate::analysis::sync::{SiteKind, SiteOrigin};
        match site.origin {
            SiteOrigin::Guard(id) => self.resources.locks().get(&id.get_alias_id()).copied(),
            SiteOrigin::Custom { .. } => self
                .resources
                .custom_locks()
                .get(&site.instance)
                .map(|entry| entry.place),
            SiteOrigin::Condvar(id) => self
                .resources
                .condvars()
                .get(&crate::analysis::memory::pointsto::AliasId::from(id))
                .copied(),
            SiteOrigin::Alias(alias) => match site.kind {
                SiteKind::Atomic => self
                    .resources
                    .atomic_places()
                    .get(&alias)
                    .and_then(|places| places.first().copied()),
                _ => None,
            },
        }
    }
}

pub(crate) fn custom_lock_sets(
    resources: &crate::translate::net::ResourceRegistry,
) -> Vec<std::collections::BTreeSet<String>> {
    let mut by_place: FxHashMap<PlaceId, std::collections::BTreeSet<String>> = FxHashMap::default();
    for (instance, entry) in resources.custom_locks() {
        by_place
            .entry(entry.place)
            .or_default()
            .insert(instance.index().to_string());
    }
    by_place.into_values().collect()
}

pub(crate) fn custom_class_sets(
    sites: &[crate::analysis::sync::SyncSite<'_>],
    classes: &[Vec<usize>],
) -> Vec<std::collections::BTreeSet<String>> {
    classes
        .iter()
        .filter(|class| sites[class[0]].origin.custom().is_some())
        .map(|class| {
            class
                .iter()
                .map(|index| sites[*index].instance.index().to_string())
                .collect()
        })
        .collect()
}

/// Slot to Petri-net place. Condition-variable and unsafe slots stay empty.
pub struct PlaceBinding {
    slot_to_place: Vec<Option<PlaceId>>,
}

impl PlaceBinding {
    pub fn new(slots: usize) -> Self {
        Self {
            slot_to_place: vec![None; slots],
        }
    }

    pub fn set(&mut self, slot: SlotId, place: PlaceId) {
        if let Some(entry) = self.slot_to_place.get_mut(slot.0 as usize) {
            *entry = Some(place);
        }
    }

    pub fn place(&self, slot: SlotId) -> Option<PlaceId> {
        self.slot_to_place.get(slot.0 as usize).copied().flatten()
    }
}

impl Default for PlaceBinding {
    fn default() -> Self {
        Self::new(0)
    }
}

pub(crate) fn add_lock_place(
    builder: &mut NetBuilder<'_>,
    group_id: usize,
    rwlock: bool,
) -> PlaceId {
    if rwlock {
        let place = builder.place(
            PlaceClass::Resource(()),
            format!("RwLock_{group_id}"),
            RWLOCK_CAPACITY,
        );
        builder.set_tokens(place, RWLOCK_CAPACITY);
        place
    } else {
        let place = builder.place(PlaceClass::Resource(()), format!("Mutex_{group_id}"), 1);
        builder.set_tokens(place, 1);
        place
    }
}

pub(crate) fn add_atomic_place(builder: &mut NetBuilder<'_>, site: &SyncSite<'_>) -> PlaceId {
    builder.add_place(
        format!("Atomic({},{})", site.instance.index(), site.local.as_u32()),
        1,
        1,
        PlaceClass::Resource(()),
        site.span.clone(),
    )
}

pub(crate) fn install_custom_lock_groups<'tcx>(
    sites: &[CustomLockSite<'tcx>],
    groups: &[Vec<usize>],
    builder: &mut NetBuilder<'_>,
    resources: &mut crate::translate::net::ResourceRegistry,
    group_id: &mut usize,
) {
    let rwlock_family = |mode: CustomLockMode| {
        matches!(
            mode,
            CustomLockMode::RwLockRead | CustomLockMode::RwLockWrite
        )
    };
    for members in groups {
        let rwlock = rwlock_family(sites[members[0]].method.mode);
        let place = add_lock_place(builder, *group_id, rwlock);
        let names: Vec<&str> = members.iter().map(|&i| sites[i].name.as_str()).collect();
        let anchor = &sites[members[0]];
        log::warn!(
            "[custom-lock-group] group{} {:?} = {}",
            *group_id,
            names,
            if rwlock { "RwLock" } else { "Mutex" }
        );
        let _ids = (anchor.def_id, anchor.instance.def_id());
        for &i in members {
            let site = &sites[i];
            resources.custom_locks_mut().insert(
                site.instance_id,
                CustomLockEntry {
                    place,
                    mode: site.method.mode,
                    op: site.method.op,
                },
            );
        }
        *group_id += 1;
    }
}

impl<'analysis, 'tcx> PetriNet<'analysis, 'tcx> {
    // Locks/atomics/unsafe are merged by equivalence class;
    // each condvar local gets its own mailbox (merging would change token counts).
    pub(crate) fn install_condvar_places(
        &mut self,
        condvars: rustc_data_structures::fx::FxHashMap<
            crate::analysis::callgraph::InstanceId,
            crate::analysis::primitives::blocking::CondvarMap<'tcx>,
        >,
    ) {
        if condvars.is_empty() {
            log::debug!("Not Found Condvars In This Crate");
            return;
        }
        let guard_plan = self.options.config.condvar_model.guard_plan();
        for condvar_map in condvars.into_values() {
            for (condvar_id, span) in condvar_map {
                let condvar_name = format!("Condvar:{}", span);
                // With the ordering guard open the
                // mailbox starts empty, so the first wait cannot return
                // without a matching notify. The default `std` plan keeps
                // the historical initial token.
                let condvar_node = self.create_resource_place(
                    condvar_name,
                    guard_plan.initial_mailbox_tokens,
                    1,
                    String::default(),
                );
                if guard_plan.wait_entry_waiting_weight > 0 {
                    let waiting_name = format!("Waiting:{}", span);
                    let waiting_node = self.net.place(
                        PlaceClass::Resource(()),
                        waiting_name,
                        usize::MAX,
                    );
                    self.resources
                        .condvar_waiting_mut()
                        .insert(condvar_node, waiting_node);
                }
                let condvar_alias = condvar_id.get_alias_id();
                self.resources
                    .condvars_mut()
                    .insert(condvar_alias, condvar_node);
            }
        }
    }

    pub(crate) fn construct_atomic_resources_legacy(&mut self) {
        use crate::analysis::callgraph::CallGraphNode;
        let (forward, back) = self.callgraph.instance_maps();
        let instances: Vec<_> = self
            .callgraph
            .graph
            .node_weights()
            .filter_map(|node| match node {
                CallGraphNode::WithBody(instance) => Some(*instance),
                _ => None,
            })
            .collect();
        let mut atomic_collector = crate::analysis::primitives::atomic::AtomicCollector::new(
            self.tcx,
            self.options.crate_name.clone(),
            forward,
            back,
        );
        let atomic_vars =
            atomic_collector.analyze(&self.options, instances, &mut |instance, local| {
                self.alias.borrow().local_built(*instance, local.as_u32())
            });
        if atomic_vars.is_empty() {
            log::warn!("Not Found Atomic Variables In This Crate");
            return;
        }
        for (_, atomic_info) in atomic_vars {
            let alias_id = atomic_info.get_alias_id();
            if let Some(op) = atomic_info.operations.first() {
                self.resources
                    .atomic_orders_mut()
                    .insert(alias_id, op.ordering);
            } else {
                self.resources
                    .atomic_orders_mut()
                    .insert(alias_id, AtomicOrdering::Relaxed);
            }
            let policy = self.options.config.alias_unknown_policy;
            let place_ids: Vec<_> = {
                let mut alias_analysis = self.alias.borrow_mut();
                let mut all_places = Vec::new();
                for (existing, places) in self.resources.atomic_places().iter() {
                    if alias_analysis
                        .alias_atomic(alias_id, *existing)
                        .may_alias(policy)
                    {
                        all_places.extend(places.iter().copied());
                    }
                }
                all_places
            };
            let place_ids: Vec<_> = if place_ids.is_empty() {
                let place_name = format!(
                    "Atomic({},{})",
                    alias_id.instance_id.index(),
                    alias_id.local.index()
                );
                vec![self.create_resource_place(
                    place_name,
                    1,
                    1,
                    atomic_info.span.clone(),
                )]
            } else {
                place_ids
                    .into_iter()
                    .collect::<FxHashSet<_>>()
                    .into_iter()
                    .collect()
            };
            self.resources
                .atomic_places_mut()
                .insert(alias_id, place_ids);
        }
    }
}
