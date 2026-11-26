//! Place registries filled while the net is built. Call recognition lives in
//! `analysis::api_patterns`.

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;

use super::PlaceId;
use crate::analysis::callgraph::InstanceId;
use crate::analysis::memory::ownership::{CustomLockMode, CustomLockOp};
use crate::analysis::memory::pointsto::AliasId;
use crate::analysis::primitives::atomic::AtomicOrdering;

/// One guard-less custom lock method: the resource place its return
/// transition reads (acquire) or writes (release), the weight class, and the
/// direction. Keyed by [`InstanceId`] in [`ResourceRegistry::custom_locks`], so
/// every monomorphized method body gets exactly one edge.
#[derive(Clone, Copy, Debug)]
pub struct CustomLockEntry {
    pub place: PlaceId,
    pub mode: CustomLockMode,
    pub op: CustomLockOp,
}

pub struct ResourceRegistry {
    locks: FxHashMap<AliasId, PlaceId>,
    /// Guard-less custom lock methods (`RawMutex::lock`, `WordLock::unlock`,
    /// user types from `custom_lock_types`) whose body carries the resource
    /// operation itself.
    custom_locks: FxHashMap<InstanceId, CustomLockEntry>,
    condvars: FxHashMap<AliasId, PlaceId>,
    /// Condvar mailbox place → waiter-counter place. Only
    /// populated when the scenario switch opens the ordering guard; the
    /// default `std` model keeps the map empty, so no arcs are added and the
    /// teaching nets stay byte-identical.
    condvar_waiting: FxHashMap<PlaceId, PlaceId>,
    /// Each alias may map to multiple places (after dropping first-match, one pointer may alias several atomics).
    atomic_places: FxHashMap<AliasId, Vec<PlaceId>>,
    atomic_orders: FxHashMap<AliasId, AtomicOrdering>,
    /// Unsafe local → alias-group id. No Petri-net places are created for
    /// unsafe variables; the group id is carried in the merged
    /// `TransitionType::UnsafeAccess` and used by the data-race detector.
    unsafe_groups: FxHashMap<AliasId, u32>,
    /// Boolean predicate places `(false_place, true_place)` keyed by
    /// the `Mutex<bool>` lock resource `PlaceId`.
    bool_predicates: FxHashMap<PlaceId, (PlaceId, PlaceId)>,
}

impl ResourceRegistry {
    pub fn new() -> Self {
        Self {
            locks: FxHashMap::default(),
            custom_locks: FxHashMap::default(),
            condvars: FxHashMap::default(),
            condvar_waiting: FxHashMap::default(),
            atomic_places: FxHashMap::default(),
            atomic_orders: FxHashMap::default(),
            unsafe_groups: FxHashMap::default(),
            bool_predicates: FxHashMap::default(),
        }
    }

    pub fn locks(&self) -> &FxHashMap<AliasId, PlaceId> {
        &self.locks
    }

    pub fn locks_mut(&mut self) -> &mut FxHashMap<AliasId, PlaceId> {
        &mut self.locks
    }

    pub fn custom_locks(&self) -> &FxHashMap<InstanceId, CustomLockEntry> {
        &self.custom_locks
    }

    pub fn custom_locks_mut(&mut self) -> &mut FxHashMap<InstanceId, CustomLockEntry> {
        &mut self.custom_locks
    }

    pub fn condvars(&self) -> &FxHashMap<AliasId, PlaceId> {
        &self.condvars
    }

    pub fn condvars_mut(&mut self) -> &mut FxHashMap<AliasId, PlaceId> {
        &mut self.condvars
    }

    /// Condvar mailbox place → waiter-counter place.
    pub fn condvar_waiting(&self) -> &FxHashMap<PlaceId, PlaceId> {
        &self.condvar_waiting
    }

    pub fn condvar_waiting_mut(&mut self) -> &mut FxHashMap<PlaceId, PlaceId> {
        &mut self.condvar_waiting
    }

    pub fn atomic_places(&self) -> &FxHashMap<AliasId, Vec<PlaceId>> {
        &self.atomic_places
    }

    pub fn atomic_places_mut(&mut self) -> &mut FxHashMap<AliasId, Vec<PlaceId>> {
        &mut self.atomic_places
    }

    pub fn atomic_orders(&self) -> &FxHashMap<AliasId, AtomicOrdering> {
        &self.atomic_orders
    }

    pub fn atomic_orders_mut(&mut self) -> &mut FxHashMap<AliasId, AtomicOrdering> {
        &mut self.atomic_orders
    }

    pub fn unsafe_groups(&self) -> &FxHashMap<AliasId, u32> {
        &self.unsafe_groups
    }

    pub fn unsafe_groups_mut(&mut self) -> &mut FxHashMap<AliasId, u32> {
        &mut self.unsafe_groups
    }

    pub fn bool_predicates(&self) -> &FxHashMap<PlaceId, (PlaceId, PlaceId)> {
        &self.bool_predicates
    }

    pub fn bool_predicates_mut(&mut self) -> &mut FxHashMap<PlaceId, (PlaceId, PlaceId)> {
        &mut self.bool_predicates
    }
}

pub struct FunctionRegistry {
    counter: FxHashMap<DefId, (PlaceId, PlaceId)>,
}

impl FunctionRegistry {
    pub fn new() -> Self {
        Self {
            counter: FxHashMap::default(),
        }
    }

    pub fn contains(&self, def_id: &DefId) -> bool {
        self.counter.contains_key(def_id)
    }

    pub fn insert(&mut self, def_id: DefId, start: PlaceId, end: PlaceId) {
        self.counter.insert(def_id, (start, end));
    }

    pub fn counter(&self) -> &FxHashMap<DefId, (PlaceId, PlaceId)> {
        &self.counter
    }

    pub fn get_or_insert<F>(&mut self, def_id: DefId, create: F) -> (PlaceId, PlaceId)
    where
        F: FnOnce() -> (PlaceId, PlaceId),
    {
        match self.counter.entry(def_id) {
            std::collections::hash_map::Entry::Occupied(existing) => *existing.get(),
            std::collections::hash_map::Entry::Vacant(vacant) => {
                let place_pair = create();
                vacant.insert(place_pair);
                place_pair
            }
        }
    }
}

impl From<AliasId> for unipn::pt::AliasId {
    fn from(a: AliasId) -> Self {
        unipn::pt::AliasId {
            instance_id: a.instance_id.index(),
            local: a.local.as_usize(),
            array_index: a.array_index,
            field: a.field,
        }
    }
}

impl From<AtomicOrdering> for unipn::pt::AtomicOrdering {
    fn from(o: AtomicOrdering) -> Self {
        match o {
            AtomicOrdering::Relaxed => unipn::pt::AtomicOrdering::Relaxed,
            AtomicOrdering::Release => unipn::pt::AtomicOrdering::Release,
            AtomicOrdering::Acquire => unipn::pt::AtomicOrdering::Acquire,
            AtomicOrdering::AcqRel => unipn::pt::AtomicOrdering::AcqRel,
            AtomicOrdering::SeqCst => unipn::pt::AtomicOrdering::SeqCst,
        }
    }
}
