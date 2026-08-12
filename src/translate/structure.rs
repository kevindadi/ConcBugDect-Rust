use regex::Regex;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;

use crate::concurrency::atomic::AtomicOrdering;
use crate::config::PnConfig;
use crate::memory::pointsto::AliasId;
use unipn::PlaceId;

/// Token capacity of an `RwLock` resource place. A read lock consumes one
/// token (so up to `RWLOCK_CAPACITY` concurrent readers); a write lock is
/// exclusive and must consume *all* tokens.
pub const RWLOCK_CAPACITY: usize = 10;

pub struct ResourceRegistry {
    locks: FxHashMap<AliasId, PlaceId>,
    condvars: FxHashMap<AliasId, PlaceId>,
    /// Each alias may map to multiple places (after dropping first-match, one pointer may alias several atomics).
    atomic_places: FxHashMap<AliasId, Vec<PlaceId>>,
    atomic_orders: FxHashMap<AliasId, AtomicOrdering>,
    /// Unsafe local → alias-group id. No Petri-net places are created for
    /// unsafe variables; the group id is carried in the merged
    /// `TransitionType::UnsafeAccess` and used by the data-race detector.
    unsafe_groups: FxHashMap<AliasId, u32>,
    channel_places: FxHashMap<AliasId, PlaceId>,
}

impl ResourceRegistry {
    pub fn new() -> Self {
        Self {
            locks: FxHashMap::default(),
            condvars: FxHashMap::default(),
            atomic_places: FxHashMap::default(),
            atomic_orders: FxHashMap::default(),
            unsafe_groups: FxHashMap::default(),
            channel_places: FxHashMap::default(),
        }
    }

    pub fn locks(&self) -> &FxHashMap<AliasId, PlaceId> {
        &self.locks
    }

    pub fn locks_mut(&mut self) -> &mut FxHashMap<AliasId, PlaceId> {
        &mut self.locks
    }

    pub fn condvars(&self) -> &FxHashMap<AliasId, PlaceId> {
        &self.condvars
    }

    pub fn condvars_mut(&mut self) -> &mut FxHashMap<AliasId, PlaceId> {
        &mut self.condvars
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

    pub fn channel_places(&self) -> &FxHashMap<AliasId, PlaceId> {
        &self.channel_places
    }

    pub fn channel_places_mut(&mut self) -> &mut FxHashMap<AliasId, PlaceId> {
        &mut self.channel_places
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

pub struct KeyApiRegex {
    pub thread_spawn: Regex,
    pub thread_join: Regex,
    pub scope_spwan: Regex,
    pub scope_join: Regex,
    pub condvar_notify: Regex,
    pub condvar_wait: Regex,

    pub channel_send: Regex,
    pub channel_recv: Regex,

    pub atomic_load: Regex,
    pub atomic_store: Regex,
}

impl KeyApiRegex {
    pub fn new(config: &PnConfig) -> Self {
        let make_regex = |patterns: &[String]| -> Regex {
            if patterns.is_empty() {
                Regex::new("^$").unwrap() // Match nothing
            } else {
                let combined = patterns.join("|");
                Regex::new(&combined).expect(&format!("Invalid regex in config: {}", combined))
            }
        };

        Self {
            thread_spawn: make_regex(&config.thread_spawn),
            thread_join: make_regex(&config.thread_join),
            scope_spwan: make_regex(&config.scope_spawn),
            scope_join: make_regex(&config.scope_join),
            condvar_notify: make_regex(&config.condvar_notify),
            condvar_wait: make_regex(&config.condvar_wait),
            channel_send: make_regex(&config.channel_send),
            channel_recv: make_regex(&config.channel_recv),
            atomic_load: make_regex(&config.atomic_load),
            atomic_store: make_regex(&config.atomic_store),
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
