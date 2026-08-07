//! Static P/T net elements: places, transitions, arcs, and markings.
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::fmt;
use std::hash::{Hash, Hasher};

use serde::{Deserialize, Serialize};

use crate::concurrency::atomic::AtomicOrdering;
use crate::memory::pointsto::AliasId;
use crate::net::ids::{PlaceId, TransitionId};
use crate::net::index_vec::IndexVec;
use petgraph::graph::NodeIndex;
use rustc_middle::mir::Local;

pub type Weight = u64;

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize, Hash)]
pub enum PlaceType {
    Resources,
    FunctionStart,
    FunctionEnd,
    BasicBlock,
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq, Hash, Debug)]
pub struct Place {
    pub name: String,
    pub tokens: Weight,
    pub capacity: Weight,
    pub place_type: PlaceType,

    pub span: String,
}

impl Place {
    pub fn new(
        name: impl Into<String>,
        tokens: Weight,
        capacity: Weight,
        place_type: PlaceType,
        span: String,
    ) -> Self {
        Self {
            name: name.into(),
            tokens,
            capacity,
            place_type,
            span,
        }
    }
}
#[derive(Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Transition {
    pub name: String,
    pub transition_type: TransitionType,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum TransitionType {
    Start(usize),
    Goto,
    Switch,
    Return(usize),
    Unlock(usize),
    DropRead(usize),
    DropWrite(usize),
    Drop,
    Assert,

    UnsafeRead(usize, String, usize, String),
    UnsafeWrite(usize, String, usize, String),

    Lock(usize),
    RwLockRead(usize),
    RwLockWrite(usize),
    Notify(usize),
    Wait,

    AtomicLoad(
        #[serde(with = "alias_id_serde")] AliasId,
        #[serde(with = "atomic_ordering_serde")] AtomicOrdering,
        String,
        usize,
    ),
    AtomicStore(
        #[serde(with = "alias_id_serde")] AliasId,
        #[serde(with = "atomic_ordering_serde")] AtomicOrdering,
        String,
        usize,
    ),
    AtomicCmpXchg(
        #[serde(with = "alias_id_serde")] AliasId,
        #[serde(with = "atomic_ordering_serde")] AtomicOrdering,
        #[serde(with = "atomic_ordering_serde")] AtomicOrdering,
        String,
        usize,
    ),
    Spawn(String),
    Join(String),

    Function,
    Normal,
    Inhibitor,
    Reset,
}

impl Transition {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            transition_type: TransitionType::Normal,
        }
    }

    pub fn new_with_transition_type(
        name: impl Into<String>,
        transition_type: TransitionType,
    ) -> Self {
        Self {
            name: name.into(),
            transition_type,
        }
    }
}

impl fmt::Debug for Transition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Transition").field(&self.name).finish()
    }
}

#[derive(Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Arc {
    pub place: PlaceId,
    pub transition: TransitionId,
    pub weight: Weight,
    pub direction: ArcDirection,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum ArcDirection {
    PlaceToTransition,
    TransitionToPlace,
}

impl Arc {
    pub fn new(
        place: PlaceId,
        transition: TransitionId,
        weight: Weight,
        direction: ArcDirection,
    ) -> Self {
        Self {
            place,
            transition,
            weight,
            direction,
        }
    }
}

impl fmt::Debug for Arc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Arc")
            .field("place", &self.place)
            .field("transition", &self.transition)
            .field("weight", &self.weight)
            .field("direction", &self.direction)
            .finish()
    }
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Marking(pub IndexVec<PlaceId, Weight>);

impl Marking {
    pub fn new(initial: IndexVec<PlaceId, Weight>) -> Self {
        Self(initial)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = (PlaceId, &Weight)> {
        self.0.iter_enumerated()
    }

    pub fn tokens(&self, place: PlaceId) -> Weight {
        self.0[place]
    }

    pub fn tokens_mut(&mut self, place: PlaceId) -> &mut Weight {
        &mut self.0[place]
    }

    pub fn into_inner(self) -> IndexVec<PlaceId, Weight> {
        self.0
    }
}

impl Hash for Marking {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for value in self.0.iter() {
            value.hash(state);
        }
    }
}

impl fmt::Debug for Marking {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        for (place, tokens) in self.iter() {
            map.entry(&place, tokens);
        }
        map.finish()
    }
}

impl PartialOrd for Marking {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.len() != other.len() {
            return None;
        }
        let mut less = false;
        let mut greater = false;
        for (idx, left) in self.0.iter_enumerated() {
            let right = other.0[idx];
            if left < &right {
                less = true;
            } else if left > &right {
                greater = true;
            }
        }
        match (less, greater) {
            (true, true) => None,
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            (false, false) => Some(Ordering::Equal),
        }
    }
}

impl Ord for Marking {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
    }
}

impl Marking {
    pub fn hashable_key(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }
}

mod alias_id_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S>(value: &AliasId, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let tuple = (
            value.instance_id.index(),
            value.local.index(),
            value.array_index,
        );
        tuple.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<AliasId, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (instance_idx, local_idx, array_index) =
            <(usize, usize, Option<u64>)>::deserialize(deserializer)?;
        let instance = NodeIndex::new(instance_idx);
        let local = Local::from_usize(local_idx);
        let mut id = AliasId::new(instance, local);
        id.array_index = array_index;
        Ok(id)
    }
}

mod atomic_ordering_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S>(value: &AtomicOrdering, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(match value {
            AtomicOrdering::Relaxed => "Relaxed",
            AtomicOrdering::Release => "Release",
            AtomicOrdering::Acquire => "Acquire",
            AtomicOrdering::AcqRel => "AcqRel",
            AtomicOrdering::SeqCst => "SeqCst",
        })
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<AtomicOrdering, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        match s.as_str() {
            "Relaxed" => Ok(AtomicOrdering::Relaxed),
            "Release" => Ok(AtomicOrdering::Release),
            "Acquire" => Ok(AtomicOrdering::Acquire),
            "AcqRel" => Ok(AtomicOrdering::AcqRel),
            "SeqCst" => Ok(AtomicOrdering::SeqCst),
            other => Err(serde::de::Error::unknown_variant(
                other,
                &["Relaxed", "Release", "Acquire", "AcqRel", "SeqCst"],
            )),
        }
    }
}
