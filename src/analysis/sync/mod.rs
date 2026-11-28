//! One identity for synchronization objects.
//!
//! ```text
//! collect (four site kinds) → partition (one equivalence) → places → ResourceMap
//! ```
//!
//! A site is one collected use of a lock, condition variable, atomic, or unsafe
//! place. Partition puts two sites in the same slot only when
//! the partition predicate says so. Places are created from slots; body lowering still
//! reads the net's resource registry, which is filled from
//! this map and does not group sites itself.
//!
//! Object identity is the alias of the underlying object (for a lock, the
//! acquiring receiver, not the guard). Spans and names are recorded for dumps
//! and are never part of the comparison.

mod collect;
mod extract;
pub mod group_locks;
pub(crate) mod partition;
pub(crate) mod shadow;
mod ty;

pub(crate) use collect::guard_protected_ty;
pub use collect::{CollectStats, collect_sync_sites};
pub(crate) use extract::{Harvest, ResourceInputs, harvest_resources};
pub use partition::same_object;
pub use ty::{TypeKey, type_compatible, type_keys_compatible};

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::Local;
use rustc_middle::ty::Ty;

use crate::analysis::callgraph::InstanceId;
use crate::analysis::memory::ownership::{CustomLockMode, CustomLockOp};
use crate::analysis::memory::pointsto::AliasId;
use crate::analysis::primitives::atomic::AtomicOrdering;
use crate::analysis::primitives::blocking::{CondVarId, LockGuardId};

/// Which synchronization object a site denotes.
///
/// Different kinds never share a slot. `Mutex` and `RwLock` stay apart even
/// when their protected types match.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SiteKind {
    Mutex,
    RwLock,
    Condvar,
    Atomic,
    Unsafe,
}

impl SiteKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Mutex => "mutex",
            Self::RwLock => "rwlock",
            Self::Condvar => "condvar",
            Self::Atomic => "atomic",
            Self::Unsafe => "unsafe",
        }
    }
}

/// What the site does with the object. Role is recorded for dumps. Partition
/// compares kind, type, and alias, not role.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SiteRole {
    Acquire,
    Release,
    Load,
    Store,
    Rmw,
    Access,
}

impl SiteRole {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Acquire => "acquire",
            Self::Release => "release",
            Self::Load => "load",
            Self::Store => "store",
            Self::Rmw => "rmw",
            Self::Access => "access",
        }
    }
}

/// Where a site came from. Body lowering still keys locks by [`LockGuardId`]
/// and atomics by [`AliasId`]; this records that key so a slot can be projected
/// back onto the registry.
#[derive(Clone, Copy, Debug)]
pub enum SiteOrigin {
    Guard(LockGuardId),
    Custom {
        mode: CustomLockMode,
        op: CustomLockOp,
    },
    Condvar(CondVarId),
    Alias(AliasId),
}

impl SiteOrigin {
    pub fn guard(self) -> Option<LockGuardId> {
        match self {
            Self::Guard(id) => Some(id),
            _ => None,
        }
    }

    pub fn custom(self) -> Option<(CustomLockMode, CustomLockOp)> {
        match self {
            Self::Custom { mode, op } => Some((mode, op)),
            _ => None,
        }
    }

    pub fn condvar(self) -> Option<CondVarId> {
        match self {
            Self::Condvar(id) => Some(id),
            _ => None,
        }
    }

    pub fn alias(self) -> Option<AliasId> {
        match self {
            Self::Alias(id) => Some(id),
            Self::Guard(id) => Some(AliasId::from(id)),
            Self::Condvar(id) => Some(AliasId::from(id)),
            Self::Custom { .. } => None,
        }
    }
}

/// One collected synchronization site.
///
/// `local` is the MIR local the collector saw (the guard, the endpoint, the
/// atomic, …). `object` is the alias id partition compares. For a lock guard
/// that is the acquiring receiver when one was resolved, otherwise the guard
/// itself.
#[derive(Clone, Debug)]
pub struct SyncSite<'tcx> {
    pub instance: InstanceId,
    pub local: Local,
    pub kind: SiteKind,
    pub ty: Ty<'tcx>,
    pub role: SiteRole,
    pub span: String,
    pub(crate) object: AliasId,
    pub(crate) origin: SiteOrigin,
    pub(crate) atomic_order: Option<AtomicOrdering>,
}

/// Identity of one site inside [`ResourceMap`]. Role is part of the key so two
/// uses of one local stay distinct when their roles differ.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SiteKey {
    pub instance: InstanceId,
    pub local: u32,
    pub field: u32,
    pub kind: SiteKind,
    pub role: SiteRole,
}

impl<'tcx> SyncSite<'tcx> {
    pub fn atomic_order(&self) -> Option<AtomicOrdering> {
        self.atomic_order
    }

    pub fn key(&self) -> SiteKey {
        let field = match self.origin {
            SiteOrigin::Guard(guard) => guard.field.unwrap_or(u32::MAX),
            _ => self.object.field.unwrap_or(u32::MAX),
        };
        SiteKey {
            instance: self.instance,
            local: self.local.as_u32(),
            field,
            kind: self.kind,
            role: self.role,
        }
    }
}

/// Equivalence-class index. `0..slot_count` in partition order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SlotId(pub u32);

/// Site → slot. The Petri-net place for a slot lives in `translate`, not here.
#[derive(Clone, Debug, Default)]
pub struct ResourceMap {
    site_to_slot: FxHashMap<SiteKey, SlotId>,
    slots: usize,
}

impl ResourceMap {
    pub fn from_assignment(slots: usize, assignment: FxHashMap<SiteKey, SlotId>) -> Self {
        Self {
            site_to_slot: assignment,
            slots,
        }
    }

    pub fn slot_of(&self, site: &SyncSite<'_>) -> Option<SlotId> {
        self.site_to_slot.get(&site.key()).copied()
    }

    pub fn slot_count(&self) -> usize {
        self.slots
    }
}
