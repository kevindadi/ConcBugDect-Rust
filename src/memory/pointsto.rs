extern crate rustc_hir;
extern crate rustc_index;

use std::cmp::{Ordering, PartialOrd};

use rustc_middle::mir::{Local, PlaceRef, ProjectionElem};

use crate::concurrency::blocking::{CondVarId, LockGuardId};
use crate::concurrency::channel::ChannelId;
use crate::translate::callgraph::InstanceId;

/// Approximate likelihood that two locations alias. The Petri-net translation
/// maps these to arc additions via [`ApproximateAliasKind::may_alias`] under the
/// configured Unknown policy.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ApproximateAliasKind {
    Probably,
    Possibly,
    Unlikely,
    Unknown,
}

impl PartialOrd for ApproximateAliasKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use ApproximateAliasKind::*;
        match (*self, *other) {
            (Probably, Probably)
            | (Possibly, Possibly)
            | (Unlikely, Unlikely)
            | (Unknown, Unknown) => Some(Ordering::Equal),
            (Probably, _) | (Possibly, Unlikely) | (Possibly, Unknown) | (Unlikely, Unknown) => {
                Some(Ordering::Greater)
            }
            (_, Probably) | (Unlikely, Possibly) | (Unknown, Possibly) | (Unknown, Unlikely) => {
                Some(Ordering::Less)
            }
        }
    }
}

impl ApproximateAliasKind {
    /// Whether this alias should add arcs under the configured Unknown policy (treat as possible alias).
    pub fn may_alias(self, policy: crate::config::AliasUnknownPolicy) -> bool {
        use crate::config::AliasUnknownPolicy;
        match self {
            ApproximateAliasKind::Probably | ApproximateAliasKind::Possibly => true,
            ApproximateAliasKind::Unlikely => false,
            ApproximateAliasKind::Unknown => matches!(policy, AliasUnknownPolicy::Conservative),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AliasId {
    pub instance_id: InstanceId,
    pub local: Local,
    /// Constant index distinguishes `arr[0]` vs `arr[1]`; dynamic index or non-array ⇒ `None` (merged).
    pub array_index: Option<u64>,
    /// For field accesses (like self.mu), this stores the field index to distinguish
    /// different fields of the same struct. None means no field projection.
    pub field: Option<u32>,
}

impl AliasId {
    pub fn new(instance_id: InstanceId, local: Local) -> Self {
        Self {
            instance_id,
            local,
            array_index: None,
            field: None,
        }
    }

    /// Build from `Place`, extracting constant indices to distinguish `arr[0]` vs `arr[1]`
    /// and field index to distinguish `self.mu` vs `self.rw1`.
    pub fn from_place<'tcx>(instance_id: InstanceId, place: PlaceRef<'tcx>) -> Self {
        let array_index = if place
            .projection
            .iter()
            .any(|e| matches!(e, ProjectionElem::Index(_)))
        {
            None
        } else {
            place.projection.iter().rev().find_map(|elem| {
                if let ProjectionElem::ConstantIndex { offset, .. } = elem {
                    Some(*offset)
                } else {
                    None
                }
            })
        };
        // Extract the first Field projection to distinguish different fields
        let field = place.projection.iter().find_map(|elem| {
            if let ProjectionElem::Field(f, _) = elem {
                Some(f.as_u32())
            } else {
                None
            }
        });
        Self {
            instance_id,
            local: place.local,
            array_index,
            field,
        }
    }
}

impl std::convert::From<LockGuardId> for AliasId {
    fn from(lockguard_id: LockGuardId) -> Self {
        Self {
            instance_id: lockguard_id.instance_id,
            local: lockguard_id.local,
            array_index: None,
            field: lockguard_id.field,
        }
    }
}

impl std::convert::From<CondVarId> for AliasId {
    fn from(condvar_id: CondVarId) -> Self {
        Self {
            instance_id: condvar_id.instance_id,
            local: condvar_id.local,
            array_index: None,
            field: None,
        }
    }
}

impl std::convert::From<ChannelId> for AliasId {
    fn from(channel_id: ChannelId) -> Self {
        Self {
            instance_id: channel_id.instance_id,
            local: channel_id.local,
            array_index: None,
            field: None,
        }
    }
}
