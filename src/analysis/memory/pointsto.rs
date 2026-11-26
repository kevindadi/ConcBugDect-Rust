extern crate rustc_hir;
extern crate rustc_index;

use std::cmp::{Ordering, PartialOrd};
use std::sync::{Mutex, OnceLock};

use petgraph::graph::NodeIndex;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::{Local, PlaceRef, ProjectionElem};

use crate::analysis::primitives::blocking::{CondVarId, LockGuardId};

/// Call-graph node index. Defined with the alias facts so collectors do not
/// depend on the analysis layer that owns the graph.
pub type InstanceId = NodeIndex;

/// One element of a receiver's full MIR projection path. Mirrors the engine's
/// [`crate::analysis::memory::pta::loc::ProjElem`] but lives here because [`AliasId`] is
/// shared by the legacy query surface and the collector (which do not depend on
/// the pointer-analysis module). `Downcast` projections are not represented: variant tags are
/// merged everywhere (see `pta::builder::proj_kinds`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PathStep {
    Deref,
    Field(u32),
    Index,
    ConstIndex(u64),
}

/// Interned id of a [`PathStep`] sequence. Interning makes the id a canonical
/// representative of the exact path, so `AliasId` can stay `Copy` while its
/// equality still distinguishes full projection paths (not just the first
/// field).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PathId(u32);

struct PathInterner {
    ids: FxHashMap<Vec<PathStep>, u32>,
    paths: Vec<Vec<PathStep>>,
}

fn path_interner() -> &'static Mutex<PathInterner> {
    static INTERNER: OnceLock<Mutex<PathInterner>> = OnceLock::new();
    INTERNER.get_or_init(|| {
        Mutex::new(PathInterner {
            ids: FxHashMap::default(),
            paths: Vec::new(),
        })
    })
}

/// Intern a receiver path. Empty paths get `None` (no projection) to keep the
/// additive field mean exactly "full path when there is one".
pub fn intern_path(steps: impl AsRef<[PathStep]>) -> Option<PathId> {
    let steps = steps.as_ref();
    if steps.is_empty() {
        return None;
    }
    let mut guard = path_interner().lock().unwrap_or_else(|e| e.into_inner());
    if let Some(&id) = guard.ids.get(steps) {
        return Some(PathId(id));
    }
    let id = guard.paths.len() as u32;
    guard.paths.push(steps.to_vec());
    guard.ids.insert(steps.to_vec(), id);
    Some(PathId(id))
}

impl PathId {
    /// The interned steps. Returns an owned vector so callers do not hold the
    /// interner lock while querying the engine.
    pub fn steps(self) -> Vec<PathStep> {
        let guard = path_interner().lock().unwrap_or_else(|e| e.into_inner());
        guard.paths[self.0 as usize].clone()
    }

    /// True when the path is a plain field chain (`Field` only). Such paths
    /// denote disjoint projections of the same base object, so differing paths
    /// can be reported as non-aliasing (the legacy first-field rule).
    pub fn is_field_chain(self) -> bool {
        let steps = self.steps();
        steps.iter().all(|s| matches!(s, PathStep::Field(_)))
    }
}

impl std::fmt::Debug for PathId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let steps = path_interner()
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .paths
            .get(self.0 as usize)
            .cloned()
            .unwrap_or_default();
        write!(f, "{:?}", steps)
    }
}

/// Convert a MIR projection into a full receiver path. `Downcast` is skipped
/// (variant tags are merged), `ConstantIndex` keeps its value, and every other
/// dynamic element is merged into `Index`.
pub fn projection_path<'tcx, P>(projection: impl IntoIterator<Item = P>) -> Vec<PathStep>
where
    P: std::borrow::Borrow<ProjectionElem<Local, rustc_middle::ty::Ty<'tcx>>>,
{
    projection
        .into_iter()
        .filter_map(|elem| match elem.borrow() {
            ProjectionElem::Downcast(..) => None,
            ProjectionElem::Deref => Some(PathStep::Deref),
            ProjectionElem::Field(f, _) => Some(PathStep::Field(f.as_u32())),
            ProjectionElem::ConstantIndex { offset, .. } => Some(PathStep::ConstIndex(*offset)),
            _ => Some(PathStep::Index),
        })
        .collect()
}

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
    ///
    /// Kept for compatibility with consumers that only know the first field;
    /// [`Self::receiver_path`] supersedes it whenever the full path is known.
    pub field: Option<u32>,
    /// Full projection path of the place this id denotes, when known. Additive:
    /// older ids (and ids built from a single field) leave it `None` and keep
    /// behaving exactly as before. Lock/condvar/atomic grouping uses the full
    /// path so `(*p).a.b` and `(*p).a.c` stay distinct instead of comparing
    /// only the first `Field`.
    pub receiver_path: Option<PathId>,
}

impl AliasId {
    pub fn new(instance_id: InstanceId, local: Local) -> Self {
        Self {
            instance_id,
            local,
            array_index: None,
            field: None,
            receiver_path: None,
        }
    }

    /// Build from `Place`, extracting constant indices to distinguish `arr[0]` vs `arr[1]`,
    /// the first field index (legacy consumers), and the full projection path.
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
        let receiver_path = intern_path(projection_path(place.projection.iter()));
        Self {
            instance_id,
            local: place.local,
            array_index,
            field,
            receiver_path,
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
            receiver_path: None,
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
            receiver_path: None,
        }
    }
}
