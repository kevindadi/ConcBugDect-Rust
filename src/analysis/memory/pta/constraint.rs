use super::loc::LocId;
use rustc_data_structures::fx::FxHashSet;

/// Inclusion (Andersen) constraints over interned location ids.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Constraint {
    /// `dst ⊇ { obj }`
    AddressOf { dst: LocId, obj: LocId },
    /// `dst ⊇ src`
    Copy { dst: LocId, src: LocId },
    /// `dst ⊇ *src`
    Load { dst: LocId, src: LocId },
    /// `*dst ⊇ src`
    Store { dst: LocId, src: LocId },
    /// Field projection (GEP): `dst ⊇ { o·suffix : o ∈ pts(src) }`, where
    /// `suffix` is an interned `FieldPath` of Field/Index elems only.
    Offset {
        dst: LocId,
        src: LocId,
        suffix: super::loc::FieldPath,
    },
    /// Scalar constant lattice seed : the value stored at `dst` is
    /// `Some(v)` (a proven `u64`/`usize` constant) or `None` (explicitly
    /// unknown, e.g. a call result). Seen as a lattice *join*: a location that
    /// receives both a constant and an unknown write is unknown.
    Const { dst: LocId, value: Option<u64> },
    /// Predicate-split element load.
    ///
    /// Semantically [`Constraint::Load`] with a predicate certificate: let
    /// `E = ⋃ { pts(o) : o ∈ pts(src) }` be the merged element set the
    /// corresponding `Load` would read. If the captured predicate value
    /// evaluates to `v`, then `dst ⊇ { tag(e, field, v) : e ∈ E }` (the
    /// matching-element branch); otherwise it behaves exactly like
    /// [`Constraint::Load`] (`dst ⊇ E`, merged element, sound).
    ///
    /// `src` is the same node the merged `Load` reads (a pointer to the
    /// iterator's element-reference slot), `field` is the predicate field path
    /// relative to the element, and `value` is the closure's captured scalar
    /// value.
    FindElement {
        dst: LocId,
        src: LocId,
        field: super::loc::FieldPath,
        value: FindValue,
    },
}

/// The right-hand side of a `find` predicate (`element.field == value`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum FindValue {
    /// A literal constant comparison (`x.id == 0`).
    Literal(u64),
    /// A value node whose scalar constant the solver evaluates (a captured
    /// upvar, directly by value or behind one reference).
    Node(LocId),
}

/// A deduplicated set of constraints.
#[derive(Clone, Default)]
pub struct ConstraintSet {
    set: FxHashSet<Constraint>,
}

impl ConstraintSet {
    /// Returns `true` if the constraint was newly inserted.
    pub fn add(&mut self, c: Constraint) -> bool {
        self.set.insert(c)
    }

    pub fn len(&self) -> usize {
        self.set.len()
    }

    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Constraint> {
        self.set.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dedups_constraints() {
        let mut cs = ConstraintSet::default();
        assert!(cs.add(Constraint::Copy { dst: 1, src: 2 }));
        assert!(!cs.add(Constraint::Copy { dst: 1, src: 2 }));
        assert!(cs.add(Constraint::AddressOf { dst: 1, obj: 9 }));
        assert_eq!(cs.len(), 2);
    }

    #[test]
    fn offset_constraint_is_distinct_and_dedups() {
        let mut cs = ConstraintSet::default();
        assert!(cs.add(Constraint::Offset {
            dst: 1,
            src: 2,
            suffix: 7
        }));
        assert!(!cs.add(Constraint::Offset {
            dst: 1,
            src: 2,
            suffix: 7
        }));
        assert!(cs.add(Constraint::Offset {
            dst: 1,
            src: 2,
            suffix: 8
        }));
        assert_eq!(cs.len(), 2);
    }
}
