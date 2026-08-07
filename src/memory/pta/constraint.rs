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
    Offset { dst: LocId, src: LocId, suffix: super::loc::FieldPath },
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
        assert!(cs.add(Constraint::Offset { dst: 1, src: 2, suffix: 7 }));
        assert!(!cs.add(Constraint::Offset { dst: 1, src: 2, suffix: 7 }));
        assert!(cs.add(Constraint::Offset { dst: 1, src: 2, suffix: 8 }));
        assert_eq!(cs.len(), 2);
    }
}
