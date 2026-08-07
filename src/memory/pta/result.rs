use rustc_data_structures::fx::FxHashSet;

use super::loc::LocId;
use super::solver::PointsTo;

/// Read-only query facade over a solved points-to relation.
///
/// Client-query extension point: add `mod_ref`, alias-set, value-flow queries
/// here without touching the solver.
pub struct PointsToResult {
    pts: PointsTo,
}

impl PointsToResult {
    pub fn new(pts: PointsTo) -> Self {
        Self { pts }
    }

    pub fn points_to(&self, n: LocId) -> &FxHashSet<LocId> {
        self.pts.points_to(n)
    }

    /// Two nodes may alias if their points-to sets intersect.
    pub fn may_alias(&self, a: LocId, b: LocId) -> bool {
        let pa = self.pts.points_to(a);
        let pb = self.pts.points_to(b);
        !pa.is_disjoint(pb)
    }

    pub fn raw(&self) -> &PointsTo {
        &self.pts
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory::pta::constraint::{Constraint, ConstraintSet};
    use crate::memory::pta::solver::Solver;

    #[test]
    fn may_alias_via_shared_pointee() {
        let (p, q, a) = (0u32, 1u32, 2u32);
        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf { dst: p, obj: a });
        cs.add(Constraint::AddressOf { dst: q, obj: a });
        let mut arena = crate::memory::pta::loc::LocArena::default();
        let pts = Solver::new(3).solve(&cs, &mut arena);
        let r = PointsToResult::new(pts);
        assert!(r.may_alias(p, q));
    }

    #[test]
    fn distinct_pointees_do_not_alias() {
        let (p, q, a, b) = (0u32, 1u32, 2u32, 3u32);
        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf { dst: p, obj: a });
        cs.add(Constraint::AddressOf { dst: q, obj: b });
        let mut arena = crate::memory::pta::loc::LocArena::default();
        let pts = Solver::new(4).solve(&cs, &mut arena);
        let r = PointsToResult::new(pts);
        assert!(!r.may_alias(p, q));
    }
}
