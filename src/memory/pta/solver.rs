use std::collections::VecDeque;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use super::constraint::{Constraint, ConstraintSet};
use super::loc::{FieldPath, LocArena, LocId};

/// Solved points-to relation: `LocId` -> set of pointee `LocId`s.
#[derive(Default)]
pub struct PointsTo {
    map: FxHashMap<LocId, FxHashSet<LocId>>,
}

impl PointsTo {
    pub fn points_to(&self, n: LocId) -> &FxHashSet<LocId> {
        static EMPTY: once_cell::sync::Lazy<FxHashSet<LocId>> =
            once_cell::sync::Lazy::new(FxHashSet::default);
        self.map.get(&n).unwrap_or(&EMPTY)
    }

    pub fn raw(&self) -> &FxHashMap<LocId, FxHashSet<LocId>> {
        &self.map
    }

    fn insert(&mut self, n: LocId, o: LocId) -> bool {
        self.map.entry(n).or_default().insert(o)
    }
}

/// Standard Andersen inclusion-based worklist solver.
pub struct Solver {
    loc_count: usize,
}

impl Solver {
    pub fn new(loc_count: usize) -> Self {
        Self { loc_count }
    }

    pub fn solve(&self, constraints: &ConstraintSet, arena: &mut LocArena) -> PointsTo {
        let mut pts = PointsTo::default();

        // copy edge `src -> {dst}` meaning `dst ⊇ src`.
        let mut copy_succ: FxHashMap<LocId, FxHashSet<LocId>> = FxHashMap::default();
        // `dst ⊇ *src` keyed by src.
        let mut loads: FxHashMap<LocId, FxHashSet<LocId>> = FxHashMap::default();
        // `*dst ⊇ src` keyed by dst.
        let mut stores: FxHashMap<LocId, FxHashSet<LocId>> = FxHashMap::default();
        // `dst ⊇ { o·suffix : o ∈ pts(src) }` keyed by src.
        let mut offsets: FxHashMap<LocId, FxHashSet<(LocId, FieldPath)>> = FxHashMap::default();

        let mut worklist: VecDeque<LocId> = VecDeque::new();
        let mut in_wl: FxHashSet<LocId> = FxHashSet::default();

        for c in constraints.iter() {
            match *c {
                Constraint::AddressOf { dst, obj } => {
                    if pts.insert(dst, obj) && in_wl.insert(dst) {
                        worklist.push_back(dst);
                    }
                }
                Constraint::Copy { dst, src } => {
                    copy_succ.entry(src).or_default().insert(dst);
                    if in_wl.insert(src) {
                        worklist.push_back(src);
                    }
                }
                Constraint::Load { dst, src } => {
                    loads.entry(src).or_default().insert(dst);
                    if in_wl.insert(src) {
                        worklist.push_back(src);
                    }
                }
                Constraint::Store { dst, src } => {
                    stores.entry(dst).or_default().insert(src);
                    if in_wl.insert(dst) {
                        worklist.push_back(dst);
                    }
                }
                Constraint::Offset { dst, src, suffix } => {
                    offsets.entry(src).or_default().insert((dst, suffix));
                    if in_wl.insert(src) {
                        worklist.push_back(src);
                    }
                }
            }
        }

        while let Some(n) = worklist.pop_front() {
            in_wl.remove(&n);
            let pointees: Vec<LocId> = pts.points_to(n).iter().copied().collect();

            // Copy edges: for each `dst ⊇ n`, propagate pts(n) into pts(dst).
            if let Some(succs) = copy_succ.get(&n) {
                let succs: Vec<LocId> = succs.iter().copied().collect();
                for dst in succs {
                    let mut changed = false;
                    for &o in &pointees {
                        changed |= pts.insert(dst, o);
                    }
                    if changed && in_wl.insert(dst) {
                        worklist.push_back(dst);
                    }
                }
            }

            // Load `dst ⊇ *n`: for each o in pts(n), add copy edge `o -> dst`.
            if let Some(dsts) = loads.get(&n) {
                let dsts: Vec<LocId> = dsts.iter().copied().collect();
                for dst in dsts {
                    for &o in &pointees {
                        if copy_succ.entry(o).or_default().insert(dst) && in_wl.insert(o) {
                            worklist.push_back(o);
                        }
                    }
                }
            }

            // Store `*n ⊇ src`: for each o in pts(n), add copy edge `src -> o`.
            if let Some(srcs) = stores.get(&n) {
                let srcs: Vec<LocId> = srcs.iter().copied().collect();
                for src in srcs {
                    for &o in &pointees {
                        if copy_succ.entry(src).or_default().insert(o) && in_wl.insert(src) {
                            worklist.push_back(src);
                        }
                    }
                }
            }

            // Offset `dst ⊇ { o·suffix : o ∈ pts(n) }`.
            if let Some(targets) = offsets.get(&n) {
                let targets: Vec<(LocId, FieldPath)> = targets.iter().copied().collect();
                for (dst, suffix) in targets {
                    let mut changed = false;
                    for &o in &pointees {
                        if let Some(proj) = arena.project(o, suffix) {
                            changed |= pts.insert(dst, proj);
                        }
                    }
                    if changed && in_wl.insert(dst) {
                        worklist.push_back(dst);
                    }
                }
            }
        }

        let _ = self.loc_count;
        pts
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory::pta::constraint::{Constraint, ConstraintSet};

    #[test]
    fn copy_propagates_points_to() {
        let mut arena = crate::memory::pta::loc::LocArena::default();
        let (p, q, a) = (0u32, 1u32, 2u32);
        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf { dst: p, obj: a });
        cs.add(Constraint::Copy { dst: q, src: p });
        let pts = Solver::new(3).solve(&cs, &mut arena);
        assert!(pts.points_to(q).contains(&a));
    }

    #[test]
    fn load_store_through_pointer() {
        let mut arena = crate::memory::pta::loc::LocArena::default();
        let (p, r, a, b) = (0u32, 1u32, 2u32, 3u32);
        let tb = 4u32;
        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf { dst: p, obj: a });
        cs.add(Constraint::AddressOf { dst: tb, obj: b });
        cs.add(Constraint::Store { dst: p, src: tb });
        cs.add(Constraint::Load { dst: r, src: p });
        let pts = Solver::new(5).solve(&cs, &mut arena);
        assert!(pts.points_to(a).contains(&b));
        assert!(pts.points_to(r).contains(&b));
    }

    #[test]
    fn offset_projects_pointees_field_sensitively() {
        use crate::memory::pta::loc::{AllocSite, LocArena, ProjElem};
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let f0 = arena.extend_path(empty, ProjElem::Field(0));

        let o = arena.heap(AllocSite { func: 0, bb: 0, idx: 0 }, empty);
        let p = arena.var(0, 1, empty);
        let q = arena.var(0, 2, empty);
        let o_f0 = arena.heap(AllocSite { func: 0, bb: 0, idx: 0 }, f0);

        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf { dst: p, obj: o });
        cs.add(Constraint::Offset { dst: q, src: p, suffix: f0 });

        let pts = Solver::new(0).solve(&cs, &mut arena);
        assert!(pts.points_to(q).contains(&o_f0));
    }

    #[test]
    fn offset_after_load_models_field_through_deref() {
        use crate::memory::pta::loc::{AllocSite, LocArena, ProjElem};
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let f0 = arena.extend_path(empty, ProjElem::Field(0));

        let o = arena.heap(AllocSite { func: 0, bb: 9, idx: 0 }, empty);
        let self_slot = arena.var(0, 1, empty); // V_self
        let addr_self = arena.var(0, 100, empty); // &self (pts = {V_self})
        let derefed = arena.var(0, 101, empty); // *self (pts = pts(V_self) = {O})
        let field = arena.var(0, 102, empty); // &(*self).f0
        let o_f0 = arena.heap(AllocSite { func: 0, bb: 9, idx: 0 }, f0);

        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf { dst: self_slot, obj: o });
        cs.add(Constraint::AddressOf { dst: addr_self, obj: self_slot });
        cs.add(Constraint::Load { dst: derefed, src: addr_self });
        cs.add(Constraint::Offset { dst: field, src: derefed, suffix: f0 });

        let pts = Solver::new(0).solve(&cs, &mut arena);
        assert!(pts.points_to(field).contains(&o_f0));
    }
}
