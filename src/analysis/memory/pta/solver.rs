use std::collections::VecDeque;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use super::constraint::{Constraint, ConstraintSet, FindValue};
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

/// Two-level scalar constant lattice: a location may hold a single proven
/// `u64`/`usize` constant or an explicitly unknown scalar. Absent from the
/// map means "no scalar information" (e.g. a reference value), which the
/// predicate query reads through one level of pointees.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ConstVal {
    Unknown,
    Known(u64),
}

/// Solved scalar constant lattice: `LocId` -> constant/unknown.
#[derive(Default, Clone)]
pub struct ConstMap {
    map: FxHashMap<LocId, ConstVal>,
}

impl ConstMap {
    pub fn get(&self, n: LocId) -> Option<ConstVal> {
        self.map.get(&n).copied()
    }

    /// The proven constant of `n`, if any.
    pub fn known(&self, n: LocId) -> Option<u64> {
        match self.map.get(&n) {
            Some(ConstVal::Known(v)) => Some(*v),
            _ => None,
        }
    }

    pub fn is_unknown(&self, n: LocId) -> bool {
        matches!(self.map.get(&n), Some(ConstVal::Unknown))
    }

    /// Lattice join. Returns whether the value changed.
    fn join(&mut self, n: LocId, v: ConstVal) -> bool {
        match self.map.get(&n).copied() {
            None => {
                self.map.insert(n, v);
                true
            }
            Some(ConstVal::Unknown) => false,
            Some(ConstVal::Known(old)) => match v {
                ConstVal::Known(new) if new == old => false,
                _ => {
                    self.map.insert(n, ConstVal::Unknown);
                    true
                }
            },
        }
    }

    /// Evaluate the scalar at `n` for the `find` predicate.
    ///
    /// A direct lattice entry wins: `Known(v)` evaluates, `Unknown` does not
    /// (never read through a scalar that is already known to be dynamic).
    /// An absent entry is the non-scalar case (typically a captured reference
    /// such as `&id`): read one level through its pointees and require every
    /// pointee to carry the same proven constant. Any unseeded/unknown pointee
    /// makes the predicate unevaluable, which keeps the merged element
    /// (sound).
    pub fn value_of(&self, pts: &PointsTo, n: LocId) -> Option<u64> {
        match self.map.get(&n) {
            Some(ConstVal::Known(v)) => Some(*v),
            Some(ConstVal::Unknown) => None,
            None => {
                let mut joined: Option<u64> = None;
                for &o in pts.points_to(n) {
                    match self.map.get(&o) {
                        Some(ConstVal::Known(v)) => match joined {
                            None => joined = Some(*v),
                            Some(prev) if prev == *v => {}
                            Some(_) => return None,
                        },
                        // An unseeded pointee carries no scalar proof, and an
                        // explicit unknown pointee is dynamic: both make the
                        // captured value unevaluable.
                        _ => return None,
                    }
                }
                joined
            }
        }
    }
}

/// Full solver result: inclusion points-to plus the scalar constant lattice.
pub struct Solution {
    pub points_to: PointsTo,
    pub constants: ConstMap,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// `FindElement` behaves like a plain `Load` (merged element). Used for
    /// the conservative first pass the constants are computed on.
    Conservative,
    /// `FindElement` is split using the already-computed constants.
    Resolved,
}

/// Standard Andersen inclusion-based worklist solver.
pub struct Solver {
    loc_count: usize,
}

impl Solver {
    pub fn new(loc_count: usize) -> Self {
        Self { loc_count }
    }

    /// Solve points-to only (constants/predicate split included).
    pub fn solve(&self, constraints: &ConstraintSet, arena: &mut LocArena) -> PointsTo {
        self.solve_full(constraints, arena).points_to
    }

    /// Solve points-to and the scalar constant lattice.
    ///
    /// Three monotone passes:
    /// 1. conservative points-to, where every `FindElement` behaves like
    ///    `Load` (merged element);
    /// 2. the scalar constant lattice over that points-to. It is computed on
    ///    the merged solution, so predicate evaluation can only be more
    ///    conservative than the final answer (tagging renames elements and
    ///    can drop constants, never add new ones);
    /// 3. the final points-to with each `FindElement` resolved from the
    ///    fixed constants: a proven constant tags the element with the
    ///    predicate identity, an unevaluable one keeps the merged `Load`.
    pub fn solve_full(&self, constraints: &ConstraintSet, arena: &mut LocArena) -> Solution {
        let conservative = self.solve_mode(constraints, arena, Mode::Conservative, None);
        let constants = self.solve_constants(constraints, &conservative);
        let points_to = self.solve_mode(constraints, arena, Mode::Resolved, Some(&constants));
        Solution {
            points_to,
            constants,
        }
    }

    fn solve_mode(
        &self,
        constraints: &ConstraintSet,
        arena: &mut LocArena,
        mode: Mode,
        constants: Option<&ConstMap>,
    ) -> PointsTo {
        let mut pts = PointsTo::default();

        // copy edge `src -> {dst}` meaning `dst ⊇ src`.
        let mut copy_succ: FxHashMap<LocId, FxHashSet<LocId>> = FxHashMap::default();
        // `dst ⊇ *src` keyed by src.
        let mut loads: FxHashMap<LocId, FxHashSet<LocId>> = FxHashMap::default();
        // `*dst ⊇ src` keyed by dst.
        let mut stores: FxHashMap<LocId, FxHashSet<LocId>> = FxHashMap::default();
        // `dst ⊇ { o·suffix : o ∈ pts(src) }` keyed by src.
        let mut offsets: FxHashMap<LocId, FxHashSet<(LocId, FieldPath)>> = FxHashMap::default();
        // Predicate-split element loads keyed by src (resolved mode only).
        // Processed in two steps so late growth of the element sets is not
        // lost: `finds` maps `src` to the (dst, field, value) triples; when
        // `src` is processed each pointee `o ∈ pts(src)` gets a dependency
        // edge in `find_succ`, and when `o` is processed its own pointees are
        // tagged into `dst`. Without the second map, an element discovered
        // after `src` was first processed would never be tagged.
        let mut finds: FxHashMap<LocId, Vec<(LocId, FieldPath, FindValue)>> = FxHashMap::default();
        let mut find_succ: FxHashMap<LocId, Vec<(LocId, FieldPath, FindValue)>> =
            FxHashMap::default();

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
                Constraint::FindElement {
                    dst,
                    src,
                    field,
                    value,
                } => match mode {
                    Mode::Conservative => {
                        // Merged element: exactly like `dst ⊇ *src`.
                        loads.entry(src).or_default().insert(dst);
                        if in_wl.insert(src) {
                            worklist.push_back(src);
                        }
                    }
                    Mode::Resolved => {
                        finds.entry(src).or_default().push((dst, field, value));
                        if in_wl.insert(src) {
                            worklist.push_back(src);
                        }
                    }
                },
                // Scalar seeds do not constrain the points-to relation.
                Constraint::Const { .. } => {}
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

            // Predicate split, step 1: register a dependency edge from each
            // pointee of `src` (the element container slot) to the find entry.
            // Step 2 (below) tags that pointee's elements when it is visited.
            if let Some(entries) = finds.get(&n) {
                let entries = entries.clone();
                for (dst, field, value) in entries {
                    let edge = (dst, field, value);
                    for &o in &pointees {
                        let succs = find_succ.entry(o).or_default();
                        if !succs.contains(&edge) {
                            succs.push(edge);
                            if in_wl.insert(o) {
                                worklist.push_back(o);
                            }
                        }
                    }
                }
            }

            // Predicate split, step 2: `dst ⊇ tag(e, field, v)` for every
            // element `e ∈ pts(n)` when the captured value evaluates; merged
            // elements otherwise (an unevaluable predicate is exactly the
            // conservative `Load`).
            if let Some(entries) = find_succ.get(&n) {
                let entries = entries.clone();
                for (dst, field, value) in entries {
                    match constants.and_then(|c| match value {
                        FindValue::Literal(v) => Some(v),
                        FindValue::Node(node) => c.value_of(&pts, node),
                    }) {
                        Some(v) => {
                            let mut changed = false;
                            for &e in &pointees {
                                let element = arena.tag_element(e, field, v).unwrap_or(e);
                                changed |= pts.insert(dst, element);
                            }
                            if changed && in_wl.insert(dst) {
                                worklist.push_back(dst);
                            }
                        }
                        None => {
                            // Unevaluable predicate: merged element, exactly
                            // the conservative `Load`: `dst ⊇ *n`, i.e. the
                            // copy edge `n -> dst` (pts(n) may still grow).
                            if copy_succ.entry(n).or_default().insert(dst) && in_wl.insert(n) {
                                worklist.push_back(n);
                            }
                        }
                    }
                }
            }
        }

        let _ = self.loc_count;
        pts
    }

    /// Scalar constant fixpoint over a fixed points-to relation.
    ///
    /// The transfer rules are the constant-preserving inclusion edges:
    /// `Const` seeds; `Copy` moves a constant; `Load`/`FindElement` read the
    /// constants of the source's pointees; `Store` writes a constant into the
    /// destination's pointees. `Offset` projects pointers, not scalar values,
    /// so it carries no constant rule.
    fn solve_constants(&self, constraints: &ConstraintSet, pts: &PointsTo) -> ConstMap {
        let mut consts = ConstMap::default();
        let mut copy_succ: FxHashMap<LocId, FxHashSet<LocId>> = FxHashMap::default();
        let mut load_succ: FxHashMap<LocId, FxHashSet<LocId>> = FxHashMap::default();
        let mut store_succ: FxHashMap<LocId, FxHashSet<LocId>> = FxHashMap::default();
        let mut worklist: VecDeque<LocId> = VecDeque::new();
        let mut in_wl: FxHashSet<LocId> = FxHashSet::default();

        let push = |n: LocId, wl: &mut VecDeque<LocId>, in_wl: &mut FxHashSet<LocId>| {
            if in_wl.insert(n) {
                wl.push_back(n);
            }
        };

        for c in constraints.iter() {
            match *c {
                Constraint::Const { dst, value } => {
                    let v = match value {
                        Some(v) => ConstVal::Known(v),
                        None => ConstVal::Unknown,
                    };
                    if consts.join(dst, v) {
                        push(dst, &mut worklist, &mut in_wl);
                    }
                }
                Constraint::Copy { dst, src } => {
                    copy_succ.entry(src).or_default().insert(dst);
                }
                Constraint::Load { dst, src } => {
                    for &o in pts.points_to(src) {
                        load_succ.entry(o).or_default().insert(dst);
                    }
                }
                Constraint::FindElement { dst, src, .. } => {
                    for &o in pts.points_to(src) {
                        load_succ.entry(o).or_default().insert(dst);
                    }
                }
                Constraint::Store { dst, src } => {
                    for &o in pts.points_to(dst) {
                        store_succ.entry(src).or_default().insert(o);
                    }
                }
                Constraint::AddressOf { .. } | Constraint::Offset { .. } => {}
            }
        }

        while let Some(n) = worklist.pop_front() {
            in_wl.remove(&n);
            let Some(v) = consts.get(n) else {
                continue;
            };
            let succs: Vec<LocId> = copy_succ
                .get(&n)
                .into_iter()
                .flatten()
                .copied()
                .chain(load_succ.get(&n).into_iter().flatten().copied())
                .chain(store_succ.get(&n).into_iter().flatten().copied())
                .collect();
            for succ in succs {
                if consts.join(succ, v) {
                    push(succ, &mut worklist, &mut in_wl);
                }
            }
        }

        consts
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::memory::pta::constraint::{Constraint, ConstraintSet};
    use crate::analysis::memory::pta::loc::{AllocSite, LocArena, ProjElem};

    #[test]
    fn copy_propagates_points_to() {
        let mut arena = crate::analysis::memory::pta::loc::LocArena::default();
        let (p, q, a) = (0u32, 1u32, 2u32);
        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf { dst: p, obj: a });
        cs.add(Constraint::Copy { dst: q, src: p });
        let pts = Solver::new(3).solve(&cs, &mut arena);
        assert!(pts.points_to(q).contains(&a));
    }

    #[test]
    fn load_store_through_pointer() {
        let mut arena = crate::analysis::memory::pta::loc::LocArena::default();
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
        use crate::analysis::memory::pta::loc::{AllocSite, LocArena, ProjElem};
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let f0 = arena.extend_path(empty, ProjElem::Field(0));

        let o = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 0,
            },
            empty,
        );
        let p = arena.var(0, 1, empty);
        let q = arena.var(0, 2, empty);
        let o_f0 = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 0,
            },
            f0,
        );

        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf { dst: p, obj: o });
        cs.add(Constraint::Offset {
            dst: q,
            src: p,
            suffix: f0,
        });

        let pts = Solver::new(0).solve(&cs, &mut arena);
        assert!(pts.points_to(q).contains(&o_f0));
    }

    #[test]
    fn offset_after_load_models_field_through_deref() {
        use crate::analysis::memory::pta::loc::{AllocSite, LocArena, ProjElem};
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let f0 = arena.extend_path(empty, ProjElem::Field(0));

        let o = arena.heap(
            AllocSite {
                func: 0,
                bb: 9,
                idx: 0,
            },
            empty,
        );
        let self_slot = arena.var(0, 1, empty); // V_self
        let addr_self = arena.var(0, 100, empty); // &self (pts = {V_self})
        let derefed = arena.var(0, 101, empty); // *self (pts = pts(V_self) = {O})
        let field = arena.var(0, 102, empty); // &(*self).f0
        let o_f0 = arena.heap(
            AllocSite {
                func: 0,
                bb: 9,
                idx: 0,
            },
            f0,
        );

        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf {
            dst: self_slot,
            obj: o,
        });
        cs.add(Constraint::AddressOf {
            dst: addr_self,
            obj: self_slot,
        });
        cs.add(Constraint::Load {
            dst: derefed,
            src: addr_self,
        });
        cs.add(Constraint::Offset {
            dst: field,
            src: derefed,
            suffix: f0,
        });

        let pts = Solver::new(0).solve(&cs, &mut arena);
        assert!(pts.points_to(field).contains(&o_f0));
    }

    #[test]
    fn constants_join_and_propagate_through_copy_and_load() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let o = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 0,
            },
            empty,
        );
        let p = arena.var(0, 1, empty);
        let addr = arena.var(0, 2, empty);
        let v = arena.var(0, 3, empty);
        let mut cs = ConstraintSet::default();
        cs.add(Constraint::Const {
            dst: p,
            value: Some(0),
        });
        cs.add(Constraint::Const {
            dst: p,
            value: Some(0),
        });
        cs.add(Constraint::Copy { dst: addr, src: p });
        cs.add(Constraint::AddressOf { dst: addr, obj: o });
        cs.add(Constraint::Store { dst: addr, src: p });
        cs.add(Constraint::Load { dst: v, src: addr });
        let sol = Solver::new(0).solve_full(&cs, &mut arena);
        assert_eq!(sol.constants.known(p), Some(0));
        assert_eq!(sol.constants.known(addr), Some(0));
        assert_eq!(sol.constants.known(v), Some(0));
        // A differing constant write joins to unknown.
        let mut cs2 = ConstraintSet::default();
        cs2.add(Constraint::Const {
            dst: p,
            value: Some(0),
        });
        cs2.add(Constraint::Const {
            dst: p,
            value: Some(1),
        });
        let sol2 = Solver::new(0).solve_full(&cs2, &mut arena);
        assert!(sol2.constants.is_unknown(p));
        assert_eq!(sol2.constants.known(p), None);
        // An explicit unknown write kills a constant.
        let mut cs3 = ConstraintSet::default();
        cs3.add(Constraint::Const {
            dst: p,
            value: Some(0),
        });
        cs3.add(Constraint::Const {
            dst: p,
            value: None,
        });
        let sol3 = Solver::new(0).solve_full(&cs3, &mut arena);
        assert!(sol3.constants.is_unknown(p));
    }

    #[test]
    fn predicate_split_tags_elements_by_field_and_value() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let idx = arena.extend_path(empty, ProjElem::Index);
        let f0 = arena.extend_path(empty, ProjElem::Field(0));
        let site = AllocSite {
            func: 7,
            bb: 3,
            idx: 1,
        };
        let container = arena.heap(site, empty);
        let element = arena.project(container, idx).unwrap();
        // The iterator model's `temp` node points at the element-reference
        // slot; that slot points at the (merged) element. `FindElement`
        // reads two levels (the same shape as `Load`).
        let slot = arena.var(7, 9, empty);
        let src = arena.var(7, 10, empty);
        let dst0 = arena.var(7, 20, empty);
        let dst1 = arena.var(7, 21, empty);
        let v0 = arena.var(7, 30, empty);
        let v1 = arena.var(7, 31, empty);
        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf {
            dst: slot,
            obj: element,
        });
        cs.add(Constraint::AddressOf {
            dst: src,
            obj: slot,
        });
        cs.add(Constraint::Const {
            dst: v0,
            value: Some(0),
        });
        cs.add(Constraint::Const {
            dst: v1,
            value: Some(1),
        });
        cs.add(Constraint::FindElement {
            dst: dst0,
            src,
            field: f0,
            value: FindValue::Node(v0),
        });
        cs.add(Constraint::FindElement {
            dst: dst1,
            src,
            field: f0,
            value: FindValue::Node(v1),
        });
        let sol = Solver::new(0).solve_full(&cs, &mut arena);
        let p0 = sol.points_to.points_to(dst0);
        let p1 = sol.points_to.points_to(dst1);
        assert_eq!(p0.len(), 1);
        assert_eq!(p1.len(), 1);
        let (a, b) = (p0.iter().next().unwrap(), p1.iter().next().unwrap());
        assert_ne!(a, b);
        // The two selections are provably different elements; either one may
        // still alias the merged element index.
        assert!(!crate::analysis::memory::pta::loc::proj_paths_may_overlap(
            arena.path(match arena.loc(*a) {
                crate::analysis::memory::pta::loc::AbstractLoc::Heap { path, .. } => *path,
                _ => unreachable!(),
            }),
            arena.path(match arena.loc(*b) {
                crate::analysis::memory::pta::loc::AbstractLoc::Heap { path, .. } => *path,
                _ => unreachable!(),
            }),
        ));
        let merged_path = idx;
        assert!(crate::analysis::memory::pta::loc::proj_paths_may_overlap(
            arena.path(match arena.loc(*a) {
                crate::analysis::memory::pta::loc::AbstractLoc::Heap { path, .. } => *path,
                _ => unreachable!(),
            }),
            arena.path(merged_path),
        ));
    }

    #[test]
    fn predicate_literal_splits_without_a_captured_node() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let idx = arena.extend_path(empty, ProjElem::Index);
        let f0 = arena.extend_path(empty, ProjElem::Field(0));
        let container = arena.heap(
            AllocSite {
                func: 1,
                bb: 1,
                idx: 0,
            },
            empty,
        );
        let element = arena.project(container, idx).unwrap();
        let slot = arena.var(1, 2, empty);
        let src = arena.var(1, 3, empty);
        let dst = arena.var(1, 4, empty);
        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf {
            dst: slot,
            obj: element,
        });
        cs.add(Constraint::AddressOf {
            dst: src,
            obj: slot,
        });
        cs.add(Constraint::FindElement {
            dst,
            src,
            field: f0,
            value: FindValue::Literal(5),
        });
        let sol = Solver::new(0).solve_full(&cs, &mut arena);
        let pointees = sol.points_to.points_to(dst);
        assert_eq!(pointees.len(), 1);
        let tagged = pointees.iter().next().unwrap();
        let path = match arena.loc(*tagged) {
            crate::analysis::memory::pta::loc::AbstractLoc::Heap { path, .. } => *path,
            _ => unreachable!(),
        };
        assert_eq!(
            arena.path(path),
            &[ProjElem::Predicate {
                field: f0,
                value: 5
            }]
        );
    }

    #[test]
    fn captured_reference_value_reads_through_one_pointee_level() {
        // `&id` captured into a closure field: the field itself carries no
        // scalar entry; its pointee (the `id` parameter local) is `Known(7)`.
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let id = arena.var(0, 2, empty);
        let addr = arena.var(0, 8, empty);
        let field = arena.var(0, 9, empty);
        let mut cs = ConstraintSet::default();
        cs.add(Constraint::Const {
            dst: id,
            value: Some(7),
        });
        cs.add(Constraint::AddressOf { dst: addr, obj: id });
        cs.add(Constraint::Copy {
            dst: field,
            src: addr,
        });
        let sol = Solver::new(0).solve_full(&cs, &mut arena);
        assert_eq!(sol.constants.value_of(&sol.points_to, field), Some(7));
        // A second, different constant reachable through the same reference
        // makes the capture dynamic (no single value can be proven).
        let other = arena.var(0, 10, empty);
        cs.add(Constraint::Const {
            dst: other,
            value: Some(8),
        });
        cs.add(Constraint::AddressOf {
            dst: addr,
            obj: other,
        });
        let sol2 = Solver::new(0).solve_full(&cs, &mut arena);
        assert_eq!(sol2.constants.known(field), None);
        assert_eq!(sol2.constants.value_of(&sol2.points_to, field), None);
    }

    #[test]
    fn unevaluable_predicate_keeps_the_merged_element() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let idx = arena.extend_path(empty, ProjElem::Index);
        let f0 = arena.extend_path(empty, ProjElem::Field(0));
        let container = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 0,
            },
            empty,
        );
        let element = arena.project(container, idx).unwrap();
        let slot = arena.var(0, 1, empty);
        let src = arena.var(0, 2, empty);
        let dst = arena.var(0, 3, empty);
        let v = arena.var(0, 4, empty);
        let mut cs = ConstraintSet::default();
        cs.add(Constraint::AddressOf {
            dst: slot,
            obj: element,
        });
        cs.add(Constraint::AddressOf {
            dst: src,
            obj: slot,
        });
        cs.add(Constraint::Const {
            dst: v,
            value: None,
        });
        cs.add(Constraint::FindElement {
            dst,
            src,
            field: f0,
            value: FindValue::Node(v),
        });
        let sol = Solver::new(0).solve_full(&cs, &mut arena);
        assert_eq!(sol.points_to.points_to(dst), &{
            let mut s = FxHashSet::default();
            s.insert(element);
            s
        });
    }
}
