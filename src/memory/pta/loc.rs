use super::context::Context;
use super::intern::Interner;

/// Projection element, decoupled from rustc `PlaceElem` so the core stays
/// rustc-free. Array/slice indices are merged into a single `Index` (sound
/// over-approximation); constant indices may be modeled later for precision.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ProjElem {
    Field(u32),
    Deref,
    Index,
}

/// Interned id for a sequence of `ProjElem` (an access path suffix).
pub type FieldPath = u32;

/// Maximum number of Field/Index elements on any object access path. Beyond
/// this, projection over-approximates by returning the object unprojected,
/// guaranteeing solver termination (bounds the projected-location universe).
pub const FIELD_DEPTH_CAP: usize = 8;

/// Allocation site: identifies a heap object abstractly by its creation point.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct AllocSite {
    /// `InstanceId` index of the allocating function (assigned by the builder).
    pub func: u32,
    pub bb: u32,
    pub idx: u32,
}

/// The universe of abstract memory locations / pointer nodes.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AbstractLoc {
    Var {
        ctx: Context,
        func: u32,
        base: u32,
        path: FieldPath,
    },
    Heap {
        ctx: Context,
        site: AllocSite,
        path: FieldPath,
    },
    Global {
        def_index: u64,
        path: FieldPath,
    },
}

/// Dense id for an interned `AbstractLoc`.
pub type LocId = u32;

/// Context-insensitive identity of an abstract location: the same memory
/// location across all calling contexts. Used to collapse k-CFA results for
/// context-insensitive queries soundly (two pointers alias if they reach the
/// same location under *any* pair of contexts).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CiKey {
    Var { func: u32, base: u32, path: FieldPath },
    Heap { site: AllocSite, path: FieldPath },
    Global { def_index: u64, path: FieldPath },
}

/// Owns the interners for field paths and abstract locations.
#[derive(Default)]
pub struct LocArena {
    paths: Interner<Vec<ProjElem>>,
    locs: Interner<AbstractLoc>,
}

impl LocArena {
    pub fn empty_path(&mut self) -> FieldPath {
        self.paths.intern(Vec::new())
    }

    pub fn extend_path(&mut self, base: FieldPath, elem: ProjElem) -> FieldPath {
        let mut v = self.paths.get(base).clone();
        v.push(elem);
        self.paths.intern(v)
    }

    pub fn path(&self, id: FieldPath) -> &[ProjElem] {
        self.paths.get(id)
    }

    /// Id of the already-interned empty path, if any path was interned.
    pub fn empty_path_id(&self) -> Option<FieldPath> {
        self.paths.get_id(&Vec::new())
    }

    pub fn var(&mut self, func: u32, base: u32, path: FieldPath) -> LocId {
        self.locs.intern(AbstractLoc::Var {
            ctx: Context::empty(),
            func,
            base,
            path,
        })
    }

    pub fn var_ctx(&mut self, ctx: Context, func: u32, base: u32, path: FieldPath) -> LocId {
        self.locs.intern(AbstractLoc::Var {
            ctx,
            func,
            base,
            path,
        })
    }

    pub fn heap(&mut self, site: AllocSite, path: FieldPath) -> LocId {
        self.locs.intern(AbstractLoc::Heap {
            ctx: Context::empty(),
            site,
            path,
        })
    }

    pub fn global(&mut self, def_index: u64, path: FieldPath) -> LocId {
        self.locs.intern(AbstractLoc::Global { def_index, path })
    }

    /// Append `suffix` (Field/Index elems only) to the access path of object
    /// `loc`. Returns the interned projected location. Over-approximates by
    /// returning `loc` unchanged when the result would exceed `FIELD_DEPTH_CAP`.
    pub fn project(&mut self, loc: LocId, suffix: FieldPath) -> Option<LocId> {
        let suffix_elems = self.paths.get(suffix).clone();
        if suffix_elems.is_empty() {
            return Some(loc);
        }
        let base_path = match self.locs.get(loc) {
            AbstractLoc::Var { path, .. }
            | AbstractLoc::Heap { path, .. }
            | AbstractLoc::Global { path, .. } => *path,
        };
        if self.paths.get(base_path).len() + suffix_elems.len() > FIELD_DEPTH_CAP {
            return Some(loc);
        }
        let mut new_path = base_path;
        for e in suffix_elems {
            new_path = self.extend_path(new_path, e);
        }
        let projected = match self.locs.get(loc) {
            AbstractLoc::Var { ctx, func, base, .. } => AbstractLoc::Var {
                ctx: ctx.clone(),
                func: *func,
                base: *base,
                path: new_path,
            },
            AbstractLoc::Heap { ctx, site, .. } => AbstractLoc::Heap {
                ctx: ctx.clone(),
                site: *site,
                path: new_path,
            },
            AbstractLoc::Global { def_index, .. } => AbstractLoc::Global {
                def_index: *def_index,
                path: new_path,
            },
        };
        Some(self.locs.intern(projected))
    }

    pub fn loc(&self, id: LocId) -> &AbstractLoc {
        self.locs.get(id)
    }

    pub fn loc_count(&self) -> usize {
        self.locs.len()
    }

    /// Iterate `(LocId, &AbstractLoc)` for every interned location.
    pub fn iter_locs(&self) -> impl Iterator<Item = (LocId, &AbstractLoc)> {
        self.locs.iter()
    }

    /// Context-insensitive identity of a location id.
    pub fn ci_key(&self, id: LocId) -> CiKey {
        match self.locs.get(id) {
            AbstractLoc::Var { func, base, path, .. } => CiKey::Var {
                func: *func,
                base: *base,
                path: *path,
            },
            AbstractLoc::Heap { site, path, .. } => CiKey::Heap {
                site: *site,
                path: *path,
            },
            AbstractLoc::Global { def_index, path } => CiKey::Global {
                def_index: *def_index,
                path: *path,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_path_intern_and_extend() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let f0 = arena.extend_path(empty, ProjElem::Field(0));
        let f0_deref = arena.extend_path(f0, ProjElem::Deref);
        let empty2 = arena.empty_path();
        let f0b = arena.extend_path(empty2, ProjElem::Field(0));
        assert_eq!(f0, f0b);
        assert_ne!(f0, f0_deref);
        assert_eq!(arena.path(f0).len(), 1);
        assert_eq!(arena.path(f0_deref).len(), 2);
    }

    #[test]
    fn loc_intern_dedup() {
        let mut arena = LocArena::default();
        let p = arena.empty_path();
        let v1 = arena.var(7, 1u32, p);
        let v2 = arena.var(7, 1u32, p);
        let h = arena.heap(AllocSite { func: 7, bb: 0, idx: 0 }, p);
        assert_eq!(v1, v2);
        assert_ne!(v1, h);
        assert_eq!(arena.loc_count(), 2);
    }

    #[test]
    fn project_appends_field_path_to_object() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let field0 = arena.extend_path(empty, ProjElem::Field(0));

        let v = arena.var(7, 1, empty);
        let vf0 = arena.project(v, field0).expect("within cap");
        let expect = arena.var(7, 1, field0);
        assert_eq!(vf0, expect);

        let h = arena.heap(AllocSite { func: 7, bb: 0, idx: 0 }, empty);
        let hf0 = arena.project(h, field0).expect("within cap");
        let hexp = arena.heap(AllocSite { func: 7, bb: 0, idx: 0 }, field0);
        assert_eq!(hf0, hexp);
    }

    #[test]
    fn project_empty_suffix_is_identity() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let v = arena.var(1, 2, empty);
        assert_eq!(arena.project(v, empty), Some(v));
    }

    #[test]
    fn project_beyond_depth_cap_returns_object_unprojected() {
        let mut arena = LocArena::default();
        let mut p = arena.empty_path();
        for _ in 0..FIELD_DEPTH_CAP {
            p = arena.extend_path(p, ProjElem::Field(0));
        }
        let v = arena.var(1, 2, p); // already at cap
        let one_more = {
            let e = arena.empty_path();
            arena.extend_path(e, ProjElem::Field(1))
        };
        assert_eq!(arena.project(v, one_more), Some(v));
    }
}
