use super::context::Context;
use super::intern::Interner;

/// Projection element, decoupled from rustc `PlaceElem` so the core stays
/// rustc-free. Dynamic array/slice indices are merged into a single `Index`
/// (sound over-approximation); a MIR `ConstantIndex` on a fixed-length array
/// is kept as `ConstIndex` so `a[0]` and `a[1]` are different abstract
/// locations. `Index` and `ConstIndex` are *not* interchangeable: `Index` is
/// the may-set of every dynamic index, and the alias query treats it as
/// possibly aliasing any constant-indexed element (see
/// `PointerAnalysis::classify_receiver_alias_paths`).
///
/// `Predicate` is the scalar-domain refinement: an iterator element
/// selected by `find(|x| x.field == value)` is identified by the predicate
/// that chose it. It replaces the merged element `Index` for the *matching*
/// branch only; two elements selected by the same predicate field with
/// different constants are provably different elements of one container, while
/// a predicate element still may equal the merged `Index`/any `ConstIndex`
/// element (sound may-alias against untagged accesses).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ProjElem {
    Field(u32),
    Deref,
    Index,
    ConstIndex(u64),
    Predicate { field: FieldPath, value: u64 },
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
    Var {
        func: u32,
        base: u32,
        path: FieldPath,
    },
    Heap {
        site: AllocSite,
        path: FieldPath,
    },
    Global {
        def_index: u64,
        path: FieldPath,
    },
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
            AbstractLoc::Var {
                ctx, func, base, ..
            } => AbstractLoc::Var {
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

    /// Replace a location's trailing merged element index with a predicate
    /// tag: `container·…·Index` becomes `container·…·Predicate{field, value}`.
    ///
    /// Used by the `find` element split: when the closure predicate
    /// `a.field == value` is evaluable, the returned element is tagged with
    /// the equality that selected it. Returns `None` when the location does
    /// not end in a merged `Index` (no tag can be applied), in which case the
    /// caller keeps the merged location (sound over-approximation).
    pub fn tag_element(&mut self, loc: LocId, field: FieldPath, value: u64) -> Option<LocId> {
        let base_path = match self.locs.get(loc) {
            AbstractLoc::Var { path, .. }
            | AbstractLoc::Heap { path, .. }
            | AbstractLoc::Global { path, .. } => *path,
        };
        let mut elems = self.paths.get(base_path).clone();
        if elems.last() != Some(&ProjElem::Index) {
            return None;
        }
        *elems
            .last_mut()
            .expect("checked non-empty by the Index test") = ProjElem::Predicate { field, value };
        let new_path = self.paths.intern(elems);
        let tagged = match self.locs.get(loc) {
            AbstractLoc::Var {
                ctx, func, base, ..
            } => AbstractLoc::Var {
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
        Some(self.locs.intern(tagged))
    }

    /// Split a location into its empty-path base and its field path. The base
    /// is interned (reusing an existing node when present) so callers can keep
    /// following value flow through the *aggregate* that contains a projected
    /// field.
    pub fn base_and_path(&mut self, id: LocId) -> (LocId, FieldPath) {
        let loc = self.locs.get(id).clone();
        let empty = self.empty_path();
        match loc {
            AbstractLoc::Var {
                ctx,
                func,
                base,
                path,
            } => (self.var_ctx(ctx, func, base, empty), path),
            AbstractLoc::Heap { ctx, site, path } => (
                self.locs.intern(AbstractLoc::Heap {
                    ctx,
                    site,
                    path: empty,
                }),
                path,
            ),
            AbstractLoc::Global { def_index, path } => (self.global(def_index, empty), path),
        }
    }

    /// Context-insensitive identity of a location id.
    pub fn ci_key(&self, id: LocId) -> CiKey {
        match self.locs.get(id) {
            AbstractLoc::Var {
                func, base, path, ..
            } => CiKey::Var {
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

/// Whether two projection paths may denote the same slot.
///
/// Paths of different lengths are different slots (a pointer slot is not its
/// pointee, and a field is not a sub-field). At equal length the elements are
/// compared pairwise: equal fields/derefs/constant indices match, and a dynamic
/// `Index` matches any element including a concrete `ConstIndex(_)`, because it
/// denotes "any element of this container". This is the soundness rule that
/// keeps `xs[*]` aliasing `xs[0]` while `xs[0]` and `xs[1]` stay disjoint.
///
/// A predicate tag is an element-selection certificate: two tags are disjoint
/// only when they select on the same field with different constants (a single
/// element cannot have one field equal to two distinct values). Against a
/// merged `Index`/`ConstIndex` the tag may still overlap, because untagged
/// accesses can reach the same element.
pub fn proj_paths_may_overlap(a: &[ProjElem], b: &[ProjElem]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter().zip(b.iter()).all(|(ea, eb)| match (ea, eb) {
        (ProjElem::Field(fa), ProjElem::Field(fb)) => fa == fb,
        (ProjElem::Deref, ProjElem::Deref) => true,
        (ProjElem::Index, ProjElem::Index)
        | (ProjElem::Index, ProjElem::ConstIndex(_))
        | (ProjElem::ConstIndex(_), ProjElem::Index) => true,
        (ProjElem::ConstIndex(ia), ProjElem::ConstIndex(ib)) => ia == ib,
        (
            ProjElem::Predicate {
                field: fa,
                value: va,
            },
            ProjElem::Predicate {
                field: fb,
                value: vb,
            },
        ) => fa != fb || va == vb,
        (ProjElem::Predicate { .. }, ProjElem::Index | ProjElem::ConstIndex(_))
        | (ProjElem::Index | ProjElem::ConstIndex(_), ProjElem::Predicate { .. }) => true,
        _ => false,
    })
}

/// Whether `key`'s access path identifies one concrete slot. A dynamic
/// `Index` element summarizes "any element of this container", so a key that
/// carries one cannot name a single object.
pub fn ci_key_is_exact(arena: &LocArena, key: &CiKey) -> bool {
    let path = match key {
        CiKey::Var { path, .. } | CiKey::Heap { path, .. } | CiKey::Global { path, .. } => *path,
    };
    !arena
        .path(path)
        .iter()
        .any(|elem| matches!(elem, ProjElem::Index))
}

/// The object identity of a receiver key set under one proven
/// constant argument vector, as sorted names. `None` when the set is empty or
/// contains an inexact (`Index`) key.
///
/// When the set contains `Heap` keys, only those name the object: the `Var`
/// keys in the same set are caller-specific views of that heap (the reference
/// flowed through different frames / closure environments at different call
/// sites), so including them would give one object different identities per
/// call site.
pub fn guard_object_identity_names(arena: &LocArena, keys: &[CiKey]) -> Option<Vec<String>> {
    if keys.is_empty() || !keys.iter().all(|key| ci_key_is_exact(arena, key)) {
        return None;
    }
    let mut names: Vec<String> = {
        let heap: Vec<String> = keys
            .iter()
            .filter(|key| matches!(key, CiKey::Heap { .. }))
            .map(|key| format!("{:?}", key))
            .collect();
        if heap.is_empty() {
            keys.iter().map(|key| format!("{:?}", key)).collect()
        } else {
            heap
        }
    };
    names.sort();
    Some(names)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proj_path_overlap_rules() {
        // Identical paths overlap.
        assert!(proj_paths_may_overlap(
            &[ProjElem::Deref, ProjElem::Field(0)],
            &[ProjElem::Deref, ProjElem::Field(0)],
        ));
        // Distinct fields / constant indices are disjoint.
        assert!(!proj_paths_may_overlap(
            &[ProjElem::Field(0)],
            &[ProjElem::Field(1)],
        ));
        assert!(!proj_paths_may_overlap(
            &[ProjElem::ConstIndex(0)],
            &[ProjElem::ConstIndex(1)],
        ));
        // A dynamic index may be any element, including a concrete one.
        assert!(proj_paths_may_overlap(
            &[ProjElem::Index],
            &[ProjElem::ConstIndex(7)],
        ));
        assert!(proj_paths_may_overlap(
            &[ProjElem::ConstIndex(7)],
            &[ProjElem::Index],
        ));
        // Different lengths / kinds are different slots.
        assert!(!proj_paths_may_overlap(
            &[ProjElem::Field(0)],
            &[ProjElem::Field(0), ProjElem::Field(0)],
        ));
        assert!(!proj_paths_may_overlap(
            &[ProjElem::Deref, ProjElem::Field(0)],
            &[ProjElem::Field(0)],
        ));
    }

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
        let h = arena.heap(
            AllocSite {
                func: 7,
                bb: 0,
                idx: 0,
            },
            p,
        );
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

        let h = arena.heap(
            AllocSite {
                func: 7,
                bb: 0,
                idx: 0,
            },
            empty,
        );
        let hf0 = arena.project(h, field0).expect("within cap");
        let hexp = arena.heap(
            AllocSite {
                func: 7,
                bb: 0,
                idx: 0,
            },
            field0,
        );
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

    #[test]
    fn predicate_tags_split_same_field_by_value_only() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let f0 = arena.extend_path(empty, ProjElem::Field(0));
        let f1 = arena.extend_path(empty, ProjElem::Field(1));
        let p0 = [ProjElem::Predicate {
            field: f0,
            value: 0,
        }];
        let p0b = [ProjElem::Predicate {
            field: f0,
            value: 0,
        }];
        let p1 = [ProjElem::Predicate {
            field: f0,
            value: 1,
        }];
        let other_field = [ProjElem::Predicate {
            field: f1,
            value: 0,
        }];
        // Same field + same value: the same selection.
        assert!(proj_paths_may_overlap(&p0, &p0b));
        // Same field + different value: one element cannot have both values.
        assert!(!proj_paths_may_overlap(&p0, &p1));
        // Different predicate fields may select the same element.
        assert!(proj_paths_may_overlap(&p0, &other_field));
        // Untagged element accesses may still reach the selected element.
        assert!(proj_paths_may_overlap(&p0, &[ProjElem::Index]));
        assert!(proj_paths_may_overlap(&p0, &[ProjElem::ConstIndex(0)]));
        assert!(proj_paths_may_overlap(&[ProjElem::Index], &p0));
        // A predicate tag is still an element slot, not a field of one.
        assert!(!proj_paths_may_overlap(&p0, &[ProjElem::Field(0)]));
    }

    #[test]
    fn tag_element_replaces_trailing_merged_index() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let f0 = arena.extend_path(empty, ProjElem::Field(0));
        let idx = arena.extend_path(empty, ProjElem::Index);
        let container = arena.heap(
            AllocSite {
                func: 4,
                bb: 2,
                idx: 1,
            },
            empty,
        );
        let element = arena.project(container, idx).expect("within cap");
        let tagged = arena
            .tag_element(element, f0, 7)
            .expect("merged element can be tagged");
        let expect_path = arena.extend_path(
            empty,
            ProjElem::Predicate {
                field: f0,
                value: 7,
            },
        );
        assert_eq!(
            arena.loc(tagged),
            &AbstractLoc::Heap {
                ctx: Context::empty(),
                site: AllocSite {
                    func: 4,
                    bb: 2,
                    idx: 1
                },
                path: expect_path,
            }
        );
        // The merged element is untouched: untagged accesses keep the
        // conservative identity.
        assert_eq!(
            arena.loc(element),
            &AbstractLoc::Heap {
                ctx: Context::empty(),
                site: AllocSite {
                    func: 4,
                    bb: 2,
                    idx: 1
                },
                path: idx,
            }
        );
        // Tagging again on the already-tagged location is refused (callers
        // then keep it unchanged rather than inventing a nested tag).
        assert_eq!(arena.tag_element(tagged, f0, 8), None);
        // A non-element slot cannot be tagged either.
        assert_eq!(arena.tag_element(container, f0, 0), None);
    }

    #[test]
    fn ci_key_exactness_rejects_dynamic_index_only() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let field0 = arena.extend_path(empty, ProjElem::Field(0));
        let index = arena.extend_path(field0, ProjElem::Index);
        let const_index = arena.extend_path(field0, ProjElem::ConstIndex(3));
        let predicate = arena.extend_path(
            field0,
            ProjElem::Predicate {
                field: field0,
                value: 1,
            },
        );
        let site = AllocSite {
            func: 1,
            bb: 0,
            idx: 0,
        };
        // Empty path, fields, constant indices and predicate tags all name one
        // concrete slot.
        assert!(ci_key_is_exact(&arena, &CiKey::Heap { site, path: empty }));
        assert!(ci_key_is_exact(&arena, &CiKey::Heap { site, path: field0 }));
        assert!(ci_key_is_exact(
            &arena,
            &CiKey::Heap {
                site,
                path: const_index,
            }
        ));
        assert!(ci_key_is_exact(
            &arena,
            &CiKey::Heap {
                site,
                path: predicate,
            }
        ));
        // A dynamic `Index` summarizes "any element": inexact for every key
        // kind.
        assert!(!ci_key_is_exact(&arena, &CiKey::Heap { site, path: index }));
        assert!(!ci_key_is_exact(
            &arena,
            &CiKey::Var {
                func: 1,
                base: 2,
                path: index,
            }
        ));
        assert!(!ci_key_is_exact(
            &arena,
            &CiKey::Global {
                def_index: 3,
                path: index,
            }
        ));
    }

    #[test]
    fn guard_object_identity_prefers_heap_keys() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let p199 = arena.extend_path(empty, ProjElem::ConstIndex(199));
        let p200 = arena.extend_path(empty, ProjElem::ConstIndex(200));
        let index = arena.extend_path(empty, ProjElem::Index);
        let site = AllocSite {
            func: 74,
            bb: 5,
            idx: 5,
        };
        let heap199 = CiKey::Heap { site, path: p199 };
        let heap200 = CiKey::Heap { site, path: p200 };
        // A caller-specific view of the same object: the closure environment
        // through which the reference flowed differs between call sites.
        let var_view = CiKey::Var {
            func: 216,
            base: 35,
            path: empty,
        };

        // With heap keys present, only they name the object: the two abstract
        // elements stay distinct, the Var view is dropped.
        let names =
            guard_object_identity_names(&arena, &[heap200, var_view, heap199]).expect("exact");
        assert_eq!(names.len(), 2, "one name per heap key, Var view dropped");
        assert!(
            names.iter().all(|name| name.starts_with("Heap")),
            "{names:?}"
        );
        let mut sorted = names.clone();
        sorted.sort();
        assert_eq!(names, sorted, "names are sorted for a stable resource key");

        // Without heap keys, Var/Global keys are the identity.
        let names = guard_object_identity_names(&arena, &[var_view]).expect("exact");
        assert_eq!(names.len(), 1);
        assert!(names[0].starts_with("Var"));

        // Empty and inexact sets yield no identity.
        assert!(guard_object_identity_names(&arena, &[]).is_none());
        assert!(
            guard_object_identity_names(&arena, &[CiKey::Heap { site, path: index }]).is_none(),
            "a dynamic Index key yields no object identity"
        );
    }
}
