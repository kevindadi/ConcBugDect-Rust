//! MIR → constraint translation.
//!
//! Places are resolved field-sensitively by a [`PlaceWalk`]: Field/Index
//! projections become `Offset` constraints that append to an object's access
//! path within the *same* object, while `Deref` follows a pointer via a `Load`
//! and is NEVER baked into a path. The local slot `Var{func,base,path:[]}` is
//! the addressable storage; heap objects come from call models, not per-place
//! seeding.

extern crate rustc_abi;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_data_structures::fx::FxHashSet;
use smallvec::SmallVec;

use rustc_middle::mir::{
    AggregateKind, Body, Const, ConstOperand, LocalKind, Operand, Place, PlaceElem,
    ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::ty::{self, GenericArgsRef, Instance, TyCtxt, TypingEnv};
use rustc_span::Spanned;

use super::constraint::{Constraint, ConstraintSet};
use super::context::Context;
use super::loc::{AllocSite, FieldPath, LocArena, LocId, ProjElem};
use super::model::{CallNodes, ModelRegistry};
use super::typeutil::leaf_field_paths;
use crate::memory::ownership;

/// A call site recorded during constraint building, to be resolved by the
/// driver (which owns the cross-function `FuncMap`). For analyzable callees the
/// driver emits interprocedural binding; otherwise the conservative model.
pub struct PendingCall<'tcx> {
    /// Monomorphized callee, if the call is a direct `FnDef`; `None` for
    /// indirect calls (fn pointers / dynamic dispatch).
    pub callee: Option<(DefId, GenericArgsRef<'tcx>)>,
    /// Basic block of the call terminator in the caller; combined with the
    /// caller's `func` id it forms the `CallSite` for context extension.
    pub bb: u32,
    pub dest: LocId,
    pub args: SmallVec<[Option<LocId>; 4]>,
    pub fresh_heap: LocId,
}

/// Store an aggregate `value` into heap object `heap`, field-wise, and point
/// `dest` (the smart-pointer local) at `heap`. `leaf_paths` are the boxed
/// type's leaf field paths from `typeutil::leaf_field_paths`. The empty path
/// (a non-aggregate boxed value) reduces to `Copy{heap, value}`. Reused for
/// `Box`/`Arc`/`Rc::new`. rustc-free so it is unit-tested directly.
pub(crate) fn emit_boxed_value(
    arena: &mut LocArena,
    out: &mut ConstraintSet,
    dest: LocId,
    heap: LocId,
    value: LocId,
    leaf_paths: &[FieldPath],
) {
    out.add(Constraint::AddressOf {
        dst: dest,
        obj: heap,
    });
    // Copy every field-path prefix of the boxed value into the heap, not just
    // the leaves: a whole-aggregate field (`(Mutex, Condvar).1`) holds the
    // value that is later referenced from a spawned closure (`&(*arc).1`), so
    // its identity must reach the corresponding heap slot. Leaf-only copies
    // leave the intermediate field slot disconnected.
    let mut seen = FxHashSet::default();
    for &p in leaf_paths {
        let elems: Vec<ProjElem> = arena.path(p).to_vec();
        let mut prefix = arena.empty_path();
        for e in elems {
            prefix = arena.extend_path(prefix, e);
            if !seen.insert(prefix) {
                continue;
            }
            if let (Some(hp), Some(vp)) =
                (arena.project(heap, prefix), arena.project(value, prefix))
            {
                out.add(Constraint::Copy { dst: hp, src: vp });
            }
        }
    }
}

/// rustc-free mirror of a MIR projection element used by the place walk.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProjKind {
    Field(u32),
    Deref,
    Index,
}

/// Resolves MIR places into field-sensitive constraint nodes.
pub struct PlaceWalk<'a> {
    arena: &'a mut LocArena,
    cs: &'a mut ConstraintSet,
    func: u32,
    ctx: Context,
    /// Shared monotonic temp counter owned by the builder, so every fresh temp
    /// in a function body is distinct across statements (no cross-statement
    /// node collisions / spurious aliasing).
    next_temp: &'a mut u32,
}

impl<'a> PlaceWalk<'a> {
    pub fn new(
        arena: &'a mut LocArena,
        cs: &'a mut ConstraintSet,
        func: u32,
        next_temp: &'a mut u32,
    ) -> Self {
        Self {
            arena,
            cs,
            func,
            ctx: Context::empty(),
            next_temp,
        }
    }

    pub fn with_ctx(
        arena: &'a mut LocArena,
        cs: &'a mut ConstraintSet,
        func: u32,
        ctx: Context,
        next_temp: &'a mut u32,
    ) -> Self {
        Self {
            arena,
            cs,
            func,
            ctx,
            next_temp,
        }
    }

    fn empty(&mut self) -> FieldPath {
        self.arena.empty_path()
    }

    fn slot(&mut self, base: u32, path: FieldPath) -> LocId {
        self.arena.var_ctx(self.ctx.clone(), self.func, base, path)
    }

    fn fresh(&mut self) -> LocId {
        let id = *self.next_temp;
        *self.next_temp += 1;
        let empty = self.empty();
        self.slot(id, empty)
    }

    fn intern_suffix(&mut self, elems: &[ProjKind]) -> FieldPath {
        let mut p = self.empty();
        for e in elems {
            let pe = match e {
                ProjKind::Field(f) => ProjElem::Field(*f),
                ProjKind::Index => ProjElem::Index,
                ProjKind::Deref => unreachable!("deref is not a path elem"),
            };
            p = self.arena.extend_path(p, pe);
        }
        p
    }

    /// Node whose points-to set is the set of lvalue locations `place` denotes
    /// (i.e. what `&place` points to).
    pub fn place_addr(&mut self, local: u32, proj: &[ProjKind]) -> LocId {
        let empty = self.empty();
        let slot = self.slot(local, empty);
        let cur0 = self.fresh();
        self.cs.add(Constraint::AddressOf {
            dst: cur0,
            obj: slot,
        }); // pts(cur0) = { V_local }
        let mut cur = cur0;
        let mut pending: Vec<ProjKind> = Vec::new();
        for e in proj {
            match e {
                ProjKind::Field(_) | ProjKind::Index => pending.push(*e),
                ProjKind::Deref => {
                    cur = self.apply_pending(cur, &mut pending); // field offset first
                    let next = self.fresh();
                    self.cs.add(Constraint::Load {
                        dst: next,
                        src: cur,
                    }); // *cur
                    cur = next;
                }
            }
        }
        self.apply_pending(cur, &mut pending)
    }

    fn apply_pending(&mut self, cur: LocId, pending: &mut Vec<ProjKind>) -> LocId {
        if pending.is_empty() {
            return cur;
        }
        let suffix = self.intern_suffix(pending);
        pending.clear();
        let next = self.fresh();
        self.cs.add(Constraint::Offset {
            dst: next,
            src: cur,
            suffix,
        });
        next
    }

    /// Node whose points-to set is the value held at `place`.
    pub fn place_value(&mut self, local: u32, proj: &[ProjKind]) -> LocId {
        if proj.is_empty() {
            let empty = self.empty();
            return self.slot(local, empty);
        }
        let addr = self.place_addr(local, proj);
        let v = self.fresh();
        self.cs.add(Constraint::Load { dst: v, src: addr }); // value = *addr
        v
    }
}

/// Translate a single MIR `Body` into inclusion constraints.
///
/// Call terminators are dispatched through `registry`: a matching library
/// model is applied, otherwise the call is recorded for interprocedural
/// binding by the driver (it owns the cross-function `FuncMap`); see
/// [`super::interproc`].
pub fn build_body<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    func: u32,
    ctx: Context,
    caller: Instance<'tcx>,
    registry: &ModelRegistry,
    arena: &mut LocArena,
    constraints: &mut ConstraintSet,
    closure_envs: &mut rustc_data_structures::fx::FxHashMap<DefId, SmallVec<[LocId; 2]>>,
    closure_env_paths: &mut rustc_data_structures::fx::FxHashMap<DefId, SmallVec<[FieldPath; 16]>>,
) -> Vec<PendingCall<'tcx>> {
    let typing_env = TypingEnv::post_analysis(tcx, caller.def_id());
    let mut builder = ConstraintBuilder {
        tcx,
        body,
        func,
        ctx,
        caller,
        typing_env,
        arena,
        constraints,
        closure_envs,
        closure_env_paths,
        pending: Vec::new(),
        call_counter: 0,
        next_temp: 1_000_000,
        addr_taken: rustc_data_structures::fx::FxHashSet::default(),
    };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                builder.process_assignment(place, rvalue);
            }
        }
        if let Some(term) = &data.terminator {
            if let TerminatorKind::Call {
                func: callee,
                args,
                destination,
                ..
            } = &term.kind
            {
                builder.process_call(bb.as_u32(), callee, args, destination, registry);
            }
        }
    }
    // Address-taken seeding disabled until precision is improved: it still
    // duplicates boxed/aggregate objects in several benchmarks. Arc-based
    // deadlock cases rely on emit_boxed_value closure binding instead.
    // builder.seed_addr_taken();
    builder.pending
}

struct ConstraintBuilder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    func: u32,
    /// Calling context this body is being built under (k-CFA). Tags every
    /// local/place node so the same instance can be cloned per context.
    ctx: Context,
    caller: Instance<'tcx>,
    typing_env: TypingEnv<'tcx>,
    arena: &'a mut LocArena,
    constraints: &'a mut ConstraintSet,
    /// Closure DefId → def-site environment heaps, threaded up to the driver so
    /// closure bodies can be bound to the environment that captured their upvars.
    closure_envs: &'a mut rustc_data_structures::fx::FxHashMap<DefId, SmallVec<[LocId; 2]>>,
    /// Closure DefId → environment field paths that were actually captured
    /// (base upvar slot and nested leaf paths of aggregate upvars). Threaded up
    /// to the driver so it can bind the closure body's env slots to the heap.
    closure_env_paths: &'a mut rustc_data_structures::fx::FxHashMap<DefId, SmallVec<[FieldPath; 16]>>,
    /// Call sites awaiting interprocedural resolution by the driver.
    pending: Vec<PendingCall<'tcx>>,
    /// Monotonic counter giving each call site a distinct fresh heap object.
    call_counter: u32,
    /// Shared monotonic counter for place-walk temp nodes, threaded into every
    /// `PlaceWalk` so temps are distinct across all statements in this body.
    /// Based at `1_000_000` to stay clear of real (small-index) MIR locals.
    next_temp: u32,
    /// Locals whose storage address is taken (`r = &local`).
    addr_taken: rustc_data_structures::fx::FxHashSet<u32>,
}

impl<'a, 'tcx> ConstraintBuilder<'a, 'tcx> {
    /// Convert a rustc MIR projection into the rustc-free [`ProjKind`] slice the
    /// place walk consumes. Index / ConstantIndex / Subslice / Downcast /
    /// OpaqueCast etc. collapse into a single `Index` (sound over-approximation).
    /// Extend an interned field path by the elements of another leaf path.
    fn extend_path_with(&mut self, base: FieldPath, suffix: FieldPath) -> FieldPath {
        let elems: Vec<ProjElem> = self.arena.path(suffix).to_vec();
        let mut p = base;
        for e in elems {
            p = self.arena.extend_path(p, e);
        }
        p
    }

    fn proj_kinds(proj: &[PlaceElem<'tcx>]) -> SmallVec<[ProjKind; 4]> {        let mut out: SmallVec<[ProjKind; 4]> = SmallVec::new();
        for e in proj {
            out.push(match e {
                ProjectionElem::Field(f, _) => ProjKind::Field(f.as_u32()),
                ProjectionElem::Deref => ProjKind::Deref,
                _ => ProjKind::Index,
            });
        }
        out
    }

    /// A `PlaceWalk` borrowing this builder's arena and constraint set. The
    /// returned walk mutably borrows `*self` for its lifetime, so each call
    /// MUST be scoped in its own block and dropped before any other `self.*`
    /// access.
    fn walk(&mut self) -> PlaceWalk<'_> {
        PlaceWalk::with_ctx(
            self.arena,
            self.constraints,
            self.func,
            self.ctx.clone(),
            &mut self.next_temp,
        )
    }

    /// Value node for a Move/Copy operand; `None` for constants.
    fn operand_value(&mut self, op: &Operand<'tcx>) -> Option<LocId> {
        match op {
            Operand::Move(p) | Operand::Copy(p) => {
                let proj = Self::proj_kinds(p.projection);
                let mut w = self.walk();
                Some(w.place_value(p.local.as_u32(), &proj))
            }
            Operand::Constant(box ConstOperand { const_, .. }) => self.static_ref_global(*const_),
            _ => None,
        }
    }

    /// A constant reference to a static (`const {allocN: &STATIC}`) gets a
    /// [`AbstractLoc::Global`] node keyed by the allocation id, so every access
    /// to the same static (e.g. a `lazy_static!` lock) resolves to the same
    /// abstract object and aliases. Non-static constants return `None`.
    fn static_ref_global(&mut self, const_: Const<'tcx>) -> Option<LocId> {
        use rustc_middle::mir::interpret::GlobalAlloc;
        let scalar = const_.try_to_scalar()?;
        let Scalar::Ptr(ptr, _) = scalar else {
            return None;
        };
        let alloc_id = ptr.provenance.alloc_id();
        if !matches!(self.tcx.global_alloc(alloc_id), GlobalAlloc::Static(_)) {
            return None;
        }
        let empty = self.arena.empty_path();
        let global = self.arena.global(alloc_id.0.get(), empty);
        // Return a node that *points to* the static object (the const value is
        // `&STATIC`), so `dst = const` copies `pts(temp) = {Global}` into the
        // destination rather than the empty points-to set of the object itself.
        let temp = {
            let mut w = self.walk();
            w.fresh()
        };
        self.constraints
            .add(Constraint::AddressOf { dst: temp, obj: global });
        Some(temp)
    }

    /// Store `value` into the lvalue locations of the place `lhs_local.lhs_proj`.
    fn store_value(&mut self, lhs_proj: &[ProjKind], lhs_local: u32, value: LocId) {
        if lhs_proj.is_empty() {
            self.copy_with_aggregate_expansion(lhs_local, value);
            return;
        }
        let addr = {
            let mut w = self.walk();
            w.place_addr(lhs_local, lhs_proj)
        };
        self.constraints.add(Constraint::Store {
            dst: addr,
            src: value,
        });
    }

    fn copy_with_aggregate_expansion(&mut self, dst_local: u32, value: LocId) {
        let empty = self.arena.empty_path();
        let dst_slot = self
            .arena
            .var_ctx(self.ctx.clone(), self.func, dst_local, empty);
        // Base copy is always sound. (Type-driven field expansion for aggregate
        // local-to-local moves is wired in the driver task; base Copy preserves
        // soundness here.)
        self.constraints.add(Constraint::Copy {
            dst: dst_slot,
            src: value,
        });
    }

    /// For aggregate (struct) local-to-local moves/copies, additionally
    /// propagate each leaf field slot (`y.p ⊇ x.p`). A plain base `Copy` only
    /// carries the base slot's points-to set, which is empty for a value
    /// struct, silently dropping every field (e.g. `SharedPtr(*mut i32)` copied
    /// by value into a thread closure). Without this, raw-pointer / shared
    /// value flows through `Copy` structs are lost and cross-thread accesses no
    /// longer alias.
    fn expand_aggregate_copy(&mut self, lhs_proj: &[ProjKind], lhs_local: u32, op: &Operand<'tcx>) {
        if !lhs_proj.is_empty() {
            return;
        }
        let Some(src) = op.place() else {
            return;
        };
        let src_proj = Self::proj_kinds(src.projection);
        let src_local = src.local.as_u32();
        if src_local == lhs_local && src_proj.is_empty() {
            return;
        }
        let ty = self.body.local_decls[rustc_middle::mir::Local::from_usize(lhs_local as usize)].ty;
        let ty = self.caller.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            self.typing_env,
            rustc_middle::ty::EarlyBinder::bind(ty),
        );
        if !matches!(ty.kind(), rustc_middle::ty::TyKind::Adt(..)) {
            return;
        }
        // Source slot prefix for a projected source (`_3 = copy (_1.0)`): the
        // value lives at `src_local` under `src_proj`, so leaf slot `p` is
        // `src_local.(src_proj · p)`. Skip sources with a Deref (not a slot).
        let src_prefix: Vec<ProjElem> = src_proj
            .iter()
            .filter_map(|e| match e {
                ProjKind::Field(f) => Some(ProjElem::Field(*f)),
                ProjKind::Index => Some(ProjElem::Index),
                ProjKind::Deref => None,
            })
            .collect();
        let has_deref = src_proj.iter().any(|e| matches!(e, ProjKind::Deref));

        let paths = leaf_field_paths(self.tcx, self.typing_env, ty, &mut self.arena);
        for p in paths {
            if self.arena.path(p).is_empty() {
                continue;
            }
            let dst = self.arena.var_ctx(self.ctx.clone(), self.func, lhs_local, p);
            let src_slot_path = if has_deref {
                p
            } else {
                let mut combined = p;
                for e in src_prefix.iter().rev() {
                    combined = self.arena.extend_path(combined, *e);
                }
                combined
            };
            let src = self.arena.var_ctx(self.ctx.clone(), self.func, src_local, src_slot_path);
            self.constraints.add(Constraint::Copy { dst, src });
        }
    }

    fn process_assignment(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>) {
        let lhs_proj = Self::proj_kinds(place.projection);
        let lhs_local = place.local.as_u32();
        match rvalue {
            Rvalue::Aggregate(box kind, fields) => match kind {
                AggregateKind::Closure(def_id, substs) => {
                    self.process_closure_aggregate(lhs_local, *def_id, substs, fields);
                }
                _ => {
                    self.assign_aggregate(lhs_local, &lhs_proj, kind, fields);
                }
            },
            Rvalue::Ref(_, _, src) | Rvalue::RawPtr(_, src) => {
                if src.projection.is_empty() {
                    match self.body.local_kind(src.local) {
                        LocalKind::Arg | LocalKind::ReturnPointer => {}
                        _ => {
                            self.addr_taken.insert(src.local.as_u32());
                        }
                    }
                }
                let src_addr = {
                    let proj = Self::proj_kinds(src.projection);
                    let mut w = self.walk();
                    w.place_addr(src.local.as_u32(), &proj)
                };
                self.store_value(&lhs_proj, lhs_local, src_addr);
            }
            Rvalue::Use(op, _) => {
                if let Some(v) = self.operand_value(op) {
                    self.store_value(&lhs_proj, lhs_local, v);
                }
                self.expand_aggregate_copy(&lhs_proj, lhs_local, op);
            }
            Rvalue::Cast(_, op, _)
            | Rvalue::Repeat(op, _)
            | Rvalue::UnaryOp(_, op) => {
                if let Some(v) = self.operand_value(op) {
                    self.store_value(&lhs_proj, lhs_local, v);
                }
            }
            Rvalue::CopyForDeref(src) | Rvalue::Discriminant(src) => {
                let v = {
                    let proj = Self::proj_kinds(src.projection);
                    let mut w = self.walk();
                    w.place_value(src.local.as_u32(), &proj)
                };
                self.store_value(&lhs_proj, lhs_local, v);
            }
            Rvalue::BinaryOp(_, box (l, r)) => {
                for op in [l, r] {
                    if let Some(v) = self.operand_value(op) {
                        self.store_value(&lhs_proj, lhs_local, v);
                    }
                }
            }
            _ => {}
        }
    }

    fn assign_aggregate(
        &mut self,
        dst_local: u32,
        lhs_proj: &[ProjKind],
        _kind: &AggregateKind<'tcx>,
        fields: &rustc_index::IndexVec<rustc_abi::FieldIdx, Operand<'tcx>>,
    ) {
        for (i, op) in fields.iter_enumerated() {
            let Some(value) = self.operand_value(op) else {
                continue;
            };
            let mut proj: SmallVec<[ProjKind; 4]> = SmallVec::from_slice(lhs_proj);
            proj.push(ProjKind::Field(i.as_u32()));
            self.store_value(&proj, dst_local, value);
        }
    }

    fn process_closure_aggregate(
        &mut self,
        dst_local: u32,
        _def_id: DefId,
        _substs: GenericArgsRef<'tcx>,
        fields: &rustc_index::IndexVec<rustc_abi::FieldIdx, Operand<'tcx>>,
    ) {
        // 获取闭包的 upvar 类型信息
        let upvar_tys = _substs.as_closure().upvar_tys();
        let empty = self.arena.empty_path();

        // 为闭包环境创建一个 heap
        self.call_counter += 1;
        let clo_heap = self.arena.heap(
            AllocSite {
                func: self.func,
                bb: 0, // 闭包定义不是 call site,用 0
                idx: self.call_counter,
            },
            empty,
        );

        // Record the def-site environment heap so the closure body's env param
        // (`_1`) can later be bound to it by the driver. A closure may be
        // constructed at several sites; all recorded heaps are unioned.
        self.closure_envs
            .entry(_def_id)
            .or_default()
            .push(clo_heap);

        // 字段级 Copy: clo_heap.field_i ⊇ upvar_value_i
        for (i, op) in fields.iter_enumerated() {
            let Some(value) = self.operand_value(op) else {
                continue;
            };
            let field_path = self.arena.extend_path(empty, ProjElem::Field(i.as_u32()));
            self.closure_env_paths
                .entry(_def_id)
                .or_default()
                .push(field_path);
            if let Some(dst) = self.arena.project(clo_heap, field_path) {
                self.constraints.add(Constraint::Copy { dst, src: value });
            }
            // Aggregate upvars captured by value: also capture each leaf field
            // slot (`clo_heap.field_i·p ⊇ V_upvar.p`). A base copy alone carries
            // the struct's (empty) points-to set, dropping fields such as a raw
            // pointer inside a `SharedPtr` that the closure dereferences.
            if let Some(place) = op.place() {
                if place.projection.is_empty() {
                    let upvar_local = place.local.as_u32();
                    let ty = self.body.local_decls[place.local].ty;
                    let ty = self.caller.instantiate_mir_and_normalize_erasing_regions(
                        self.tcx,
                        self.typing_env,
                        rustc_middle::ty::EarlyBinder::bind(ty),
                    );
                    if matches!(ty.kind(), rustc_middle::ty::TyKind::Adt(..)) {
                        let paths =
                            leaf_field_paths(self.tcx, self.typing_env, ty, &mut self.arena);
                        for p in paths {
                            if self.arena.path(p).is_empty() {
                                continue;
                            }
                            let combined = self.extend_path_with(field_path, p);
                            self.closure_env_paths
                                .entry(_def_id)
                                .or_default()
                                .push(combined);
                            if let Some(dst) = self.arena.project(clo_heap, combined) {
                                let src = self
                                    .arena
                                    .var_ctx(self.ctx.clone(), self.func, upvar_local, p);
                                self.constraints.add(Constraint::Copy { dst, src });
                            }
                        }
                    }
                }
            }
            // 如果 upvar 是引用类型,还需要 AddressOf
            let upvar_ty = upvar_tys.get(i.as_usize());
            if let Some(upvar_ty) = upvar_ty {
                if upvar_ty.is_ref() {
                    let addr = {
                        let mut w = self.walk();
                        w.fresh()
                    };
                    self.constraints.add(Constraint::AddressOf {
                        dst: addr,
                        obj: value,
                    });
                    if let Some(dst) = self.arena.project(clo_heap, field_path) {
                        self.constraints.add(Constraint::Copy { dst, src: addr });
                    }
                }
            }
        }

        // 将 dst_local (闭包变量) 指向这个 heap
        let dst_slot = self
            .arena
            .var_ctx(self.ctx.clone(), self.func, dst_local, empty);
        self.constraints.add(Constraint::AddressOf {
            dst: dst_slot,
            obj: clo_heap,
        });
    }

    fn process_call(
        &mut self,
        bb: u32,
        callee: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        registry: &ModelRegistry,
    ) {
        let dest = {
            let proj = Self::proj_kinds(destination.projection);
            if proj.is_empty() {
                let empty = self.arena.empty_path();
                self.arena.var_ctx(
                    self.ctx.clone(),
                    self.func,
                    destination.local.as_u32(),
                    empty,
                )
            } else {
                // Projected destination (`(*p).f = call()`): models and binding
                // `Copy` the return value into `dest` treating it as a *value*
                // slot. Route through a fresh temp value node stored back
                // through the lvalue address, so field/deref targets receive
                // the value soundly (`*addr ⊇ temp ⊇ return`).
                let (addr, temp) = {
                    let mut w = self.walk();
                    let addr = w.place_addr(destination.local.as_u32(), &proj);
                    let temp = w.fresh();
                    (addr, temp)
                };
                self.constraints.add(Constraint::Store {
                    dst: addr,
                    src: temp,
                });
                temp
            }
        };

        let mut arg_nodes: SmallVec<[Option<LocId>; 4]> = SmallVec::new();
        for a in args {
            arg_nodes.push(self.operand_value(&a.node));
        }

        // Closures are interprocedural: any closure passed by value will be invoked
        // with an environment heap that stores the captured upvars. For each closure arg:
        // 1. Allocate a fresh heap object (clo_heap)
        // 2. Store the captured value (clo_obj) into clo_heap._0
        // 3. Point clo_dest at clo_heap via AddressOf
        // 4. Queue the closure body for analysis with clo_dest as the destination
        for (i, a) in args.iter().enumerate() {
            let Some(Some(clo_obj)) = arg_nodes.get(i).copied() else {
                continue;
            };
            let arg_ty = self.caller.instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                self.typing_env,
                ty::EarlyBinder::bind(a.node.ty(self.body, self.tcx)),
            );
            if let ty::Closure(clo_def, clo_substs) = *arg_ty.kind() {
                self.call_counter += 1;
                let empty = self.arena.empty_path();
                let clo_heap = self.arena.heap(
                    AllocSite {
                        func: self.func,
                        bb,
                        idx: self.call_counter,
                    },
                    empty,
                );
                let clo_dest =
                    self.arena
                        .var_ctx(self.ctx.clone(), self.func, u32::MAX - i as u32, empty);

                // 字段级 Copy: clo_heap.field_j ⊇ upvar_value_j
                for (j, upvar_loc) in arg_nodes.iter().enumerate() {
                    if let Some(upvar_loc) = upvar_loc {
                        let field_path = self.arena.extend_path(empty, ProjElem::Field(j as u32));
                        if let Some(dst) = self.arena.project(clo_heap, field_path) {
                            self.constraints.add(Constraint::Copy {
                                dst,
                                src: *upvar_loc,
                            });
                        }
                    }
                }

                // Point the closure destination at the heap
                self.constraints.add(Constraint::AddressOf {
                    dst: clo_dest,
                    obj: clo_heap,
                });

                self.pending.push(PendingCall {
                    callee: Some((clo_def, clo_substs)),
                    bb,
                    dest: clo_dest,
                    args: {
                        let mut v: SmallVec<[Option<LocId>; 4]> = SmallVec::new();
                        v.push(Some(clo_obj));
                        v
                    },
                    fresh_heap: clo_heap,
                });
            }
        }

        self.call_counter += 1;
        let empty = self.arena.empty_path();
        let fresh_heap = self.arena.heap(
            AllocSite {
                func: self.func,
                bb,
                idx: self.call_counter,
            },
            empty,
        );

        // Monomorphize the callee type in the caller's context (mirrors the
        // call-graph construction) so generic calls resolve correctly.
        let func_ty = self.caller.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            self.typing_env,
            ty::EarlyBinder::bind(callee.ty(self.body, self.tcx)),
        );

        if let ty::FnDef(def_id, substs) = *func_ty.kind() {
            // Box/Arc/Rc::new: store the boxed aggregate into the fresh heap
            // field-wise, and point `dest` at that heap, so dereferencing any
            // clone reaches the same shared object.
            if ownership::is_box_arc_rc_new(def_id, self.tcx) {
                // The smart pointer always points at the fresh heap, even when
                // the boxed value is a constant operand (`Box::new(0)`).
                self.constraints.add(Constraint::AddressOf {
                    dst: dest,
                    obj: fresh_heap,
                });                // The pointer's *internal* pointer fields hold the heap address.
                // An inlined `Box::into_raw` reads them as `box.0.0` field
                // accesses, so point every field-slot prefix of the pointer's
                // type at the heap to make the raw pointer resolve to the shared
                // object.
                let box_ty = self.body.local_decls[destination.local].ty;
                let box_ty = self.caller.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    self.typing_env,
                    ty::EarlyBinder::bind(box_ty),
                );
                let box_paths = leaf_field_paths(self.tcx, self.typing_env, box_ty, self.arena);
                for p in box_paths {
                    let elems: Vec<ProjElem> = self.arena.path(p).to_vec();
                    let mut prefix = self.arena.empty_path();
                    for e in elems {
                        prefix = self.arena.extend_path(prefix, e);
                        if let Some(dest_field) = self.arena.project(dest, prefix) {
                            self.constraints.add(Constraint::AddressOf {
                                dst: dest_field,
                                obj: fresh_heap,
                            });
                        }
                    }
                }
                if let Some(Some(value)) = arg_nodes.first().copied() {
                    let boxed_ty = self.caller.instantiate_mir_and_normalize_erasing_regions(
                        self.tcx,
                        self.typing_env,
                        ty::EarlyBinder::bind(args[0].node.ty(self.body, self.tcx)),
                    );
                    let paths = leaf_field_paths(self.tcx, self.typing_env, boxed_ty, self.arena);
                    emit_boxed_value(
                        self.arena,
                        self.constraints,
                        dest,
                        fresh_heap,
                        value,
                        &paths,
                    );
                }
                return;
            }

            // `Box::into_raw(b) -> *mut T`: the result points to the box's
            // pointee. Model directly so the raw pointer resolves to the shared
            // heap without descending into the std chain.
            if ownership::is_box_into_raw(def_id, self.tcx) {
                if let Some(Some(arg)) = arg_nodes.first().copied() {
                    self.constraints.add(Constraint::Copy {
                        dst: dest,
                        src: arg,
                    });
                }
                return;
            }

            let nodes = CallNodes {
                dest,
                args: arg_nodes,
                fresh_heap,
            };
            if registry.try_specialized(self.tcx, def_id, substs, &nodes, self.constraints) {
                return;
            }
            // Analyzable-or-not is decided by the driver; record for binding.
            self.pending.push(PendingCall {
                callee: Some((def_id, substs)),
                bb,
                dest: nodes.dest,
                args: nodes.args,
                fresh_heap: nodes.fresh_heap,
            });
        } else {
            // Indirect call (fn pointer / dynamic dispatch).
            self.pending.push(PendingCall {
                callee: None,
                bb,
                dest,
                args: arg_nodes,
                fresh_heap,
            });
        }
    }
}

#[cfg(test)]
mod place_tests {
    use super::*;
    use crate::memory::pta::constraint::{Constraint, ConstraintSet};
    use crate::memory::pta::loc::{LocArena, ProjElem};
    use crate::memory::pta::solver::Solver;

    fn mk<'a>(
        arena: &'a mut LocArena,
        cs: &'a mut ConstraintSet,
        next_temp: &'a mut u32,
    ) -> PlaceWalk<'a> {
        PlaceWalk::new(arena, cs, /*func*/ 0, next_temp)
    }

    #[test]
    fn ref_of_field_through_deref_is_object_field() {
        // _1 (self) = &O ; r = &(*_1).0  ⇒ pts(r) = { O·0 }.
        let mut arena = LocArena::default();
        let mut cs = ConstraintSet::default();
        let empty = arena.empty_path();
        let f0 = arena.extend_path(empty, ProjElem::Field(0));
        let o = arena.heap(
            crate::memory::pta::loc::AllocSite {
                func: 0,
                bb: 0,
                idx: 0,
            },
            empty,
        );
        let v1 = arena.var_ctx(crate::memory::pta::context::Context::empty(), 0, 1, empty);
        cs.add(Constraint::AddressOf { dst: v1, obj: o }); // self = &O

        let mut next_temp = 1_000_000u32;
        let r = {
            let mut w = mk(&mut arena, &mut cs, &mut next_temp);
            w.place_addr(1, &[ProjKind::Deref, ProjKind::Field(0)])
        };

        let o_f0 = arena.heap(
            crate::memory::pta::loc::AllocSite {
                func: 0,
                bb: 0,
                idx: 0,
            },
            f0,
        );
        let pts = Solver::new(0).solve(&cs, &mut arena);
        assert!(pts.points_to(r).contains(&o_f0));
    }

    #[test]
    fn boxed_value_stores_fields_into_heap_and_points_dest_at_it() {
        use crate::memory::pta::loc::AllocSite;
        let mut arena = LocArena::default();
        let mut cs = ConstraintSet::default();
        let empty = arena.empty_path();
        let f0 = arena.extend_path(empty, ProjElem::Field(0));

        // value = the aggregate being boxed; its field .0 holds a lock object L.
        let value = arena.var(0, 5, empty);
        let value_f0 = arena.var(0, 5, f0);
        let lock = arena.heap(
            AllocSite {
                func: 0,
                bb: 1,
                idx: 1,
            },
            empty,
        );
        cs.add(Constraint::AddressOf {
            dst: value_f0,
            obj: lock,
        }); // value.0 = &L

        let dest = arena.var(0, 6, empty); // the Arc local
        let heap = arena.heap(
            AllocSite {
                func: 0,
                bb: 2,
                idx: 1,
            },
            empty,
        ); // H_arc

        // leaf paths for a 1-field aggregate: [.0]
        super::emit_boxed_value(&mut arena, &mut cs, dest, heap, value, &[f0]);

        let heap_f0 = arena.heap(
            AllocSite {
                func: 0,
                bb: 2,
                idx: 1,
            },
            f0,
        );
        let pts = Solver::new(0).solve(&cs, &mut arena);
        // dest points at the heap, and heap.0 carries the lock (shared content).
        assert!(pts.points_to(dest).contains(&heap));
        assert!(pts.points_to(heap_f0).contains(&lock));
    }

    #[test]
    fn closure_environment_has_field_level_upvars() {
        // Test that closure environment heap has field-level upvar storage.
        // This verifies the fix for the 6-lock bug where closures weren't
        // properly modeling struct field access through captured upvars.
        use crate::memory::pta::loc::AllocSite;
        use crate::memory::pta::solver::Solver;

        let mut arena = LocArena::default();
        let mut cs = ConstraintSet::default();
        let empty = arena.empty_path();

        // Create a struct's heap with 3 fields (simulating MyStruct { mu, rw1, rw2 })
        let _struct_heap = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 0,
            },
            empty,
        );
        let f0 = arena.extend_path(empty, ProjElem::Field(0)); // mu field
        let f1 = arena.extend_path(empty, ProjElem::Field(1)); // rw1 field
        let f2 = arena.extend_path(empty, ProjElem::Field(2)); // rw2 field

        let struct_f0 = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 0,
            },
            f0,
        );
        let struct_f1 = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 0,
            },
            f1,
        );
        let struct_f2 = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 0,
            },
            f2,
        );

        // Create 3 lock objects (one for each field)
        let lock0 = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 1,
            },
            empty,
        );
        let lock1 = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 2,
            },
            empty,
        );
        let lock2 = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 3,
            },
            empty,
        );

        // Struct fields point to locks via AddressOf
        cs.add(Constraint::AddressOf {
            dst: struct_f0,
            obj: lock0,
        });
        cs.add(Constraint::AddressOf {
            dst: struct_f1,
            obj: lock1,
        });
        cs.add(Constraint::AddressOf {
            dst: struct_f2,
            obj: lock2,
        });

        // Create closure environment heap with 3 fields
        let _clo_heap = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 4,
            },
            empty,
        );
        let clo_f0 = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 4,
            },
            f0,
        );
        let clo_f1 = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 4,
            },
            f1,
        );
        let clo_f2 = arena.heap(
            AllocSite {
                func: 0,
                bb: 0,
                idx: 4,
            },
            f2,
        );

        // Closure captures struct: clo_heap.field_i ⊇ struct_heap.field_i
        // This is the key constraint that was missing before the fix
        cs.add(Constraint::Copy {
            dst: clo_f0,
            src: struct_f0,
        });
        cs.add(Constraint::Copy {
            dst: clo_f1,
            src: struct_f1,
        });
        cs.add(Constraint::Copy {
            dst: clo_f2,
            src: struct_f2,
        });

        let pts = Solver::new(0).solve(&cs, &mut arena);

        // Verify: closure's field 0 points to lock0 (through struct_f0)
        assert!(
            pts.points_to(clo_f0).contains(&lock0),
            "closure field 0 should point to lock0 (struct's mu)"
        );

        // Verify: closure's field 1 points to lock1
        assert!(
            pts.points_to(clo_f1).contains(&lock1),
            "closure field 1 should point to lock1 (struct's rw1)"
        );

        // Verify: closure's field 2 points to lock2
        assert!(
            pts.points_to(clo_f2).contains(&lock2),
            "closure field 2 should point to lock2 (struct's rw2)"
        );

        // All fields should point to DISTINCT locks (not the same)
        // This is the key property that fixes the 6-lock bug
        let pts_to_f0: std::collections::HashSet<_> =
            pts.points_to(clo_f0).iter().copied().collect();
        let pts_to_f1: std::collections::HashSet<_> =
            pts.points_to(clo_f1).iter().copied().collect();
        let pts_to_f2: std::collections::HashSet<_> =
            pts.points_to(clo_f2).iter().copied().collect();

        assert!(
            pts_to_f0.is_disjoint(&pts_to_f1),
            "closure fields should point to different locks"
        );
        assert!(
            pts_to_f0.is_disjoint(&pts_to_f2),
            "closure fields should point to different locks"
        );
        assert!(
            pts_to_f1.is_disjoint(&pts_to_f2),
            "closure fields should point to different locks"
        );
    }
}
