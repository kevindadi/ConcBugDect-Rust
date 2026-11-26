//! Builds and solves pointer-analysis constraints for reachable functions.
//! `k` selects call-site sensitivity; `k = 0` is context-insensitive.
//! It does not lower MIR to Petri-net places.

extern crate rustc_middle;

use std::collections::VecDeque;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Instance, InstanceKind, TyCtxt, TypingEnv};
use smallvec::SmallVec;

use super::builder::{PendingCall, build_body};
use super::constraint::{Constraint, ConstraintSet};
use super::context::{CallSite, Context, ContextPolicy, KCallSite};
use super::interproc::FuncMap;
use super::loc::{AbstractLoc, CiKey, FieldPath, LocArena, LocId, ProjElem};
use super::model::{CallNodes, ModelRegistry};
use super::result::PointsToResult;
use super::solver::Solver;

/// Upper bound on closure environment fields eagerly bound per closure. Only
/// fields that were actually captured have heap entries; unused slots get empty
/// copies (no-ops), so a generous cap is harmless.
const MAX_UPVAR_FIELDS: u32 = 32;

pub struct PointerAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
    arena: LocArena,
    constraints: ConstraintSet,
    funcs: FuncMap<'tcx>,
    registry: ModelRegistry,
    policy: KCallSite,
    /// `(instance, context)` pairs already translated.
    built: FxHashSet<(Instance<'tcx>, Context)>,
    /// Proven-constant integer arguments per `(callee, context)`, seeded from
    /// each call site. Contexts are call-site keyed (k-CFA), so all calls that
    /// share an entry agree on their constant arguments; disagreements are
    /// merged to `None` (dynamic) by [`Self::record_param_consts`].
    param_values: FxHashMap<(Instance<'tcx>, Context), SmallVec<[Option<u64>; 4]>>,
    /// Distinct proven-constant argument vectors observed at the
    /// call sites that resolved to each callee instance.
    call_arg_consts: FxHashMap<Instance<'tcx>, Vec<SmallVec<[Option<u64>; 4]>>>,
    /// Proven-constant argument vectors of each concrete call site,
    /// keyed by `(caller instance, basic block)`.
    call_site_consts: FxHashMap<(Instance<'tcx>, u32), Vec<SmallVec<[Option<u64>; 4]>>>,
    /// Closure DefId → def-site environment heaps (from each construction site).
    closure_envs: FxHashMap<DefId, SmallVec<[LocId; 2]>>,
    /// Closure DefId → captured environment field paths (base slots + nested
    /// leaf paths of aggregate upvars).
    closure_env_paths: FxHashMap<DefId, SmallVec<[FieldPath; 16]>>,
    /// Closure instances built under a context, awaiting env binding after the
    /// main build loop (the capturing function may be built later in the queue).
    built_closures: Vec<(Instance<'tcx>, Context, u32)>,
    /// Monotonic counter for temporary loc ids used by interprocedural binding.
    temp_counter: u32,
    /// Reverse value-flow edges `src -> dst`: a value at `src` flows to `dst`
    /// through `Copy` (moves/copies) or is stored into `dst` (a pointee of a
    /// `Store` address). Ownership-insensitive: moves carry the value just like
    /// copies, since the Petri net (not Rust move semantics) drives control
    /// flow. Used by [`Self::stored_into`] to match a value (e.g. the result of
    /// `Condvar::new()`) to the references that point at its heap slot.
    value_flow_succ: FxHashMap<LocId, FxHashSet<LocId>>,
}

impl<'tcx> PointerAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self::with_k(tcx, 0)
    }

    /// Create an analysis with call-site sensitivity depth `k` (`0` = context
    /// insensitive, `1` = last call site, etc.).
    pub fn with_k(tcx: TyCtxt<'tcx>, k: usize) -> Self {
        Self {
            tcx,
            arena: LocArena::default(),
            constraints: ConstraintSet::default(),
            funcs: FuncMap::default(),
            registry: ModelRegistry::builtin(),
            policy: KCallSite::new(k),
            built: FxHashSet::default(),
            param_values: FxHashMap::default(),
            call_arg_consts: FxHashMap::default(),
            call_site_consts: FxHashMap::default(),
            closure_envs: FxHashMap::default(),
            closure_env_paths: FxHashMap::default(),
            built_closures: Vec::new(),
            temp_counter: 1_000_000,
            value_flow_succ: FxHashMap::default(),
        }
    }

    /// Mutable access to the model registry for registering extra models.
    pub fn registry_mut(&mut self) -> &mut ModelRegistry {
        &mut self.registry
    }

    /// Build constraints for every function reachable by direct calls from
    /// `roots` (entered under the empty context). Safe to call multiple times;
    /// already-built `(instance, context)` pairs are skipped.
    pub fn build_reachable<I>(&mut self, roots: I)
    where
        I: IntoIterator<Item = Instance<'tcx>>,
    {
        let mut queue: VecDeque<(Instance<'tcx>, Context)> =
            roots.into_iter().map(|i| (i, Context::empty())).collect();
        while let Some((inst, ctx)) = queue.pop_front() {
            if !self.built.insert((inst, ctx.clone())) {
                continue;
            }
            // Only user `Item` instances have safely-materializable MIR;
            // intrinsics / shims / virtual dispatch would ICE in `instance_mir`.
            if !Self::is_user_item(self.tcx, inst) {
                continue;
            }
            let body = self.tcx.instance_mir(inst.def);
            if body.source.promoted.is_some() {
                continue;
            }
            let func = self.funcs.intern(inst);
            log::debug!(
                "[pta-func] f{} = {}",
                func,
                crate::util::format_name(inst.def_id())
            );
            // Value-set index injection: seed the callee's local constants
            // from the proven-constant arguments of the call site that created
            // this context.
            let mut param_consts: FxHashMap<u32, u64> = FxHashMap::default();
            if let Some(vals) = self.param_values.get(&(inst, ctx.clone())) {
                for (i, v) in vals.iter().enumerate() {
                    if let Some(v) = v {
                        param_consts.insert(i as u32 + 1, *v);
                    }
                }
            }
            let pending = build_body(
                self.tcx,
                body,
                func,
                ctx.clone(),
                inst,
                &self.registry,
                &mut self.arena,
                &mut self.constraints,
                &mut self.closure_envs,
                &mut self.closure_env_paths,
                &param_consts,
            );
            if Self::is_closure(self.tcx, inst) {
                self.built_closures.push((inst, ctx.clone(), func));
            }
            for pc in pending {
                self.resolve_pending(inst, func, &ctx, pc, &mut queue);
            }
        }

        // Bind every closure's env param (`_1`) to the environment
        // heap created at its definition site. Without this, upvars captured by
        // a closure are unbound when the closure is built as a whole-program
        // root, so aliasing through the capture (e.g. an `Arc<Mutex>` moved
        // into a spawned thread) is lost. Constraints dedupe, so rebinding on a
        // second `build_reachable` is harmless.
        for (inst, ctx, func) in std::mem::take(&mut self.built_closures) {
            let heaps = self.closure_envs.get(&inst.def_id()).cloned();
            let paths = self.closure_env_paths.get(&inst.def_id()).cloned();
            if let Some(heaps) = heaps {
                let empty = self.arena.empty_path();
                let env_node = self.arena.var_ctx(ctx.clone(), func, 1, empty);
                let is_coroutine = self.tcx.is_coroutine(inst.def_id());
                for heap in heaps {
                    if is_coroutine {
                        // Async-fn coroutine: `_1` is `Pin<&mut State>` and the
                        // captured upvars are read through the state pointer
                        // `_1.0` (deref → `(*_1.0).variant#N.k`), not through
                        // `_1.field_i` like a closure. Point the state pointer
                        // `_1.0` at the state heap where the upvars were stored
                        // by the coroutine aggregate.
                        let state_ptr_path = self.arena.extend_path(empty, ProjElem::Field(0));
                        let state_ptr = self.arena.var_ctx(ctx.clone(), func, 1, state_ptr_path);
                        self.constraints.add(Constraint::AddressOf {
                            dst: state_ptr,
                            obj: heap,
                        });
                        continue;
                    }
                    self.constraints.add(Constraint::AddressOf {
                        dst: env_node,
                        obj: heap,
                    });
                    // Bind the base upvar slots (`_1.field_i`); the MAX probing
                    // covers every plausible field index, not just captured ones.
                    for i in 0..MAX_UPVAR_FIELDS {
                        let field_path = self.arena.extend_path(empty, ProjElem::Field(i as u32));
                        let env_field = self.arena.var_ctx(ctx.clone(), func, 1, field_path);
                        if let Some(heap_field) = self.arena.project(heap, field_path) {
                            self.constraints.add(Constraint::Copy {
                                dst: env_field,
                                src: heap_field,
                            });
                        }
                    }
                    // Nested leaf paths of aggregate upvars (e.g. `SharedPtr`
                    // copied by value) so `_1.0.field_0` keeps its raw-pointer
                    // value.
                    if let Some(paths) = &paths {
                        for &p in paths {
                            if self.arena.path(p).is_empty() {
                                continue;
                            }
                            let env_field = self.arena.var_ctx(ctx.clone(), func, 1, p);
                            if let Some(heap_field) = self.arena.project(heap, p) {
                                self.constraints.add(Constraint::Copy {
                                    dst: env_field,
                                    src: heap_field,
                                });
                            }
                        }
                    }
                }
            }
        }
    }

    /// Whether `inst` is a closure (or coroutine) instance whose body reads its
    /// captured upvars through the environment param.
    fn is_closure(tcx: TyCtxt<'tcx>, inst: Instance<'tcx>) -> bool {
        matches!(inst.def, InstanceKind::Item(_)) && tcx.is_closure_like(inst.def_id())
    }

    fn resolve_pending(
        &mut self,
        caller: Instance<'tcx>,
        caller_func: u32,
        caller_ctx: &Context,
        pc: PendingCall<'tcx>,
        queue: &mut VecDeque<(Instance<'tcx>, Context)>,
    ) {
        if let Some((def_id, substs)) = pc.callee {
            // Higher-order `Option` adapters called with a *fn item*
            // (`FnDef`) as the mapping function. std's adapter body invokes
            // the function through the `FnOnce::call_once` shim, which is not
            // a user item: the analysis falls back to the unknown model, the
            // fn item's parameters stay unbound and its receiver point set is
            // empty. Bind the fn item's first parameter to the option payload
            // directly and queue its body instead of analyzing the adapter.
            if let Some(is_map_or) = Self::option_adapter_fn_item(self.tcx, def_id, substs) {
                if let Some(Some(option)) = pc.args.first().copied() {
                    let empty = self.arena.empty_path();
                    let payload_path = self.arena.extend_path(empty, ProjElem::Field(0));
                    if let Some(payload) = self.arena.project(option, payload_path) {
                        if let Some((callee, body)) = self.resolve_fn_item(self.tcx, caller, substs)
                        {
                            if body.arg_count >= 1 {
                                let site = CallSite::new(caller_func, pc.bb);
                                let callee_ctx = self.policy.extend(caller_ctx.clone(), site);
                                // Reuse the normal interprocedural binder with the
                                // adapter's `self` replaced by the payload: the fn
                                // item's `_1` receives the option payload, field
                                // expansion included, and `dest ⊇ callee._0`.
                                let synthetic = PendingCall {
                                    callee: None,
                                    bb: pc.bb,
                                    dest: pc.dest,
                                    args: smallvec::smallvec![Some(payload)],
                                    fresh_heap: pc.fresh_heap,
                                    temps: pc.temps.clone(),
                                    arg_consts: smallvec::smallvec![None],
                                };
                                self.bind_callee(
                                    callee,
                                    callee_ctx.clone(),
                                    body.arg_count,
                                    &synthetic,
                                );
                                // `map_or`'s `default` argument flows into the
                                // result on the `None` branch (the adapter body
                                // is not analyzed here).
                                if is_map_or {
                                    if let Some(Some(default)) = pc.args.get(1).copied() {
                                        self.constraints.add(Constraint::Copy {
                                            dst: pc.dest,
                                            src: default,
                                        });
                                    }
                                }
                                if !self.built.contains(&(callee, callee_ctx.clone())) {
                                    queue.push_back((callee, callee_ctx));
                                }
                                return;
                            }
                        }
                    }
                }
            }
            // Use the caller's typing environment to resolve the callee instance.
            // For closures, substs contains captured upvars from the caller's scope,
            // so we resolve them in the caller's environment.
            let typing_env = TypingEnv::post_analysis(self.tcx, caller.def_id());
            let resolved = Instance::try_resolve(self.tcx, typing_env, def_id, substs)
                .ok()
                .flatten();
            if let Some(callee) = resolved {
                if Self::is_user_item(self.tcx, callee) {
                    let body = self.tcx.instance_mir(callee.def);
                    if body.source.promoted.is_none() {
                        // The call site carries a fingerprint of its
                        // proven-constant arguments. Two calls at the same
                        // block with different constants (e.g. `account(from)`
                        // / `account(to)` from opposite transfer directions)
                        // then get distinct callee contexts even after the
                        // k=1 truncation drops the caller context.
                        let site = CallSite::with_args(caller_func, pc.bb, &pc.arg_consts);
                        let callee_ctx = self.policy.extend(caller_ctx.clone(), site);
                        self.record_param_consts(callee, &callee_ctx, &pc);
                        self.record_call_arg_consts(caller, callee, pc.bb, &pc.arg_consts);
                        self.bind_callee(callee, callee_ctx.clone(), body.arg_count, &pc);
                        if !self.built.contains(&(callee, callee_ctx.clone())) {
                            queue.push_back((callee, callee_ctx));
                        }
                        return;
                    }
                }
            }
        }
        // Indirect, unresolved, intrinsic/shim, or no MIR: conservative model.
        self.apply_unknown(pc);
    }

    /// Whether `inst` is a user `Item` with available MIR that can be safely
    /// materialized by `instance_mir`. Intrinsics, compiler shims (drop/clone
    /// glue, fn-ptr/closure shims), and virtual dispatch are excluded — they
    /// either ICE in `instance_mir` or carry no user pointer flow — and are
    /// handled by the conservative call model instead.
    fn is_user_item(tcx: TyCtxt<'tcx>, inst: Instance<'tcx>) -> bool {
        matches!(inst.def, InstanceKind::Item(_)) && tcx.is_mir_available(inst.def_id())
    }

    /// Recognize `Option::map_or` / `map` / `and_then` when the generic
    /// function parameter `F` is a fn item (`FnDef`).
    ///
    /// Returns `Some(is_map_or)` for the adapters we bind at the call site.
    /// The adapter's own std body is skipped: it invokes `F` through the
    /// `FnOnce::call_once` shim, which the engine cannot materialize (see the call
    /// site in [`Self::resolve_pending`]). Closure arguments are *not*
    /// handled here — they keep the previous path through std's body.
    fn option_adapter_fn_item(
        tcx: TyCtxt<'tcx>,
        def_id: rustc_hir::def_id::DefId,
        substs: rustc_middle::ty::GenericArgsRef<'tcx>,
    ) -> Option<bool> {
        use rustc_middle::ty::{GenericArgKind, TyKind};
        let is_map_or = option_adapter_kind(&tcx.def_path_str(def_id))?;
        // `Option::<T>::map_or::<U, F>` has substs `[T, U, F]`; `F` is last.
        let GenericArgKind::Type(f_ty) = substs.last()?.kind() else {
            return None;
        };
        matches!(*f_ty.kind(), TyKind::FnDef(..)).then_some(is_map_or)
    }

    /// Resolve the fn item stored in the adapter's last generic argument to a
    /// user-code instance with MIR.
    fn resolve_fn_item(
        &self,
        tcx: TyCtxt<'tcx>,
        caller: Instance<'tcx>,
        substs: rustc_middle::ty::GenericArgsRef<'tcx>,
    ) -> Option<(Instance<'tcx>, &'tcx rustc_middle::mir::Body<'tcx>)> {
        use rustc_middle::ty::{GenericArgKind, TyKind};
        let GenericArgKind::Type(f_ty) = substs.last()?.kind() else {
            return None;
        };
        let TyKind::FnDef(fn_def_id, fn_args) = *f_ty.kind() else {
            return None;
        };
        let fn_args = crate::util::fn_def_args(tcx, fn_args);
        let typing_env = TypingEnv::post_analysis(tcx, caller.def_id());
        let callee = Instance::try_resolve(tcx, typing_env, fn_def_id, fn_args)
            .ok()
            .flatten()?;
        if !Self::is_user_item(tcx, callee) {
            return None;
        }
        let body = tcx.instance_mir(callee.def);
        if body.source.promoted.is_some() {
            return None;
        }
        Some((callee, body))
    }

    /// Emit interprocedural binding constraints between a call site and an
    /// analyzable callee (`param ⊇ arg`, `dest ⊇ callee._0`). Callee nodes are
    /// created under `callee_ctx`.
    fn bind_callee(
        &mut self,
        callee: Instance<'tcx>,
        callee_ctx: Context,
        arg_count: usize,
        pc: &PendingCall<'tcx>,
    ) {
        let callee_func = self.funcs.intern(callee);
        let body = self.tcx.instance_mir(callee.def);
        let typing_env = TypingEnv::post_analysis(self.tcx, callee.def_id());
        let empty = self.arena.empty_path();

        // return: dest ⊇ callee._0
        let ret = self
            .arena
            .var_ctx(callee_ctx.clone(), callee_func, 0, empty);
        self.constraints.add(Constraint::Copy {
            dst: pc.dest,
            src: ret,
        });

        // Field-expand the return value: `dest·p ⊇ callee._0·p` for every leaf
        // path of the return type. Without this, aggregate returns (slice/vec
        // iterators, `&[T]` fat pointers, `Option`, tuples) only copy their
        // base node, so the pointer fields a callee wrote are lost in the
        // caller. Parameters have always been field-expanded below; returns
        // were the missing half of the `stored_into`/load path composition.
        let ret_ty = body.local_decls[rustc_middle::mir::Local::from_usize(0)].ty;
        let ret_ty = callee.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            typing_env,
            rustc_middle::ty::EarlyBinder::bind(self.tcx, ret_ty),
        );
        let ret_paths = crate::analysis::memory::pta::typeutil::leaf_field_paths(
            self.tcx,
            typing_env,
            ret_ty,
            &mut self.arena,
        );
        if log::log_enabled!(log::Level::Debug) {
            log::debug!(
                "[pta-bind] -> f{} ({}) bb{} return {:?} dest={} ret={} paths={}",
                callee_func,
                crate::util::format_name(callee.def_id()),
                pc.bb,
                ret_ty,
                pc.dest,
                ret,
                ret_paths.len()
            );
        }
        for p in ret_paths {
            if self.arena.path(p).is_empty() {
                continue;
            }
            if let (Some(dst_field), Some(src_field)) =
                (self.arena.project(pc.dest, p), self.arena.project(ret, p))
            {
                self.constraints.add(Constraint::Copy {
                    dst: dst_field,
                    src: src_field,
                });
            }
        }

        // params: callee._i ⊇ arg_i, plus field-wise expansion for aggregate params.
        for i in 1..=arg_count {
            let Some(Some(arg)) = pc.args.get(i - 1).copied() else {
                continue;
            };
            let param = self
                .arena
                .var_ctx(callee_ctx.clone(), callee_func, i as u32, empty);
            self.constraints.add(Constraint::Copy {
                dst: param,
                src: arg,
            });

            // Field expansion: for each leaf field path p of the param's type,
            // `param·p ⊇ value-at(arg·p)`. We must project the arg's *pointees*
            // by p and then read the value there (Offset then Load); a plain
            // `Copy` from `arg·p` only reads the arg's own (usually empty) field
            // slot and silently drops by-value aggregate params (e.g. a
            // `SharedPtr(*mut i32)` passed by value into `as_ptr`). For a
            // reference-to-local arg the two readings coincide, so this stays
            // sound for the shared-struct-field patterns too.
            let param_ty = body.local_decls[rustc_middle::mir::Local::from_usize(i)].ty;
            let param_ty = callee.instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                typing_env,
                rustc_middle::ty::EarlyBinder::bind(self.tcx, param_ty),
            );
            let paths = crate::analysis::memory::pta::typeutil::leaf_field_paths(
                self.tcx,
                typing_env,
                param_ty,
                &mut self.arena,
            );
            for p in paths {
                if self.arena.path(p).is_empty() {
                    continue;
                }
                if let Some(pj) = self.arena.project(param, p) {
                    // Pointer/ref arg: the struct is the arg's pointee, so
                    // project the pointees by p and read the value there.
                    let temp = self.fresh_temp_loc();
                    self.constraints.add(Constraint::Offset {
                        dst: temp,
                        src: arg,
                        suffix: p,
                    });
                    self.constraints
                        .add(Constraint::Load { dst: pj, src: temp });
                    // By-value aggregate arg: the struct *is* the arg value, so
                    // its fields live in the arg's own field slots (`arg·p`).
                    // Copy those directly (a no-op when the arg is a reference).
                    if let crate::analysis::memory::pta::loc::AbstractLoc::Var {
                        ctx: actx,
                        func: afunc,
                        base: abase,
                        path: apath,
                    } = self.arena.loc(arg).clone()
                    {
                        if self.arena.path(apath).is_empty() {
                            let arg_field = self.arena.var_ctx(actx, afunc, abase, p);
                            self.constraints.add(Constraint::Copy {
                                dst: pj,
                                src: arg_field,
                            });
                        }
                    }
                }
            }
        }
    }

    fn apply_unknown(&mut self, pc: PendingCall<'tcx>) {
        let nodes = CallNodes {
            dest: pc.dest,
            args: pc.args,
            fresh_heap: pc.fresh_heap,
            temps: pc.temps,
            arg_consts: pc.arg_consts,
            predicate: None,
        };
        self.registry
            .apply_unknown(&nodes, &mut self.arena, &mut self.constraints);
    }

    /// Merge a call site's proven-constant arguments into the param table for
    /// `(callee, context)`. Two calls sharing a context but disagreeing on a
    /// value clear that position (it is dynamic after all).
    fn record_param_consts(
        &mut self,
        callee: Instance<'tcx>,
        callee_ctx: &Context,
        pc: &PendingCall<'tcx>,
    ) {
        let key = (callee, callee_ctx.clone());
        if !self.param_values.contains_key(&key) {
            // First call site for this context: its values are the entry.
            self.param_values.insert(key, pc.arg_consts.clone());
            return;
        }
        let entry = self.param_values.get_mut(&key).expect("checked above");
        if entry.len() < pc.arg_consts.len() {
            entry.resize(pc.arg_consts.len(), None);
        }
        // Any call that cannot prove a position constant, or proves a
        // different value, makes that position dynamic for this context.
        for (i, v) in pc.arg_consts.iter().enumerate() {
            if entry[i] != *v {
                entry[i] = None;
            }
        }
    }

    /// Record a call site's proven-constant argument vector for the callee and
    /// for the `(caller, bb)` site itself.
    fn record_call_arg_consts(
        &mut self,
        caller: Instance<'tcx>,
        callee: Instance<'tcx>,
        bb: u32,
        arg_consts: &SmallVec<[Option<u64>; 4]>,
    ) {
        let per_callee = self.call_arg_consts.entry(callee).or_default();
        if !per_callee
            .iter()
            .any(|v| v.as_slice() == arg_consts.as_slice())
        {
            per_callee.push(arg_consts.clone());
        }
        let per_site = self.call_site_consts.entry((caller, bb)).or_default();
        if !per_site
            .iter()
            .any(|v| v.as_slice() == arg_consts.as_slice())
        {
            per_site.push(arg_consts.clone());
        }
    }

    /// Solve the accumulated constraints and return a query facade.
    pub fn solve(&mut self) -> PointsToResult {
        let pts = Solver::new(self.arena.loc_count()).solve(&self.constraints, &mut self.arena);

        // Build the reverse value-flow graph once from the constraints and the
        // solved relation:
        // - `Copy { dst, src }` carries the value at `src` to `dst` (a move is
        //   treated like a copy — the Petri net, not move semantics, drives
        //   control flow, so a moved value keeps flowing).
        // - `Store { dst, src }` puts `src`'s value into every pointee of
        //   `dst` (the storage location), resolved from the solved points-to.
        let mut value_flow_succ: FxHashMap<LocId, FxHashSet<LocId>> = FxHashMap::default();
        for c in self.constraints.iter() {
            match *c {
                Constraint::Copy { dst, src } => {
                    value_flow_succ.entry(src).or_default().insert(dst);
                }
                Constraint::Store { dst, src } => {
                    for &storage in pts.points_to(dst) {
                        value_flow_succ.entry(src).or_default().insert(storage);
                    }
                }
                _ => {}
            }
        }
        self.value_flow_succ = value_flow_succ;

        PointsToResult::new(pts)
    }

    /// Existing `func` id for an instance, or `None` if it was never built.
    pub fn func_id(&self, instance: Instance<'tcx>) -> Option<u32> {
        self.funcs.get_id(&instance)
    }

    /// All context-qualified node ids for a function-local variable (the local
    /// itself, empty field path), across every calling context that was built.
    /// `local = 0` is the return place; `1..=arg_count` are parameters.
    pub fn var_nodes(&self, instance: Instance<'tcx>, local: u32) -> SmallVec<[LocId; 4]> {
        let mut out = SmallVec::new();
        let Some(func) = self.funcs.get_id(&instance) else {
            return out;
        };
        for (id, loc) in self.arena.iter_locs() {
            if let AbstractLoc::Var {
                func: f,
                base,
                path,
                ..
            } = loc
            {
                if *f == func && *base == local && self.arena.path(*path).is_empty() {
                    out.push(id);
                }
            }
        }
        out
    }

    /// Context-insensitive points-to set for a local: the union over all
    /// contexts, with pointees collapsed to their context-insensitive identity.
    pub fn collapsed_points_to(
        &self,
        result: &PointsToResult,
        instance: Instance<'tcx>,
        local: u32,
    ) -> FxHashSet<CiKey> {
        let mut keys = FxHashSet::default();
        for node in self.var_nodes(instance, local) {
            for &pointee in result.points_to(node) {
                keys.insert(self.arena.ci_key(pointee));
            }
        }
        keys
    }

    /// Sound context-insensitive may-alias: two locals may alias if their
    /// context-collapsed points-to sets share a context-insensitive location.
    pub fn collapsed_may_alias(
        &self,
        result: &PointsToResult,
        a: Instance<'tcx>,
        a_local: u32,
        b: Instance<'tcx>,
        b_local: u32,
    ) -> bool {
        let sa = self.collapsed_points_to(result, a, a_local);
        if sa.is_empty() {
            return false;
        }
        let sb = self.collapsed_points_to(result, b, b_local);
        !sa.is_disjoint(&sb)
    }

    /// Collapsed points-to for a receiver that may carry a single field
    /// projection (an `AliasId.field`), covering every MIR access shape:
    /// - the direct field slot `V_local.field`,
    /// - the offset into every pointee of the base slot, `*V_local.field`.
    ///
    /// The last shape is what resolves closure upvar receivers (`(*env).field`
    /// where `env` points at the captured environment heap) and `&(*self).mu`
    /// receivers to the object stored at the field.
    ///
    /// With a field projection, only the *field-specific* slots/pointees are
    /// emitted. Including the base var slot or the whole base pointee would
    /// make every field of the same base alias each other (e.g. `self.mu1`
    /// aliasing `self.rw1`), collapsing distinct locks into one resource.
    pub fn collapsed_receiver_points_to(
        &mut self,
        result: &PointsToResult,
        instance: Instance<'tcx>,
        local: u32,
        field: Option<u32>,
    ) -> FxHashSet<CiKey> {
        // Legacy single-field view. Full paths go through
        // [`Self::collapsed_receiver_points_to_path`].
        match field {
            Some(f) => {
                let steps = [ProjElem::Field(f)];
                self.collapsed_receiver_points_to_path(result, instance, local, &steps)
            }
            None => {
                let mut keys = FxHashSet::default();
                let Some(func) = self.funcs.get_id(&instance) else {
                    return keys;
                };
                let (base_nodes, base_pointees) = self.receiver_base_nodes(result, func, local);
                for &id in &base_nodes {
                    keys.insert(self.arena.ci_key(id));
                    // A value local (no pointees) has no forward points-to;
                    // its identity is the heap slots it is stored into. Include
                    // those destinations so e.g. a `Condvar::new()` result can
                    // be matched to the `&Condvar` reference inside a spawned
                    // closure that dereferences the shared `Arc`.
                    if result.points_to(id).is_empty() {
                        keys.extend(self.stored_into(id));
                    }
                }
                for &p in &base_pointees {
                    keys.insert(self.arena.ci_key(p));
                }
                if log::log_enabled!(log::Level::Debug) {
                    self.log_receiver_pts(
                        Some(func),
                        local,
                        None,
                        &base_nodes,
                        &base_pointees,
                        &keys,
                    );
                }
                keys
            }
        }
    }

    /// Receiver points-to identity for a *full* projection path.
    ///
    /// The path is the receiver's MIR projection after the base local
    /// (`Deref`/`Field`/`Index`/`ConstIndex`, variant tags merged). It is
    /// evaluated as a place: a leading `Deref` consumes the base local's
    /// pointees, a `Deref` further in consumes the pointees of the current
    /// frontier, and every other element projects the frontier slots. The
    /// resulting slots (and the objects they point to) are the lock/condvar/
    /// atomic identities, so `(*p).a.b` stays distinct from `(*p).a.c` instead
    /// of comparing only the first `Field`.
    pub fn collapsed_receiver_points_to_path(
        &mut self,
        result: &PointsToResult,
        instance: Instance<'tcx>,
        local: u32,
        steps: &[ProjElem],
    ) -> FxHashSet<CiKey> {
        let mut keys = FxHashSet::default();
        let Some(func) = self.funcs.get_id(&instance) else {
            return keys;
        };
        let (base_nodes, base_pointees) = self.receiver_base_nodes(result, func, local);
        keys = self.project_receiver_path(result, &base_nodes, &base_pointees, steps);

        if log::log_enabled!(log::Level::Debug) {
            self.log_receiver_pts(
                Some(func),
                local,
                Some(steps),
                &base_nodes,
                &base_pointees,
                &keys,
            );
        }
        keys
    }

    /// Project a receiver path from a fixed set of base slots and their
    /// pointees. Shared by [`Self::collapsed_receiver_points_to_path`] (every
    /// context unioned) and [`Self::receiver_points_to_path_by_context`] (one
    /// context at a time), so the two queries cannot drift apart.
    fn project_receiver_path(
        &mut self,
        result: &PointsToResult,
        base_nodes: &[LocId],
        base_pointees: &[LocId],
        steps: &[ProjElem],
    ) -> FxHashSet<CiKey> {
        let mut keys = FxHashSet::default();

        // A leading `Deref` means the base local holds the reference; the lock
        // object is in its pointees. Without one, start from both the base
        // slots and their pointees (the legacy over-approximation).
        let mut frontier: Vec<LocId> = Vec::new();
        let mut rest = steps;
        if steps.first() == Some(&ProjElem::Deref) {
            frontier.extend(base_pointees.iter().copied());
            rest = &steps[1..];
        } else {
            frontier.extend(base_nodes.iter().copied());
            frontier.extend(base_pointees.iter().copied());
        }

        let empty = self.arena.empty_path();
        for step in rest {
            let mut next: Vec<LocId> = Vec::new();
            match step {
                ProjElem::Deref => {
                    for &loc in &frontier {
                        next.extend(result.points_to(loc).iter().copied());
                    }
                }
                _ => {
                    let suffix = self.arena.extend_path(empty, *step);
                    for &loc in &frontier {
                        if let Some(projected) = self.arena.project(loc, suffix) {
                            next.push(projected);
                        }
                    }
                }
            }
            next.sort_unstable();
            next.dedup();
            frontier = next;
        }

        for &loc in &frontier {
            keys.insert(self.arena.ci_key(loc));
            // When the projected slot holds a reference, the object it points
            // at is also a possible lock identity.
            keys.extend(result.points_to(loc).iter().map(|&p| self.arena.ci_key(p)));
        }
        keys
    }

    /// Per-context receiver points-to identity for a full projection path
    /// (P3 call-site sensitivity).
    ///
    /// [`Self::collapsed_receiver_points_to_path`] unions every k-CFA context
    /// of the base local into one set. Here each context the local was built
    /// in is walked separately, so two acquisition sites can be compared only
    /// where they coexist in the same call-site context. Contexts in which the
    /// local has no node are simply absent from the result; consumers must
    /// treat "no shared context" as inconclusive, never as disjoint.
    pub fn receiver_points_to_path_by_context(
        &mut self,
        result: &PointsToResult,
        instance: Instance<'tcx>,
        local: u32,
        steps: &[ProjElem],
    ) -> Vec<(Context, FxHashSet<CiKey>)> {
        let Some(func) = self.funcs.get_id(&instance) else {
            return Vec::new();
        };

        // Group the empty-path base slots by context first: the projection walk
        // below needs `&mut self.arena`, so the immutable arena scan must finish
        // before it starts.
        let mut base_by_ctx: FxHashMap<Context, Vec<LocId>> = FxHashMap::default();
        for (id, loc) in self.arena.iter_locs() {
            if let AbstractLoc::Var {
                ctx,
                func: f,
                base,
                path,
            } = loc
            {
                if *f == func && *base == local && self.arena.path(*path).is_empty() {
                    base_by_ctx.entry(ctx.clone()).or_default().push(id);
                }
            }
        }

        let mut out: Vec<(Context, FxHashSet<CiKey>)> = Vec::new();
        for (ctx, base_nodes) in base_by_ctx {
            let mut base_pointees: Vec<LocId> = Vec::new();
            for &id in &base_nodes {
                base_pointees.extend(result.points_to(id).iter().copied());
            }
            let keys = self.project_receiver_path(result, &base_nodes, &base_pointees, steps);
            if log::log_enabled!(log::Level::Debug) {
                let mut rendered: Vec<String> = keys.iter().map(|k| self.fmt_ci_key(k)).collect();
                rendered.sort();
                log::debug!(
                    "[receiver-ctx-pts] func={:?} local={} path={:?} ctx={} keys={:?}",
                    Some(func),
                    local,
                    steps,
                    Self::fmt_context(&ctx),
                    rendered
                );
            }
            out.push((ctx, keys));
        }
        out.sort_by(|(a, _), (b, _)| Self::context_sort_key(a).cmp(&Self::context_sort_key(b)));
        out
    }

    fn context_sort_key(ctx: &Context) -> Vec<(u32, u32, Option<u64>)> {
        ctx.as_slice()
            .iter()
            .map(|s| (s.func, s.bb, s.value))
            .collect()
    }

    fn fmt_context(ctx: &Context) -> String {
        if ctx.is_empty() {
            return "<empty>".to_string();
        }
        ctx.as_slice()
            .iter()
            .map(|s| match s.value {
                Some(v) => format!("{}:{}#{:x}", s.func, s.bb, v),
                None => format!("{}:{}", s.func, s.bb),
            })
            .collect::<Vec<_>>()
            .join(",")
    }

    /// Base variable slots (empty path) of `(func, local)` across all k-CFA
    /// contexts, plus their pointees.
    fn receiver_base_nodes(
        &mut self,
        result: &PointsToResult,
        func: u32,
        local: u32,
    ) -> (Vec<LocId>, Vec<LocId>) {
        let mut base_nodes = Vec::new();
        let mut base_pointees = Vec::new();
        for (id, loc) in self.arena.iter_locs() {
            if let AbstractLoc::Var {
                func: f,
                base,
                path,
                ..
            } = loc
            {
                if *f == func && *base == local && self.arena.path(*path).is_empty() {
                    base_nodes.push(id);
                    for &p in result.points_to(id) {
                        base_pointees.push(p);
                    }
                }
            }
        }
        (base_nodes, base_pointees)
    }

    fn log_receiver_pts(
        &self,
        func: Option<u32>,
        local: u32,
        steps: Option<&[ProjElem]>,
        base_nodes: &[LocId],
        base_pointees: &[LocId],
        keys: &FxHashSet<CiKey>,
    ) {
        let mut rendered: Vec<String> = keys.iter().map(|k| self.fmt_ci_key(k)).collect();
        rendered.sort();
        let path = steps
            .map(|s| {
                s.iter()
                    .map(|e| match e {
                        ProjElem::Field(f) => format!(".{}", f),
                        ProjElem::Deref => ".*".to_string(),
                        ProjElem::Index => "[*]".to_string(),
                        ProjElem::ConstIndex(i) => format!("[{}]", i),
                        ProjElem::Predicate { field, value } => {
                            format!("[{}={}]", self.fmt_path(*field), value)
                        }
                    })
                    .collect::<String>()
            })
            .unwrap_or_default();
        log::debug!(
            "[receiver-pts] func={:?} local={} path={:?} base_nodes={} base_pointees={} keys={:?}",
            func,
            local,
            path,
            base_nodes.len(),
            base_pointees.len(),
            rendered
        );
    }

    /// Render a context-insensitive location key for diagnostics.
    fn fmt_ci_key(&self, key: &CiKey) -> String {
        match key {
            CiKey::Var { func, base, path } => {
                format!("V(f{}:_{}){}", func, base, self.fmt_path(*path))
            }
            CiKey::Heap { site, path } => format!(
                "H(f{}:bb{}#{}){}",
                site.func,
                site.bb,
                site.idx,
                self.fmt_path(*path)
            ),
            CiKey::Global { def_index, path } => {
                format!("G({}){}", def_index, self.fmt_path(*path))
            }
        }
    }

    /// Locations a value at `start` (transitively, through copies/moves) is
    /// stored into, collapsed to context-insensitive keys. Backed by
    /// [`Self::value_flow_succ`]; ownership-insensitive (moves == copies).
    fn stored_into(&mut self, start: LocId) -> FxHashSet<CiKey> {
        let mut keys = FxHashSet::default();
        let empty = self.arena.empty_path();
        let mut visited: FxHashSet<(LocId, FieldPath)> = FxHashSet::default();
        let mut stack = vec![(start, empty)];
        visited.insert((start, empty));
        while let Some((node, rel)) = stack.pop() {
            let Some(succs) = self.value_flow_succ.get(&node) else {
                continue;
            };
            let succs: Vec<LocId> = succs.iter().copied().collect();
            for succ in succs {
                // The value at `node` flows to `succ`. When `node` is the
                // aggregate that contains the tracked value, the field offset
                // `rel` travels with it.
                let Some(projected) = self.arena.project(succ, rel) else {
                    continue;
                };
                keys.insert(self.arena.ci_key(projected));
                // Follow the value slot itself (plain copy/move chains).
                let empty = self.arena.empty_path();
                if visited.insert((projected, empty)) {
                    stack.push((projected, empty));
                }
                // Follow the containing aggregate as well: a struct/tuple that
                // holds the tracked field may itself be moved into a heap
                // allocation (e.g. `Arc::new(CondPair { cvar,.. })`). Without
                // this, the field slot in the constructing frame and the
                // projected heap slot seen through `&self.cvar` never meet.
                let (base, path) = self.arena.base_and_path(projected);
                if visited.insert((base, path)) {
                    stack.push((base, path));
                }
            }
        }
        keys
    }

    /// May-alias for receivers that may carry a single field projection.
    ///
    /// `None` means the query is inconclusive: at least one receiver has an
    /// empty points-to set. For a lock receiver that emptiness means the
    /// analysis could not resolve the lock object (the program would be
    /// dereferencing nothing otherwise), *not* that the two objects are
    /// provably distinct. Reporting it as "no alias" was a
    /// recall-gap bug: two access paths to the same lock that both lost
    /// their target were split into separate resource places even under the
    /// conservative policy, so the net never saw the two acquisitions
    /// contend for one lock.
    ///
    /// `Some(true)` = the sets intersect, `Some(false)` = both are non-empty
    /// and disjoint. The caller decides what `None` means under its policy
    /// ([`crate::config::AliasUnknownPolicy`]).
    pub fn collapsed_may_alias_receiver(
        &mut self,
        result: &PointsToResult,
        a: Instance<'tcx>,
        a_local: u32,
        a_field: Option<u32>,
        b: Instance<'tcx>,
        b_local: u32,
        b_field: Option<u32>,
    ) -> Option<bool> {
        let sa = self.collapsed_receiver_points_to(result, a, a_local, a_field);
        let sb = self.collapsed_receiver_points_to(result, b, b_local, b_field);
        Self::classify_receiver_alias_sets(&sa, &sb)
    }

    /// May-alias for receivers carrying a full projection path (P1/P2).
    ///
    /// Unlike [`Self::collapsed_may_alias_receiver`], both receivers are
    /// evaluated at their complete paths, and two identity keys may overlap
    /// even when they are not syntactically equal: a dynamic `Index` in one
    /// path denotes *any* element, so it overlaps a concrete `ConstIndex(i)`
    /// in the other. Treating them as disjoint would be unsound (it would
    /// split `xs[*]` from `xs[0]`). Field chains remain disjoint unless fully
    /// equal, which preserves the legacy first-field discrimination.
    pub fn collapsed_may_alias_receiver_path(
        &mut self,
        result: &PointsToResult,
        a: Instance<'tcx>,
        a_local: u32,
        a_steps: &[ProjElem],
        b: Instance<'tcx>,
        b_local: u32,
        b_steps: &[ProjElem],
    ) -> Option<bool> {
        let sa = self.collapsed_receiver_points_to_path(result, a, a_local, a_steps);
        let sb = self.collapsed_receiver_points_to_path(result, b, b_local, b_steps);
        self.classify_receiver_alias_paths(&sa, &sb)
    }

    /// Path-aware counterpart of [`Self::classify_receiver_alias_sets`]:
    /// `None` when either side is unresolved (empty), otherwise whether any
    /// pair of identity keys may denote the same slot.
    pub(crate) fn classify_receiver_alias_paths(
        &self,
        a: &FxHashSet<CiKey>,
        b: &FxHashSet<CiKey>,
    ) -> Option<bool> {
        if a.is_empty() || b.is_empty() {
            return None;
        }
        Some(
            a.iter()
                .any(|ka| b.iter().any(|kb| self.ci_keys_may_overlap(ka, kb))),
        )
    }

    /// Context-aware may-alias verdict for two receivers evaluated by
    /// [`Self::receiver_points_to_path_by_context`].
    ///
    /// Only call-site contexts present on *both* sides are compared — those
    /// are the executions in which both acquisition sites run. `Some(true)`
    /// when any shared context's key sets overlap; `Some(false)` when every
    /// shared context has both sets resolved and disjoint; `None` when there
    /// is no shared context or any shared context is unresolved. `None` means
    /// inconclusive, never distinct: the caller applies its unknown policy.
    pub fn classify_receiver_alias_by_context(
        &self,
        a: &[(Context, FxHashSet<CiKey>)],
        b: &[(Context, FxHashSet<CiKey>)],
    ) -> Option<bool> {
        Self::classify_by_context(a, b, |ka, kb| self.ci_keys_may_overlap(ka, kb))
    }

    /// Set-level core of [`Self::classify_receiver_alias_by_context`], kept
    /// generic so the context walk is unit-testable without a `TyCtxt`.
    pub(crate) fn classify_by_context<K, F>(
        a: &[(Context, FxHashSet<K>)],
        b: &[(Context, FxHashSet<K>)],
        mut may_overlap: F,
    ) -> Option<bool>
    where
        K: Eq + std::hash::Hash,
        F: FnMut(&K, &K) -> bool,
    {
        let b_by_ctx: FxHashMap<&Context, &FxHashSet<K>> =
            b.iter().map(|(ctx, set)| (ctx, set)).collect();
        // Is there a call-site context in which both receivers actually
        // resolve? The empty context is the context-insensitive fallback
        // instance the driver builds for every call-graph node; its receivers
        // are merged (no predicate/base split), so it can carry overlap that
        // the precise executions do not have. When a precise shared context
        // resolves both sides, the fallback context is not evidence about
        // these particular executions.
        let precise_exists = a.iter().any(|(ctx, sa)| {
            !ctx.is_empty() && !sa.is_empty() && b_by_ctx.get(ctx).is_some_and(|sb| !sb.is_empty())
        });
        let mut shared = 0usize;
        let mut unresolved = false;
        for (ctx, sa) in a {
            let Some(sb) = b_by_ctx.get(ctx) else {
                continue;
            };
            if ctx.is_empty() && precise_exists {
                continue;
            }
            // A context where *neither* receiver resolves carries no alias
            // evidence at all (typically the context-insensitive fallback
            // instance of a function, which the driver builds for every
            // call-graph node). Treating it as "unresolved" would discard the
            // precise per-context verdicts below; skipping it keeps the
            // verdict based on the executions where at least one side is
            // actually known.
            if sa.is_empty() && sb.is_empty() {
                continue;
            }
            shared += 1;
            if sa.is_empty() || sb.is_empty() {
                unresolved = true;
                continue;
            }
            if sa.iter().any(|ka| sb.iter().any(|kb| may_overlap(ka, kb))) {
                return Some(true);
            }
        }
        if shared == 0 || unresolved {
            None
        } else {
            Some(false)
        }
    }

    /// Whether two context-insensitive keys may denote the same slot. Identity
    /// components (variant + func/base/site/def) must match; projection paths
    /// must then be pairwise compatible, with `Index` acting as a wildcard for
    /// `ConstIndex(_)`. Paths of different lengths are disjoint slots.
    fn ci_keys_may_overlap(&self, a: &CiKey, b: &CiKey) -> bool {
        match (a, b) {
            (
                CiKey::Var {
                    func: fa,
                    base: ba,
                    path: pa,
                },
                CiKey::Var {
                    func: fb,
                    base: bb,
                    path: pb,
                },
            ) => fa == fb && ba == bb && self.paths_may_overlap(*pa, *pb),
            (CiKey::Heap { site: sa, path: pa }, CiKey::Heap { site: sb, path: pb }) => {
                sa == sb && self.paths_may_overlap(*pa, *pb)
            }
            (
                CiKey::Global {
                    def_index: da,
                    path: pa,
                },
                CiKey::Global {
                    def_index: db,
                    path: pb,
                },
            ) => da == db && self.paths_may_overlap(*pa, *pb),
            _ => false,
        }
    }

    fn paths_may_overlap(&self, a: FieldPath, b: FieldPath) -> bool {
        crate::analysis::memory::pta::loc::proj_paths_may_overlap(
            self.arena.path(a),
            self.arena.path(b),
        )
    }

    /// Classify two receiver points-to sets into the tri-state the alias
    /// policy consumes. Split out so the "empty means unknown, not disjoint"
    /// rule is unit-testable without a `TyCtxt`.
    pub(crate) fn classify_receiver_alias_sets<T: Eq + std::hash::Hash>(
        a: &FxHashSet<T>,
        b: &FxHashSet<T>,
    ) -> Option<bool> {
        if a.is_empty() || b.is_empty() {
            return None;
        }
        Some(!a.is_disjoint(b))
    }

    /// Whether `pointer` may point to a location whose context-insensitive
    /// identity matches one of `pointee`'s own collapsed locations.
    pub fn collapsed_points_to_local(
        &self,
        result: &PointsToResult,
        pointer: Instance<'tcx>,
        pointer_local: u32,
        pointee: Instance<'tcx>,
        pointee_local: u32,
    ) -> bool {
        let targets = self.collapsed_points_to(result, pointer, pointer_local);
        if targets.is_empty() {
            return false;
        }
        // The pointee local's own context-insensitive identity (empty path).
        let Some(func) = self.funcs.get_id(&pointee) else {
            return false;
        };
        let Some(empty) = self.arena.empty_path_id() else {
            return false;
        };
        let key = CiKey::Var {
            func,
            base: pointee_local,
            path: empty,
        };
        targets.contains(&key)
    }

    pub fn arena(&self) -> &LocArena {
        &self.arena
    }

    /// A fresh temporary var node (never a real MIR local) for holding an
    /// intermediate Offset/Load value during interprocedural binding.
    fn fresh_temp_loc(&mut self) -> LocId {
        let base = self.temp_counter;
        self.temp_counter += 1;
        let empty = self.arena.empty_path();
        self.arena.var_ctx(Context::empty(), 0, base, empty)
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Distinct proven-constant argument vectors observed at the
    /// call sites that resolved to `instance`. Empty when the callee is never
    /// called with a proven constant.
    pub fn call_arg_const_vectors(
        &self,
        instance: Instance<'tcx>,
    ) -> &[SmallVec<[Option<u64>; 4]>] {
        self.call_arg_consts
            .get(&instance)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Proven-constant argument vectors recorded for the concrete
    /// call site `(caller, bb)`. More than one entry means the same MIR site
    /// was built under contexts that proved different constants.
    pub fn call_site_arg_const_vectors(
        &self,
        caller: Instance<'tcx>,
        bb: u32,
    ) -> &[SmallVec<[Option<u64>; 4]>] {
        self.call_site_consts
            .get(&(caller, bb))
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Proven-constant parameter vectors per k-CFA context for
    /// `instance`, in a deterministic context order.
    pub fn param_values_by_context(
        &self,
        instance: Instance<'tcx>,
    ) -> Vec<(Context, SmallVec<[Option<u64>; 4]>)> {
        let mut out: Vec<(Context, SmallVec<[Option<u64>; 4]>)> = self
            .param_values
            .iter()
            .filter(|((inst, _), _)| *inst == instance)
            .map(|((_, ctx), vals)| (ctx.clone(), vals.clone()))
            .collect();
        out.sort_by(|(a, _), (b, _)| Self::context_sort_key(a).cmp(&Self::context_sort_key(b)));
        out
    }

    /// Is every projection of `key` an exact slot? A dynamic `Index`
    /// element means "any element of the container": a key containing it is a
    /// summary of several objects, so giving it a dedicated lock resource
    /// would wrongly make it disjoint from the per-object resources.
    pub fn ci_key_is_exact(&self, key: &CiKey) -> bool {
        super::loc::ci_key_is_exact(&self.arena, key)
    }

    /// Object identity names of a receiver key set under one proven
    /// constant argument vector (`None`: empty or inexact). See
    /// [`super::loc::guard_object_identity_names`].
    pub fn guard_object_identity_names(&self, keys: &[CiKey]) -> Option<Vec<String>> {
        super::loc::guard_object_identity_names(&self.arena, keys)
    }

    pub fn constraints(&self) -> &ConstraintSet {
        &self.constraints
    }

    /// Render the solved points-to relation as a deterministic, human-readable
    /// report. Used for differential comparison against the legacy engine.
    pub fn format_report(&self, result: &PointsToResult) -> String {
        let mut entries: Vec<(LocId, Vec<LocId>)> = result
            .raw()
            .raw()
            .iter()
            .filter(|(_, set)| !set.is_empty())
            .map(|(node, set)| {
                let mut pointees: Vec<LocId> = set.iter().copied().collect();
                pointees.sort_unstable();
                (*node, pointees)
            })
            .collect();
        entries.sort_unstable_by_key(|(node, _)| *node);

        let mut out = String::from("=== Spn Points-To Report (new engine) ===\n");
        out.push_str(&format!("nodes-with-pointees: {}\n", entries.len()));
        for (node, pointees) in &entries {
            let lhs = self.fmt_loc(*node);
            let rhs: Vec<String> = pointees.iter().map(|p| self.fmt_loc(*p)).collect();
            out.push_str(&format!("  {} -> {{ {} }}\n", lhs, rhs.join(", ")));
        }
        out.push_str("=== End ===\n");
        out
    }

    fn fmt_loc(&self, id: LocId) -> String {
        match self.arena.loc(id) {
            AbstractLoc::Var {
                ctx,
                func,
                base,
                path,
            } => {
                let cx = if ctx.is_empty() {
                    String::new()
                } else {
                    let sites: Vec<String> = ctx
                        .as_slice()
                        .iter()
                        .map(|s| format!("{}:{}", s.func, s.bb))
                        .collect();
                    format!("@[{}]", sites.join(","))
                };
                format!("f{}::_{}{}{}", func, base, self.fmt_path(*path), cx)
            }
            AbstractLoc::Heap { site, path, .. } => {
                format!(
                    "Heap(f{}:bb{}#{}){}",
                    site.func,
                    site.bb,
                    site.idx,
                    self.fmt_path(*path)
                )
            }
            AbstractLoc::Global { def_index, path } => {
                format!("Global({}){}", def_index, self.fmt_path(*path))
            }
        }
    }

    fn fmt_path(&self, path: FieldPath) -> String {
        let mut s = String::new();
        for elem in self.arena.path(path) {
            match elem {
                ProjElem::Field(i) => s.push_str(&format!(".{}", i)),
                ProjElem::Deref => s.push_str(".*"),
                ProjElem::Index => s.push_str("[*]"),
                ProjElem::ConstIndex(i) => s.push_str(&format!("[{}]", i)),
                ProjElem::Predicate { field, value } => {
                    s.push_str(&format!("[{}={}]", self.fmt_path(*field), value));
                }
            }
        }
        s
    }
}

/// Classify an `Option` adapter by its def path.
///
/// Returns `Some(true)` for `map_or` (which has a `default` argument) and
/// `Some(false)` for `map`/`and_then`. Other adapters (`map_or_else`, which
/// takes two functions, and all `Result` methods) are deliberately excluded.
fn option_adapter_kind(path: &str) -> Option<bool> {
    if !path.contains("option::Option") {
        return None;
    }
    if path.ends_with("::map_or") {
        Some(true)
    } else if path.ends_with("::map") || path.ends_with("::and_then") {
        Some(false)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::PointerAnalysis as PtaAnalysis;
    use crate::analysis::memory::pta::context::{CallSite, Context, ContextPolicy, KCallSite};
    use rustc_data_structures::fx::FxHashSet;

    fn set(items: &[u32]) -> FxHashSet<u32> {
        items.iter().copied().collect()
    }

    /// One-deep call-site context, as `pta_k = 1` produces.
    fn ctx(func: u32, bb: u32) -> Context {
        KCallSite::new(1).extend(Context::empty(), CallSite::new(func, bb))
    }

    fn per_ctx(entries: &[(Context, &[u32])]) -> Vec<(Context, FxHashSet<u32>)> {
        entries
            .iter()
            .map(|(c, xs)| (c.clone(), xs.iter().copied().collect()))
            .collect()
    }

    #[test]
    fn per_context_disjoint_sets_are_disjoint() {
        // Both sites run in the same context and reach different objects: the
        // per-context query can split them even though the collapsed union of
        // both sites' sets would intersect.
        let a = per_ctx(&[(ctx(1, 2), &[10])]);
        let b = per_ctx(&[(ctx(1, 2), &[20])]);
        assert_eq!(
            PtaAnalysis::classify_by_context(&a, &b, |x, y| x == y),
            Some(false)
        );
    }

    #[test]
    fn both_empty_shared_context_is_ignored() {
        // The context-insensitive fallback instance resolves neither receiver;
        // it carries no evidence and must not erase a precise disjoint verdict
        // from the specific contexts.
        let a = per_ctx(&[(ctx(1, 2), &[10]), (Context::empty(), &[])]);
        let b = per_ctx(&[(ctx(1, 2), &[20]), (Context::empty(), &[])]);
        assert_eq!(
            PtaAnalysis::classify_by_context(&a, &b, |x, y| x == y),
            Some(false)
        );
    }

    #[test]
    fn only_both_empty_shared_contexts_is_unknown() {
        // With nothing but unresolved contexts there is no evidence for a
        // disjoint verdict either: stay inconclusive.
        let a = per_ctx(&[(Context::empty(), &[])]);
        let b = per_ctx(&[(Context::empty(), &[])]);
        assert_eq!(
            PtaAnalysis::classify_by_context(&a, &b, |x, y| x == y),
            None
        );
    }

    #[test]
    fn per_context_overlap_is_alias() {
        let a = per_ctx(&[(ctx(1, 2), &[10, 20]), (ctx(3, 4), &[10])]);
        let b = per_ctx(&[(ctx(1, 2), &[20])]);
        assert_eq!(
            PtaAnalysis::classify_by_context(&a, &b, |x, y| x == y),
            Some(true)
        );
    }

    #[test]
    fn no_shared_context_is_unknown() {
        // Different call strings: the two sites never coexist in one context,
        // so the comparison is inconclusive (the unknown policy decides).
        let a = per_ctx(&[(ctx(1, 2), &[10])]);
        let b = per_ctx(&[(ctx(3, 4), &[10])]);
        assert_eq!(
            PtaAnalysis::classify_by_context(&a, &b, |x, y| x == y),
            None
        );
    }

    #[test]
    fn unresolved_shared_context_is_unknown() {
        // One shared context is unresolved: even a disjoint sibling context
        // cannot make the pair provably distinct.
        let a = per_ctx(&[(ctx(1, 2), &[10]), (ctx(3, 4), &[10])]);
        let b = per_ctx(&[(ctx(1, 2), &[]), (ctx(3, 4), &[20])]);
        assert_eq!(
            PtaAnalysis::classify_by_context(&a, &b, |x, y| x == y),
            None
        );
    }

    #[test]
    fn missing_context_is_not_compared() {
        // Contexts present on only one side are ignored; the remaining shared
        // context decides.
        let a = per_ctx(&[(ctx(1, 2), &[10]), (ctx(9, 9), &[99])]);
        let b = per_ctx(&[(ctx(1, 2), &[20]), (ctx(8, 8), &[10])]);
        assert_eq!(
            PtaAnalysis::classify_by_context(&a, &b, |x, y| x == y),
            Some(false)
        );
    }

    #[test]
    fn precise_contexts_ignore_the_context_insensitive_fallback() {
        // The empty-context instance keeps the *merged* (untagged)
        // receivers of a function, so its sets overlap even though the precise
        // per-value contexts select disjoint elements. With a precise shared
        // context resolving both sides, the fallback context is not evidence.
        let a = per_ctx(&[(ctx(1, 2), &[10]), (Context::empty(), &[10, 20])]);
        let b = per_ctx(&[(ctx(1, 2), &[20]), (Context::empty(), &[10, 20])]);
        assert_eq!(
            PtaAnalysis::classify_by_context(&a, &b, |x, y| x == y),
            Some(false)
        );
    }

    #[test]
    fn fallback_context_still_counts_without_a_precise_context() {
        // Without any precise shared context the empty context is the only
        // evidence there is; it must keep deciding (here: overlap).
        let a = per_ctx(&[(Context::empty(), &[10, 20])]);
        let b = per_ctx(&[(Context::empty(), &[20])]);
        assert_eq!(
            PtaAnalysis::classify_by_context(&a, &b, |x, y| x == y),
            Some(true)
        );
    }

    #[test]
    fn intersecting_receiver_sets_may_alias() {
        assert_eq!(
            PtaAnalysis::classify_receiver_alias_sets(&set(&[1, 2]), &set(&[2, 3])),
            Some(true)
        );
    }

    #[test]
    fn disjoint_non_empty_receiver_sets_do_not_alias() {
        assert_eq!(
            PtaAnalysis::classify_receiver_alias_sets(&set(&[1, 2]), &set(&[3, 4])),
            Some(false)
        );
    }

    #[test]
    fn empty_receiver_set_is_unknown_not_disjoint() {
        // The recall-gap bug: an unresolved receiver (empty set) was
        // answered as "no alias", splitting one lock's two access paths even
        // under the conservative policy. It must stay unknown so the policy
        // decides (Conservative merges).
        assert_eq!(
            PtaAnalysis::classify_receiver_alias_sets(&set(&[]), &set(&[3, 4])),
            None
        );
        assert_eq!(
            PtaAnalysis::classify_receiver_alias_sets(&set(&[1, 2]), &set(&[])),
            None
        );
        assert_eq!(
            PtaAnalysis::classify_receiver_alias_sets(&set(&[]), &set(&[])),
            None
        );
    }

    #[test]
    fn option_adapters_are_recognized_by_def_path() {
        use super::option_adapter_kind;
        assert_eq!(
            option_adapter_kind("std::option::Option::<T>::map_or"),
            Some(true)
        );
        assert_eq!(
            option_adapter_kind("core::option::Option::<T>::map"),
            Some(false)
        );
        assert_eq!(
            option_adapter_kind("std::option::Option::<T>::and_then"),
            Some(false)
        );
        // `map_or_else` takes two functions; not modeled as a fn-item adapter.
        assert_eq!(
            option_adapter_kind("std::option::Option::<T>::map_or_else"),
            None
        );
        // Result adapters share method names and must not match.
        assert_eq!(
            option_adapter_kind("std::result::Result::<T, E>::map"),
            None
        );
        assert_eq!(option_adapter_kind("std::option::Option::<T>::ok_or"), None);
    }
}
