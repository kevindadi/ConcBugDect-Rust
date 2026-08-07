//! Whole-program driver.
//!
//! [`PointerAnalysis`] builds constraints for all functions reachable (by
//! direct calls) from a set of roots, performing interprocedural binding for
//! analyzable callees and falling back to the conservative model otherwise,
//! then solves to a [`PointsToResult`]. Call-site sensitivity (k-CFA) is
//! controlled by `k`: each `(instance, context)` pair is built once and its
//! local/place nodes are tagged with that context. `k = 0` reduces to a single
//! context-insensitive context.

extern crate rustc_middle;

use std::collections::VecDeque;

use rustc_data_structures::fx::FxHashSet;
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

pub struct PointerAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
    arena: LocArena,
    constraints: ConstraintSet,
    funcs: FuncMap<'tcx>,
    registry: ModelRegistry,
    policy: KCallSite,
    /// `(instance, context)` pairs already translated.
    built: FxHashSet<(Instance<'tcx>, Context)>,
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
            let pending = build_body(
                self.tcx,
                body,
                func,
                ctx.clone(),
                inst,
                &self.registry,
                &mut self.arena,
                &mut self.constraints,
            );
            for pc in pending {
                self.resolve_pending(inst, func, &ctx, pc, &mut queue);
            }
        }
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
                        let site = CallSite {
                            func: caller_func,
                            bb: pc.bb,
                        };
                        let callee_ctx = self.policy.extend(caller_ctx.clone(), site);
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
        self.constraints
            .add(Constraint::Copy { dst: pc.dest, src: ret });

        // params: callee._i ⊇ arg_i, plus field-wise expansion for aggregate params.
        for i in 1..=arg_count {
            let Some(Some(arg)) = pc.args.get(i - 1).copied() else {
                continue;
            };
            let param = self
                .arena
                .var_ctx(callee_ctx.clone(), callee_func, i as u32, empty);
            self.constraints
                .add(Constraint::Copy { dst: param, src: arg });

            // Field expansion: for each leaf field path p of the param's type,
            // param·p ⊇ arg·p. Only adds edges between *projected* slots; sound
            // (the base Copy already covers the field-insensitive case).
            let param_ty = body.local_decls[rustc_middle::mir::Local::from_usize(i)].ty;
            let param_ty = callee.instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                typing_env,
                rustc_middle::ty::EarlyBinder::bind(param_ty),
            );
            let paths = crate::memory::pta::typeutil::leaf_field_paths(
                self.tcx,
                typing_env,
                param_ty,
                &mut self.arena,
            );
            for p in paths {
                if self.arena.path(p).is_empty() {
                    continue;
                }
                let pj = self.arena.project(param, p);
                let aj = self.arena.project(arg, p);
                if let (Some(pj), Some(aj)) = (pj, aj) {
                    self.constraints.add(Constraint::Copy { dst: pj, src: aj });
                }
            }
        }
    }

    fn apply_unknown(&mut self, pc: PendingCall<'tcx>) {
        let nodes = CallNodes {
            dest: pc.dest,
            args: pc.args,
            fresh_heap: pc.fresh_heap,
        };
        self.registry.apply_unknown(&nodes, &mut self.constraints);
    }

    /// Solve the accumulated constraints and return a query facade.
    pub fn solve(&mut self) -> PointsToResult {
        let pts = Solver::new(self.arena.loc_count()).solve(&self.constraints, &mut self.arena);
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

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
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

        let mut out = String::from("=== PTA Points-To Report (new engine) ===\n");
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
            }
        }
        s
    }
}
