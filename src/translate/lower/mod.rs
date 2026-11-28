//! Lowers one MIR body to Petri-net places and transitions.
//! Block walking, loops, guards, and thread queries live in the child modules.
//! This file keeps the translator's fields and the helpers every child calls.

mod body;
mod call;
mod control_flow;
pub mod facts;
pub(crate) mod guards;
mod loops;
mod terminator;
mod unsafe_ops;

use crate::analysis::callgraph::{CallGraph, InstanceId};
use crate::translate::net::{NetBuilder, PlaceId, TransitionId, UnsafeOp};
use crate::{
    analysis::api_patterns::KeyApiRegex,
    analysis::memory::alias_engine::AliasEngine,
    analysis::primitives::blocking::LockGuardMap,
    config::CondvarModel,
    config::LoopSemantics,
    translate::net::{FunctionRegistry, ResourceRegistry},
};
use control_flow::{BasicBlockGraph, SegState};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Local, Operand, TerminatorKind, visit::Visitor};
use rustc_middle::{
    mir::Body,
    ty::{Instance, TyCtxt},
};
use std::{cell::RefCell, collections::VecDeque, sync::Arc};

pub struct BodyToPetriNet<'translate, 'analysis, 'tcx> {
    instance_id: InstanceId,
    instance: &'translate Instance<'tcx>,
    body: &'translate Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    callgraph: &'translate CallGraph<'tcx>,
    pub net: &'translate mut NetBuilder<'tcx>,
    alias: &'translate mut RefCell<AliasEngine<'tcx>>,
    /// The call graph's lifetime. The alias engine no longer borrows it;
    /// the parameter stays so every lowering impl keeps the same header.
    _callgraph_lifetime: std::marker::PhantomData<&'analysis ()>,
    pub lockguards: Arc<LockGuardMap<'tcx>>,
    functions: &'translate FunctionRegistry,
    resources: &'translate ResourceRegistry,
    /// Places of collected sync sites. Filled before this body is lowered.
    /// Lock acquire and release read it; alias scans still use `resources`.
    resource_map: &'translate crate::analysis::sync::ResourceMap,
    place_binding: &'translate crate::translate::resources::PlaceBinding,
    bb_graph: BasicBlockGraph,
    pub exclude_bb: FxHashSet<usize>,
    back_edges: FxHashSet<(BasicBlock, BasicBlock)>,
    break_cfg_cycles: bool,
    /// How a cut back edge is modelled. `Cut` is the historical
    /// behaviour; `Summary` additionally emits one summary transition per cut
    /// edge.
    loop_semantics: LoopSemantics,
    /// How many re-entries a loop-summary transition may perform,
    /// i.e. the number of initial tokens on its budget place (`0` disables the
    /// summary, leaving only the terminal fallback).
    loop_summary_k: usize,
    /// The cut back edges whose summary transitions `emit_loop_summaries` must
    /// create. Recorded at the site that actually drops the edge, so a back
    /// edge that a handler happened to keep (e.g. a call whose callee is not
    /// translated goes through `connect_to_target`) is not summarized.
    cut_back_edges: Vec<CutBackEdge>,
    return_transition: TransitionId,
    /// Start place of *this* frame's function: where the entry transition
    /// (`bb0_start`) takes its token from. `None` keeps the historical
    /// behaviour for bodies without a registered function place.
    frame_start: Option<PlaceId>,
    /// End place of *this* frame's function: where every terminal transition
    /// (return, panic, unreachable, abort, …) deposits the frame's token.
    /// The `entry_exit` constructor argument only carries main's places; a
    /// non-main frame using them would leak its token onto main's end.
    frame_exit: PlaceId,
    /// Label prefix for this frame's places and transitions. It is the
    /// source function path. Provenance (`fn_path`) uses the formatted name.
    frame_name: String,
    /// Cleanup blocks whose unwind-chain transitions have already been emitted
    /// (they are shared by every panic site and translated once).
    translated_cleanup_blocks: FxHashSet<usize>,
    /// This body's function in `format_name` form; keys every provenance
    /// entry recorded for it.
    fn_path: String,
    /// Shared translation coverage accumulator (`translation-coverage.json`).
    coverage: &'translate mut crate::report::coverage::Coverage,
    key_api_regex: &'translate KeyApiRegex,
    alias_unknown_policy: crate::config::AliasUnknownPolicy,
    /// The scenario-level condvar model (type recognition, call
    /// matching, and the waiter-counter ordering guard).
    condvar_model: CondvarModel,
    /// Whether to translate atomic memory-ordering segment places.
    /// Only enabled for `atomic` / `all` analysis modes.
    translate_atomic_ordering: bool,
    ordered_spawn_ends: VecDeque<PlaceId>,
    spawn_handle_end: FxHashMap<Local, PlaceId>,
    local_ref_source: FxHashMap<Local, Local>,
    vec_alias_source: FxHashMap<Local, Local>,
    vec_spawn_ends: FxHashMap<Local, VecDeque<PlaceId>>,
    iter_vec_source: FxHashMap<Local, Local>,
    option_vec_source: FxHashMap<Local, Local>,
    handle_vec_source: FxHashMap<Local, Local>,
    joinhandle_vec_locals: FxHashSet<Local>,
    /// Locals carrying a `Condvar::wait` result, directly or through a
    /// `Result`/`Option` extractor chain. The wait subnet already re-acquires
    /// the guard on the wait's return transition, so a later extractor call
    /// with such a local as argument only forwards the guard; translating it
    /// as a lock acquisition would take a second mutex token.
    wait_result_locals: FxHashSet<Local>,
    /// `Condvar::wait` destination locals (e.g. `_12: LockResult<MutexGuard>`)
    /// that are dropped directly (`let _ = cv.wait(g2);`) without being
    /// extracted by `.unwrap()`/`.expect()`, mapped to the `LockGuardId` of the
    /// guard passed into `cv.wait`. Dropping such a `Result` drops the inner
    /// re-acquired `MutexGuard` and must release its lock resource.
    unextracted_wait_guards: FxHashMap<Local, crate::analysis::primitives::blocking::LockGuardId>,
    /// Recognized single-guard `while !*g { cv.wait(g) }` loops in this body.
    pub(super) bool_wait_loops: Vec<guards::predicates::BoolWaitLoop>,
    /// Recognized `*g = true` write blocks in this body.
    pub(super) bool_true_writes: Vec<(
        BasicBlock,
        crate::analysis::primitives::blocking::LockGuardId,
    )>,
    seg: SegState,
    /// Unsafe accesses accumulated while scanning the current basic block;
    /// flushed into one merged `UnsafeAccess` transition per block.
    pending_unsafe_ops: Vec<UnsafeOp>,
    subnet: crate::translate::net::subnets::SubNetContext,
    thread_seq: usize,
    spawn_thread_by_local: FxHashMap<Local, PlaceId>,
    ordered_thread_places: VecDeque<PlaceId>,
    vec_thread_places: FxHashMap<Local, VecDeque<PlaceId>>,
}

/// One back edge dropped by cycle breaking, as the translation actually
/// dropped it. the `LoopSemantics::Summary` turns each of these into one
/// loop-summary transition (bounded unroll `loop_summary_k`, default 1).
#[derive(Clone, Copy, Debug)]
pub(super) enum CutBackEdge {
    /// A pure control edge (`goto` / `switch` / `assert` / fallthrough):
    /// without the cut it would have been `last(source) -> start(target)`, so
    /// the summary transition can consume `last(source)` itself.
    Direct {
        source: BasicBlock,
        target: BasicBlock,
    },
    /// A call-return or drop edge: without the cut it would have been
    /// `after -> start(target)`. `last(source)` is consumed by `after`, so a
    /// trigger place carries `after`'s completion to the summary transition.
    After {
        source: BasicBlock,
        target: BasicBlock,
        after: TransitionId,
    },
}

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    fn functions_map(&self) -> &FxHashMap<DefId, (PlaceId, PlaceId)> {
        self.functions.counter()
    }

    /// Whether `src -> target` is a CFG back edge removed by cycle breaking.
    /// `back_edges` is only populated when `break_cfg_cycles` is enabled.
    fn is_back_edge(&self, src: BasicBlock, target: BasicBlock) -> bool {
        if self.bool_wait_loops.iter().any(|l| {
            l.latch_bb == src
                && l.header_bb == target
                && self
                    .lock_node_for_guard(l.guard_id)
                    .is_some_and(|ln| self.resources.bool_predicates().contains_key(&ln))
        }) {
            return false;
        }
        self.break_cfg_cycles && self.back_edges.contains(&(src, target))
    }

    /// Locals whose value is the result of a `Condvar::wait` call, directly or
    /// forwarded through a `Result`/`Option` extractor (`unwrap`, `expect`,
    /// ...). The wait subnet releases the guard at the wait call and
    /// re-acquires it at the wait's return transition; an extractor that
    /// merely forwards that result must not be translated as an acquisition
    /// (`Condvar::wait` guard release happens exactly once).
    fn collect_wait_result_locals(
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        key_api_regex: &KeyApiRegex,
    ) -> FxHashSet<Local> {
        let call_def_id = |func: &Operand<'tcx>| match func.ty(body, tcx).kind() {
            rustc_middle::ty::TyKind::FnDef(id, _) | rustc_middle::ty::TyKind::Closure(id, _) => {
                Some(*id)
            }
            _ => None,
        };

        let mut wait_results: FxHashSet<Local> = FxHashSet::default();
        for bb in body.basic_blocks.iter() {
            let TerminatorKind::Call {
                func, destination, ..
            } = &bb.terminator().kind
            else {
                continue;
            };
            let Some(def_id) = call_def_id(func) else {
                continue;
            };
            let name = crate::util::format_name(def_id);
            if crate::analysis::memory::ownership::is_condvar_wait(def_id, tcx)
                || crate::util::has_spn_attribute(tcx, def_id, "pn_condvar_wait")
                || key_api_regex.matches_condvar_wait(&name)
            {
                wait_results.insert(destination.local);
            }
        }

        // Chained or forwarded extracts (`let r = wait(g); let g = r.unwrap();`)
        // carry the same guard through; iterate to a fixpoint.
        loop {
            let mut changed = false;
            for bb in body.basic_blocks.iter() {
                let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } = &bb.terminator().kind
                else {
                    continue;
                };
                let Some(def_id) = call_def_id(func) else {
                    continue;
                };
                if !crate::analysis::memory::ownership::is_wrapper_extract(def_id, tcx) {
                    continue;
                }
                if args.iter().any(|arg| {
                    arg.node
                        .place()
                        .is_some_and(|place| wait_results.contains(&place.local))
                }) {
                    changed |= wait_results.insert(destination.local);
                }
            }
            if !changed {
                break;
            }
        }

        wait_results
    }

    pub fn new(
        instance_id: InstanceId,
        instance: &'translate Instance<'tcx>,
        body: &'translate Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        callgraph: &'translate CallGraph<'tcx>,
        net: &'translate mut NetBuilder<'tcx>,
        alias: &'translate mut RefCell<AliasEngine<'tcx>>,
        lockguards: Arc<LockGuardMap<'tcx>>,
        functions: &'translate FunctionRegistry,
        resources: &'translate ResourceRegistry,
        resource_map: &'translate crate::analysis::sync::ResourceMap,
        place_binding: &'translate crate::translate::resources::PlaceBinding,
        entry_exit: (PlaceId, PlaceId),
        key_api_regex: &'translate KeyApiRegex,
        alias_unknown_policy: crate::config::AliasUnknownPolicy,
        condvar_model: CondvarModel,
        break_cfg_cycles: bool,
        loop_semantics: LoopSemantics,
        loop_summary_k: usize,
        translate_atomic_ordering: bool,
        coverage: &'translate mut crate::report::coverage::Coverage,
    ) -> Self {
        let joinhandle_vec_locals: FxHashSet<Local> = body
            .local_decls
            .iter_enumerated()
            .filter_map(|(local, decl)| {
                let ty_str = format!("{:?}", decl.ty);
                if ty_str.contains("Vec") && ty_str.contains("JoinHandle") {
                    Some(local)
                } else {
                    None
                }
            })
            .collect();

        let wait_result_locals = Self::collect_wait_result_locals(body, tcx, key_api_regex);

        let (bool_wait_loops, bool_true_writes) = if !resources.bool_predicates().is_empty() {
            (
                guards::predicates::find_bool_guard_wait_loops(
                    instance_id,
                    body,
                    tcx,
                    &lockguards,
                    key_api_regex,
                ),
                guards::predicates::find_bool_guard_true_writes(
                    instance_id,
                    body,
                    tcx,
                    &lockguards,
                ),
            )
        } else {
            (Vec::new(), Vec::new())
        };

        #[allow(unused_mut)]
        let mut s = Self {
            instance_id,
            instance,
            body,
            tcx,
            callgraph,
            net,
            alias,
            _callgraph_lifetime: std::marker::PhantomData,
            lockguards,
            functions,
            resources,
            resource_map,
            place_binding,
            bb_graph: BasicBlockGraph::new(),
            exclude_bb: FxHashSet::default(),
            back_edges: FxHashSet::default(),
            break_cfg_cycles,
            loop_semantics,
            loop_summary_k,
            cut_back_edges: Vec::new(),
            return_transition: TransitionId(0),
            frame_start: functions
                .counter()
                .get(&instance.def_id())
                .map(|(start, _)| *start),
            frame_exit: functions
                .counter()
                .get(&instance.def_id())
                .map(|(_, end)| *end)
                .unwrap_or_else(|| {
                    log::warn!(
                        "no function-end place registered for {}; falling back to main's end",
                        tcx.def_path_str(instance.def_id())
                    );
                    entry_exit.1
                }),
            frame_name: tcx.def_path_str(instance.def_id()),
            translated_cleanup_blocks: FxHashSet::default(),
            fn_path: crate::util::format_name(instance.def_id()),
            coverage,
            key_api_regex,
            alias_unknown_policy,
            condvar_model,
            translate_atomic_ordering,
            ordered_spawn_ends: VecDeque::new(),
            spawn_handle_end: FxHashMap::default(),
            local_ref_source: FxHashMap::default(),
            vec_alias_source: FxHashMap::default(),
            vec_spawn_ends: FxHashMap::default(),
            iter_vec_source: FxHashMap::default(),
            option_vec_source: FxHashMap::default(),
            handle_vec_source: FxHashMap::default(),
            joinhandle_vec_locals,
            wait_result_locals,
            unextracted_wait_guards: FxHashMap::default(),
            bool_wait_loops,
            bool_true_writes,
            seg: SegState::default(),
            pending_unsafe_ops: Vec::new(),
            subnet: crate::translate::net::subnets::SubNetContext::new(
                crate::util::format_name(instance.def_id()),
                functions
                    .counter()
                    .get(&instance.def_id())
                    .map(|(start, _)| *start)
                    .unwrap_or(entry_exit.0),
                functions
                    .counter()
                    .get(&instance.def_id())
                    .map(|(_, end)| *end)
                    .unwrap_or(entry_exit.1),
            ),
            thread_seq: 0,
            spawn_thread_by_local: FxHashMap::default(),
            ordered_thread_places: VecDeque::new(),
            vec_thread_places: FxHashMap::default(),
        };

        s.unextracted_wait_guards = s.collect_unextracted_wait_guards();

        {
            if s.translate_atomic_ordering {
                let tid = s.instance_id.index();
                s.seg.seg_index.insert(tid, 0);
                let seg_place = s.ensure_seg_place(tid, 0);
                s.net.set_tokens(seg_place, 1);
                s.net.ensure_capacity(seg_place, 1);
            }
        }

        s
    }

    pub fn translate(&mut self) {
        self.record_function_facts();
        self.visit_body(self.body);
        self.attach_bool_guard_true_writes();
        self.attach_custom_lock_resource();
        if self.loop_semantics == LoopSemantics::Summary {
            self.emit_loop_summaries();
        } else {
            self.emit_loop_abandon_returns();
        }
        self.record_cut_back_edges();
    }

    pub(super) fn take_subnet(&mut self) -> crate::translate::net::subnets::SubNetContext {
        std::mem::replace(
            &mut self.subnet,
            crate::translate::net::subnets::SubNetContext::new(
                String::new(),
                PlaceId(0),
                PlaceId(0),
            ),
        )
    }

    pub(super) fn emit_thread_place(&mut self, owner: Option<Local>) -> PlaceId {
        use crate::translate::net::{ControlSub, PlaceClass};
        let place = self.net.place(
            PlaceClass::Control(ControlSub::FunctionEnd),
            format!("{}_thread_{}", self.frame_name, self.thread_seq),
            1,
        );
        self.thread_seq += 1;
        if let Some(owner) = owner {
            self.spawn_thread_by_local.insert(owner, place);
        }
        self.ordered_thread_places.push_back(place);
        place
    }

    /// Whether `place` already has a consumer arc (`place -> transition`).
    ///
    /// UniPN's `ArcDir::Input` is the arc that *leaves* the place toward a
    /// transition and consumes its token; `ArcDir::Output` is the reverse
    /// (`transition -> place`) arc that *delivers* a token. Testing `Output`
    /// would be wrong here: every place a transition produces has one, so the
    /// check would never fire (found while validating that fix on
    /// parking_lot: the abandon emitter silently skipped every strand).
    fn place_has_consumer(&self, place: PlaceId) -> bool {
        self.net.has_consumer(place)
    }

    fn block_reaches(&self, from: BasicBlock, target: BasicBlock) -> bool {
        let mut visited = vec![false; self.body.basic_blocks.len()];
        let mut queue = VecDeque::new();
        visited[from.index()] = true;
        queue.push_back(from);
        while let Some(bb) = queue.pop_front() {
            if bb == target {
                return true;
            }
            if let Some(term) = &self.body.basic_blocks[bb].terminator {
                for succ in term.successors() {
                    if !self.body.basic_blocks[succ].is_cleanup && !visited[succ.index()] {
                        visited[succ.index()] = true;
                        queue.push_back(succ);
                    }
                }
            }
        }
        false
    }
}
