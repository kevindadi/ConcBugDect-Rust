//! MIR → Petri net translation (main module).

mod bb_graph;
mod calls;
mod cfg_utils;
mod closure;
mod concurrency;
mod drop_unsafe;
mod terminator;
mod thread_control;

use super::callgraph::{CallGraph, InstanceId};
use crate::{
    concurrency::blocking::LockGuardMap,
    memory::alias_engine::AliasEngine,
    memory::pointsto::AliasId,
    translate::structure::{FunctionRegistry, KeyApiRegex, ResourceRegistry},
};
use unipn::pt::{PtBuilder, UnsafeOp};
use unipn::{PlaceId, TransitionId};
use bb_graph::{BasicBlockGraph, SegState};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Local, Operand, Rvalue, Statement, StatementKind, TerminatorKind,
    visit::Visitor,
};
use rustc_middle::{
    mir::{Body, Terminator},
    ty::{Instance, TyCtxt},
};
use std::{cell::RefCell, collections::VecDeque, sync::Arc};

pub struct BodyToPetriNet<'translate, 'analysis, 'tcx> {
    instance_id: InstanceId,
    instance: &'translate Instance<'tcx>,
    body: &'translate Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    callgraph: &'translate CallGraph<'tcx>,
    pub net: &'translate mut PtBuilder,
    alias: &'translate mut RefCell<AliasEngine<'analysis, 'tcx>>,
    pub lockguards: Arc<LockGuardMap<'tcx>>,
    functions: &'translate FunctionRegistry,
    resources: &'translate ResourceRegistry,
    bb_graph: BasicBlockGraph,
    pub exclude_bb: FxHashSet<usize>,
    back_edges: FxHashSet<(BasicBlock, BasicBlock)>,
    break_cfg_cycles: bool,
    return_transition: TransitionId,
    entry_exit: (PlaceId, PlaceId),
    key_api_regex: &'translate KeyApiRegex,
    alias_unknown_policy: crate::config::AliasUnknownPolicy,
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
    seg: SegState,
    /// Unsafe accesses accumulated while scanning the current basic block;
    /// flushed into one merged `UnsafeAccess` transition per block.
    pending_unsafe_ops: Vec<UnsafeOp>,
}

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    fn functions_map(&self) -> &FxHashMap<DefId, (PlaceId, PlaceId)> {
        self.functions.counter()
    }

    fn is_back_edge(&self, _src: BasicBlock, _target: BasicBlock) -> bool {
        // Preserve complete control flow; do not skip back edges.
        false
    }

    /// Match `join_id` against `spawn_calls` via alias analysis; returns plausible spawn callee `DefId`s.
    fn get_matching_spawn_callees(&mut self, join_id: AliasId) -> Vec<DefId> {
        self.callgraph
            .get_spawn_calls(self.instance.def_id())
            .map(|spawn_calls| {
                spawn_calls
                    .iter()
                    .filter_map(|(spawn_dest_id, callees)| {
                        let alias_kind = self.alias.borrow_mut().alias(join_id, *spawn_dest_id);
                        if alias_kind.may_alias(self.alias_unknown_policy) {
                            Some(callees.iter().copied())
                        } else {
                            None
                        }
                    })
                    .flatten()
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default()
    }

    pub fn new(
        instance_id: InstanceId,
        instance: &'translate Instance<'tcx>,
        body: &'translate Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        callgraph: &'translate CallGraph<'tcx>,
        net: &'translate mut PtBuilder,
        alias: &'translate mut RefCell<AliasEngine<'analysis, 'tcx>>,
        lockguards: Arc<LockGuardMap<'tcx>>,
        functions: &'translate FunctionRegistry,
        resources: &'translate ResourceRegistry,
        entry_exit: (PlaceId, PlaceId),
        key_api_regex: &'translate KeyApiRegex,
        alias_unknown_policy: crate::config::AliasUnknownPolicy,
        break_cfg_cycles: bool,
        translate_atomic_ordering: bool,
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

        #[allow(unused_mut)]
        let mut s = Self {
            instance_id,
            instance,
            body,
            tcx,
            callgraph,
            net,
            alias,
            lockguards,
            functions,
            resources,
            bb_graph: BasicBlockGraph::new(),
            exclude_bb: FxHashSet::default(),
            back_edges: FxHashSet::default(),
            break_cfg_cycles,
            return_transition: TransitionId(0),
            entry_exit,
            key_api_regex,
            alias_unknown_policy,
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
            seg: SegState::default(),
            pending_unsafe_ops: Vec::new(),
        };

        {
            if s.translate_atomic_ordering {
                let tid = s.instance_id.index();
                s.seg.seg_index.insert(tid, 0);
                let seg_place = s.ensure_seg_place(tid, 0);
                s.net.set_place_tokens(seg_place, 1);
                if let Some(place) = s.net.place_mut(seg_place)
                    && place.capacity.map_or(true, |c| c < 1)
                {
                    place.capacity = Some(1);
                }
            }
        }

        s
    }

    pub fn translate(&mut self) {
        self.visit_body(self.body);
    }

    fn handle_terminator(
        &mut self,
        term: &Terminator<'tcx>,
        bb_idx: BasicBlock,
        name: &str,
        bb: &BasicBlockData<'tcx>,
    ) {
        match &term.kind {
            TerminatorKind::Goto { target } => self.handle_goto(bb_idx, target, name),
            TerminatorKind::SwitchInt { targets, .. } => self.handle_switch(bb_idx, targets, name),
            TerminatorKind::Return => self.handle_return(bb_idx, name),
            TerminatorKind::Assert { target, .. } => {
                self.handle_assert(bb_idx, target, name);
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => {
                self.handle_call(
                    bb_idx,
                    func,
                    args,
                    destination,
                    target,
                    name,
                    &format!("{:?}", term.source_info.span),
                    unwind,
                );
            }
            TerminatorKind::Drop { place, target, .. } => {
                self.handle_drop(&bb_idx, place, target, name, bb)
            }
            TerminatorKind::FalseEdge { real_target, .. } => {
                self.handle_fallthrough(bb_idx, real_target, name, "false_edge");
            }
            TerminatorKind::FalseUnwind { real_target, .. } => {
                self.handle_fallthrough(bb_idx, real_target, name, "false_unwind");
            }
            TerminatorKind::Yield { resume, .. } => {
                self.handle_fallthrough(bb_idx, resume, name, "yield");
            }
            TerminatorKind::InlineAsm {
                targets, unwind: _, ..
            } => {
                if let Some(target) = targets.first() {
                    self.handle_fallthrough(bb_idx, target, name, "inline_asm");
                } else {
                    self.handle_terminal_block(bb_idx, name, "inline_asm_noreturn");
                }
            }
            TerminatorKind::Unreachable => {
                self.handle_terminal_block(bb_idx, name, "unreachable");
            }
            TerminatorKind::UnwindResume => {
                self.handle_terminal_block(bb_idx, name, "unwind_resume");
            }
            TerminatorKind::UnwindTerminate(_) => {
                self.handle_terminal_block(bb_idx, name, "unwind_terminate");
            }
            TerminatorKind::CoroutineDrop => {
                self.handle_terminal_block(bb_idx, name, "coroutine_drop");
            }
            TerminatorKind::TailCall { .. } => {
                self.handle_terminal_block(bb_idx, name, "tail_call");
            }
        }
    }

    fn visit_statement_body(&mut self, statement: &Statement<'tcx>, bb_idx: BasicBlock) {
        let span_str = format!("{:?}", statement.source_info.span);
        if let StatementKind::Assign(box (dest, rvalue)) = &statement.kind {
            let fn_name = self.tcx.def_path_str(self.instance.def_id());
            self.track_joinhandle_dataflow(dest.local, rvalue);

            self.process_rvalue_reads(rvalue, &fn_name, bb_idx, &span_str);

            self.process_place_writes(dest, &fn_name, bb_idx, &span_str);
        }
    }

    fn track_joinhandle_dataflow(&mut self, dest: Local, rvalue: &Rvalue<'tcx>) {
        match rvalue {
            Rvalue::Ref(_, _, place) => {
                self.local_ref_source.insert(dest, place.local);
            }
            Rvalue::Use(op, _) => {
                if let Operand::Move(place) | Operand::Copy(place) = op {
                    let src = place.local;
                    if let Some(end) = self.spawn_handle_end.get(&src).copied() {
                        self.spawn_handle_end.insert(dest, end);
                    }
                    if let Some(vec_local) = self.iter_vec_source.get(&src).copied() {
                        self.iter_vec_source.insert(dest, vec_local);
                    }
                    if let Some(vec_local) = self.option_vec_source.get(&src).copied() {
                        self.option_vec_source.insert(dest, vec_local);
                    }
                    if let Some(vec_local) = self.handle_vec_source.get(&src).copied() {
                        self.handle_vec_source.insert(dest, vec_local);
                    }
                    let src_vec = self.resolve_vec_local(src);
                    if self.vec_spawn_ends.contains_key(&src_vec) {
                        self.vec_alias_source.insert(dest, src_vec);
                    }
                }
            }
            _ => {}
        }
    }
}

impl<'translate, 'analysis, 'tcx> Visitor<'tcx> for BodyToPetriNet<'translate, 'analysis, 'tcx> {
    fn visit_body(&mut self, body: &Body<'tcx>) {
        let def_id = self.instance.def_id();

        let fn_name = self.tcx.def_path_str(def_id);

        if fn_name.contains("::deserialize")
            || fn_name.contains("::serialize")
            || fn_name.contains("::visit_seq")
            || fn_name.contains("::visit_map")
        {
            log::warn!("Skipping serialization function: {}", fn_name);
            return;
        }

        self.init_basic_block(body, &fn_name);

        if self.break_cfg_cycles {
            self.back_edges = cfg_utils::compute_back_edges(body);
        }

        for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
            if bb.is_cleanup || bb.is_empty_unreachable() {
                continue;
            }

            for stmt in bb.statements.iter() {
                if let Some(ref term) = bb.terminator {
                    if let TerminatorKind::Assert { .. } = &term.kind {
                        break;
                    }
                }
                self.visit_statement_body(stmt, bb_idx);
            }

            self.flush_unsafe_ops(bb_idx);

            if bb_idx.index() == 0 {
                self.handle_start_block(&fn_name, bb_idx, def_id);
            }

            if let Some(term) = &bb.terminator {
                self.handle_terminator(term, bb_idx, &fn_name, bb);
            }
        }
    }
}
