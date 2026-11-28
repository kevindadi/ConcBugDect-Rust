//! Terminators: `init_basic_block`, `handle_start_block`, `handle_goto`, `handle_switch`, `handle_return`, …

use super::BodyToPetriNet;
use crate::translate::net::{PlaceId, TransitionId, TransitionType};
use rustc_middle::mir::{BasicBlock, Body, Operand, SwitchTargets, TerminatorKind};

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    pub(super) fn init_basic_block(&mut self, body: &Body<'tcx>, body_name: &str) {
        for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
            if bb.is_cleanup || bb.is_empty_unreachable() {
                self.exclude_bb.insert(bb_idx.index());
                continue;
            }
            let bb_span = bb.terminator.as_ref().map_or("".to_string(), |term| {
                format!("{:?}", term.source_info.span)
            });

            let bb_name = format!("{}_{}", body_name, bb_idx.index());
            let bb_start = crate::bb_place!(self.net, bb_name, bb_span);
            self.bb_graph.register(bb_idx, bb_start);
        }
    }

    pub(super) fn handle_start_block(&mut self, name: &str, bb_idx: BasicBlock) {
        let bb_start_name = format!("{}_{}_start", name, bb_idx.index());
        let span = self.bb_span(bb_idx);
        let bb_start = self.new_transition(
            bb_start_name,
            TransitionType::Start(self.instance_id.index()),
            bb_idx,
            span,
        );

        if let Some(func_start) = self.frame_start {
            self.net.arc_in(func_start, bb_start, 1);
        }
        self.net.arc_out(self.bb_graph.start(bb_idx), bb_start, 1);
    }

    pub(super) fn handle_assert(&mut self, bb_idx: BasicBlock, target: &BasicBlock, name: &str) {
        if self.is_back_edge(bb_idx, *target) {
            self.record_cut_back_edge(super::CutBackEdge::Direct {
                source: bb_idx,
                target: *target,
            });
            return;
        }
        let transition = crate::add_fallthrough_transition!(
            self,
            bb_idx,
            name,
            "assert",
            TransitionType::Assert,
            target
        );
        self.record_guard_transition(bb_idx, transition);
    }

    pub(super) fn handle_fallthrough(
        &mut self,
        bb_idx: BasicBlock,
        target: &BasicBlock,
        name: &str,
        kind: &str,
    ) {
        if self.exclude_bb.contains(&target.index()) {
            log::debug!(
                "Fallthrough {} from bb{} to excluded bb{}",
                kind,
                bb_idx.index(),
                target.index()
            );
            return;
        }
        if self.is_back_edge(bb_idx, *target) {
            self.record_cut_back_edge(super::CutBackEdge::Direct {
                source: bb_idx,
                target: *target,
            });
            return;
        }

        crate::add_fallthrough_transition!(self, bb_idx, name, kind, TransitionType::Goto, target);
    }

    /// A frame-terminating block (`unreachable`, `unwind_resume`,
    /// `unwind_terminate`, `coroutine_drop`, `tail_call`, noreturn inline asm):
    /// the frame ends at its own function-end place.
    pub(super) fn handle_terminal_block(&mut self, bb_idx: BasicBlock, name: &str, kind: &str) {
        crate::add_terminal_transition!(
            self,
            bb_idx,
            name,
            kind,
            TransitionType::Return(self.instance_id.index())
        );
    }

    pub(super) fn handle_goto(&mut self, bb_idx: BasicBlock, target: &BasicBlock, name: &str) {
        if self.body.basic_blocks[*target].is_cleanup {
            self.handle_panic(bb_idx, name, Some(*target));
            return;
        }
        if self.is_back_edge(bb_idx, *target) {
            self.record_cut_back_edge(super::CutBackEdge::Direct {
                source: bb_idx,
                target: *target,
            });
            return;
        }

        crate::add_fallthrough_transition!(
            self,
            bb_idx,
            name,
            "goto",
            TransitionType::Goto,
            target
        );
    }

    pub(super) fn handle_switch(
        &mut self,
        bb_idx: BasicBlock,
        targets: &SwitchTargets,
        name: &str,
    ) {
        // In a coroutine body, `bb0` is the state-machine dispatch (switch on the
        // discriminant). Its *resume* states are only valid after a previous
        // suspend; exploring them from the initial poll lets e.g. `main` reach an
        // `.await` poll without its spawned task ever running, producing bogus
        // terminal states. The suspend fix already routes resumptions through the
        // continuation, so here we only keep the entry state (discriminant 0).
        let is_coroutine_dispatch =
            bb_idx.index() == 0 && self.tcx.is_coroutine(self.instance.def_id());
        let mut t_num = 1u8;
        for t in targets.all_targets() {
            if is_coroutine_dispatch && t_num > 1 {
                break;
            }
            if self.exclude_bb.contains(&t.index()) {
                continue;
            }
            if self.is_back_edge(bb_idx, *t) {
                self.record_cut_back_edge(super::CutBackEdge::Direct {
                    source: bb_idx,
                    target: *t,
                });
                continue;
            }
            let bb_term_name = crate::transition_name!(name, bb_idx, "switch", t_num.to_string());
            t_num += 1;
            let span = self.bb_span(bb_idx);
            let bb_end = self.new_transition(bb_term_name, TransitionType::Switch, bb_idx, span);
            self.record_guard_transition(bb_idx, bb_end);

            self.net.arc_in(self.bb_graph.last(bb_idx), bb_end, 1);
            let target_bb_start = self.bb_graph.start(*t);
            self.net.arc_out(target_bb_start, bb_end, 1);

            // Attach read arcs (`data.<var>.false` on the `!*g == true`
            // loop-entry branch, `data.<var>.true` on the `!*g == false`
            // loop-exit branch) when `bb_idx` is the `SwitchInt` of a
            // recognized `while !*g { cv.wait(g) }` loop.
            if let Some(wait_loop) = self
                .bool_wait_loops
                .iter()
                .find(|l| l.switch_bb == bb_idx)
                .copied()
                && let Some(lock_node) = self.lock_node_for_guard(wait_loop.guard_id)
                && let Some(&(false_place, true_place)) =
                    self.resources.bool_predicates().get(&lock_node)
            {
                if *t == wait_loop.loop_body_bb {
                    self.net.arc_in(false_place, bb_end, 1);
                    self.net.arc_out(false_place, bb_end, 1);
                } else if *t == wait_loop.loop_exit_bb {
                    self.net.arc_in(true_place, bb_end, 1);
                    self.net.arc_out(true_place, bb_end, 1);
                }
            }
        }
    }

    pub(super) fn handle_return(&mut self, bb_idx: BasicBlock, name: &str) {
        // A coroutine's `Return` with `Poll::Pending` is a suspend point, not a
        // completion: the task stays alive holding its locks and later resumes
        // (the `Poll::Ready` return is the real completion). Connecting a suspend
        // to the function end would spuriously "complete" the task and leak the
        // locks it still holds, so instead we resume to the continuation block
        // (the poll-switch's other target).
        if self.tcx.is_coroutine(self.instance.def_id()) && self.block_sets_poll_pending(bb_idx) {
            if let Some(cont) = self.find_suspend_continuation(bb_idx) {
                self.handle_fallthrough(bb_idx, &cont, name, "suspend");
            }
            return;
        }

        let return_node = self.frame_exit;

        if self.return_transition.index() == 0 {
            let bb_term_name = crate::transition_name!(name, bb_idx, "return");
            let span = self.bb_span(bb_idx);
            let bb_end = self.new_transition(
                bb_term_name,
                TransitionType::Return(self.instance_id.index()),
                bb_idx,
                span,
            );

            self.return_transition = bb_end.clone();
        }

        self.net
            .arc_in(self.bb_graph.last(bb_idx), self.return_transition, 1);
        self.net.arc_out(return_node, self.return_transition, 1);
    }

    /// The transition of a call terminator; its span is the call's, so the
    /// provenance points at the call rather than at the block.
    pub(super) fn create_call_transition(
        &mut self,
        bb_idx: BasicBlock,
        bb_term_name: &str,
        span: &str,
    ) -> TransitionId {
        let bb_end = self.new_transition(
            bb_term_name.to_string(),
            TransitionType::Function,
            bb_idx,
            span.to_string(),
        );

        self.net.arc_in(self.bb_graph.last(bb_idx), bb_end, 1);
        bb_end
    }

    pub(super) fn connect_to_target(
        &mut self,
        _bb_idx: BasicBlock,
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
    ) {
        if let Some(target_bb) = target {
            self.net.arc_out(self.bb_graph.start(*target_bb), bb_end, 1);
        }
    }

    /// A call that never returns and has no local cleanup successor
    /// (`UnwindAction::Continue`): the frame ends at its own end place.
    pub(super) fn handle_unwind_continue(&mut self, bb_idx: BasicBlock, name: &str) {
        crate::add_terminal_transition!(
            self,
            bb_idx,
            name,
            "unwind",
            TransitionType::Return(self.instance_id.index())
        );
    }

    /// A frame that exits abnormally (panic). When the terminator names the
    /// first cleanup block, the frame walks its unwind chain — dropping the
    /// guards it still holds — before ending at its own function-end place;
    /// without a cleanup successor it ends directly.
    pub(super) fn handle_panic(
        &mut self,
        bb_idx: BasicBlock,
        name: &str,
        cleanup: Option<BasicBlock>,
    ) {
        let t_name = crate::transition_name!(name, bb_idx, "panic");
        let span = self.bb_span(bb_idx);
        let t_id = self.new_transition(
            t_name,
            TransitionType::Return(self.instance_id.index()),
            bb_idx,
            span,
        );
        self.net.arc_in(self.bb_graph.last(bb_idx), t_id, 1);

        match cleanup {
            Some(cleanup_bb) => {
                let place = self.cleanup_place(cleanup_bb);
                self.net.arc_out(place, t_id, 1);
                self.translate_cleanup_chain(cleanup_bb);
            }
            None => {
                self.net.arc_out(self.frame_exit, t_id, 1);
            }
        }
    }

    /// A frame-terminating abort (`UnwindAction::Terminate`/`Unreachable`).
    /// Process-level termination is not modelled; the frame is treated as
    /// ending, with its own transition kind so the approximation stays visible.
    pub(super) fn handle_abort(&mut self, bb_idx: BasicBlock, name: &str) {
        crate::add_terminal_transition!(
            self,
            bb_idx,
            name,
            "abort",
            TransitionType::Return(self.instance_id.index())
        );
    }

    /// Lazily create (or look up) the control place of a cleanup block.
    /// Cleanup blocks never enter `init_basic_block`'s graph, so their place is
    /// created the first time an unwind chain reaches them; every later panic
    /// site that unwinds through the same block merges into that place.
    fn cleanup_place(&mut self, bb_idx: BasicBlock) -> PlaceId {
        if let Some(&place) = self.bb_graph.start_places.get(&bb_idx) {
            return place;
        }
        let span = self.body.basic_blocks[bb_idx]
            .terminator
            .as_ref()
            .map_or(String::new(), |term| format!("{:?}", term.source_info.span));
        let fn_name = self.tcx.def_path_str(self.instance.def_id());
        let name = format!("{}_{}_cleanup", fn_name, bb_idx.index());
        let place = crate::bb_place!(self.net, name, span);
        self.bb_graph.register(bb_idx, place);
        place
    }

    /// Translate the unwind cleanup chain that starts at `entry`: walk the
    /// cleanup blocks, emit one transition per step (drops of lock guards reuse
    /// the normal release wiring and weights), and end the frame at its own
    /// `_end` when the chain resumes or cannot be followed further.
    ///
    /// Every panic site that unwinds through the same chain shares its blocks:
    /// each block is translated once (so parallel input arcs are not double-
    /// counted), while its place collects one token per entering frame.
    pub(super) fn translate_cleanup_chain(&mut self, entry: BasicBlock) {
        let fn_name = self.tcx.def_path_str(self.instance.def_id());
        let mut worklist = vec![entry];
        while let Some(bb_idx) = worklist.pop() {
            if !self.translated_cleanup_blocks.insert(bb_idx.index()) {
                continue;
            }
            let place = self.cleanup_place(bb_idx);
            let Some(term) = self.body.basic_blocks[bb_idx].terminator.clone() else {
                self.emit_cleanup_end(bb_idx, place, &fn_name);
                continue;
            };
            match &term.kind {
                TerminatorKind::Drop {
                    place: drop_place,
                    target,
                    ..
                } => {
                    self.emit_cleanup_step(
                        bb_idx,
                        place,
                        *target,
                        "cleanup_drop",
                        TransitionType::Drop,
                        Some(drop_place),
                        &fn_name,
                    );
                    worklist.push(*target);
                }
                TerminatorKind::Goto { target, .. } => {
                    self.emit_cleanup_step(
                        bb_idx,
                        place,
                        *target,
                        "cleanup_goto",
                        TransitionType::Goto,
                        None,
                        &fn_name,
                    );
                    worklist.push(*target);
                }
                TerminatorKind::SwitchInt { targets, .. } => {
                    // Drop-flag dispatch inside a cleanup chain: keep every
                    // successor (dropping and not dropping are both possible).
                    let successors = targets.all_targets();
                    let target_places: Vec<PlaceId> = successors
                        .iter()
                        .map(|target| self.cleanup_place(*target))
                        .collect();
                    for (n, (target, target_place)) in
                        successors.iter().zip(target_places).enumerate()
                    {
                        let t_name = crate::transition_name!(
                            &fn_name,
                            bb_idx,
                            "cleanup_switch",
                            (n + 1).to_string()
                        );
                        let span = self.bb_span(bb_idx);
                        let t_id =
                            self.new_transition(t_name, TransitionType::Switch, bb_idx, span);
                        self.record_guard_transition(bb_idx, t_id);
                        self.net.arc_in(place, t_id, 1);
                        self.net.arc_out(target_place, t_id, 1);
                        worklist.push(*target);
                    }
                }
                TerminatorKind::Call {
                    func, args, target, ..
                } => {
                    // Drop glue of the unwinding frame. Only a `drop_in_place`
                    // (or `drop`) call releases a guard; any other call is
                    // stepped over without touching resources.
                    let is_drop = self.callee_is_drop_in_place(func);
                    let drop_place = if is_drop {
                        args.first().and_then(|arg| arg.node.place())
                    } else {
                        None
                    };
                    let (kind, transition_type) = if is_drop {
                        ("cleanup_drop", TransitionType::Drop)
                    } else {
                        ("cleanup_call", TransitionType::Function)
                    };
                    match target {
                        Some(target) => {
                            self.emit_cleanup_step(
                                bb_idx,
                                place,
                                *target,
                                kind,
                                transition_type,
                                drop_place.as_ref(),
                                &fn_name,
                            );
                            worklist.push(*target);
                        }
                        None => self.emit_cleanup_end(bb_idx, place, &fn_name),
                    }
                }
                TerminatorKind::FalseEdge { real_target, .. }
                | TerminatorKind::FalseUnwind { real_target, .. } => {
                    self.emit_cleanup_step(
                        bb_idx,
                        place,
                        *real_target,
                        "cleanup_goto",
                        TransitionType::Goto,
                        None,
                        &fn_name,
                    );
                    worklist.push(*real_target);
                }
                TerminatorKind::Assert { target, .. } => {
                    // Same approximation as ordinary blocks: the success path.
                    self.emit_cleanup_step(
                        bb_idx,
                        place,
                        *target,
                        "cleanup_assert",
                        TransitionType::Assert,
                        None,
                        &fn_name,
                    );
                    worklist.push(*target);
                }
                TerminatorKind::Yield { resume, .. } => {
                    self.emit_cleanup_step(
                        bb_idx,
                        place,
                        *resume,
                        "cleanup_goto",
                        TransitionType::Goto,
                        None,
                        &fn_name,
                    );
                    worklist.push(*resume);
                }
                TerminatorKind::UnwindResume
                | TerminatorKind::UnwindTerminate(_)
                | TerminatorKind::Return
                | TerminatorKind::Unreachable
                | TerminatorKind::CoroutineDrop
                | TerminatorKind::TailCall { .. }
                | TerminatorKind::InlineAsm { .. } => {
                    self.emit_cleanup_end(bb_idx, place, &fn_name);
                }
            }
        }
    }

    /// One cleanup step: `place -> transition -> target_place`, releasing the
    /// guard in `drop_place` when it holds one.
    fn emit_cleanup_step(
        &mut self,
        bb_idx: BasicBlock,
        place: PlaceId,
        target: BasicBlock,
        kind: &str,
        transition_type: TransitionType,
        drop_place: Option<&rustc_middle::mir::Place<'tcx>>,
        fn_name: &str,
    ) {
        let t_name = crate::transition_name!(fn_name, bb_idx, kind);
        let span = self.bb_span(bb_idx);
        let t_id = self.new_transition(t_name, transition_type, bb_idx, span);
        self.net.arc_in(place, t_id, 1);
        let target_place = self.cleanup_place(target);
        self.net.arc_out(target_place, t_id, 1);
        if let Some(drop_place) = drop_place {
            self.add_guard_release_arcs(t_id, drop_place);
        }
    }

    /// The end of an unwind chain: the frame stops at its own function end.
    fn emit_cleanup_end(&mut self, bb_idx: BasicBlock, place: PlaceId, fn_name: &str) {
        let t_name = crate::transition_name!(fn_name, bb_idx, "cleanup_end");
        let span = self.bb_span(bb_idx);
        let t_id = self.new_transition(
            t_name,
            TransitionType::Return(self.instance_id.index()),
            bb_idx,
            span,
        );
        self.net.arc_in(place, t_id, 1);
        self.net.arc_out(self.frame_exit, t_id, 1);
    }

    /// Whether a cleanup call is drop glue (`drop_in_place` / `drop`).
    fn callee_is_drop_in_place(&self, func: &Operand<'tcx>) -> bool {
        match func.ty(self.body, self.tcx).kind() {
            rustc_middle::ty::TyKind::FnDef(def_id, _) => {
                let name = crate::util::format_name(*def_id);
                name.contains("drop_in_place") || name.contains("::drop")
            }
            _ => false,
        }
    }

    /// Whether the return block sets `_0` to `Poll::Pending` (a coroutine
    /// suspend) rather than `Poll::Ready` (completion).
    fn block_sets_poll_pending(&self, bb_idx: BasicBlock) -> bool {
        let bb = &self.body.basic_blocks[bb_idx];
        for stmt in &bb.statements {
            if let rustc_middle::mir::StatementKind::Assign((place, _)) = &stmt.kind {
                if place.local.index() == 0 {
                    return format!("{:?}", stmt.kind).contains("Pending");
                }
            }
        }
        false
    }

    /// Find the block a coroutine suspend resumes to: the poll switch that
    /// leads into the suspend block has the Ready/continuation as another
    /// target.
    fn find_suspend_continuation(&self, suspend_bb: BasicBlock) -> Option<BasicBlock> {
        for (_bb_idx, bb) in self.body.basic_blocks.iter_enumerated() {
            if let Some(term) = &bb.terminator {
                if let rustc_middle::mir::TerminatorKind::SwitchInt { targets, .. } = &term.kind {
                    if targets.all_targets().contains(&suspend_bb) {
                        for t in targets.all_targets() {
                            if *t != suspend_bb && !self.body.basic_blocks[*t].is_cleanup {
                                return Some(*t);
                            }
                        }
                    }
                }
            }
        }
        None
    }
}
