//! Loop cutting, summaries, and abandon returns.

use super::BodyToPetriNet;
use super::CutBackEdge;
use super::facts::LoopSummaryFacts;
use crate::translate::net::{ControlSub, PlaceClass, TransitionType};
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Operand, Rvalue, StatementKind, TerminatorKind,
};
use std::collections::VecDeque;

/// Whether a cut back edge may be replaced by a return to this frame's `_end`.
///
/// The question is whether the source block's exit still holds a lock guard,
/// not whether the frame or the crate has a guard somewhere. An early return
/// swallows a guard that is still live. A guard-less custom lock keeps its
/// held state on the receiver, which [`BodyToPetriNet::guards_held_at_back_edge`]
/// cannot see, so that frame stays cut.
fn abandon_shape_allows(
    custom_lock_method: bool,
    guards_at_cut: &[crate::analysis::primitives::blocking::LockGuardId],
) -> bool {
    if custom_lock_method {
        return false;
    }
    guards_at_cut.is_empty()
}

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// Turn a *stranded* cut back edge into a normal frame return.
    ///
    /// Problem : `LoopSemantics::Cut` drops the back edge without
    /// any substitute. When the back edge is its source block's only outgoing
    /// edge — the loop latch — the block's last place (the block start, or the
    /// `_unsafe_ready` place when the block has unsafe accesses) is left with
    /// no consumer. A synchronous callee whose loop only stops through that
    /// latch then never deposits a token in its `_end`, so every caller
    /// waiting in its `bb_ret` transition is reported as a control-blocked
    /// deadlock (parking_lot's `mark_parked_if_locked` / `lock_slow` are
    /// examples).
    ///
    /// Option (a) — restoring non-back-edge exits that
    /// cycle breaking wrongly deleted — does not apply: the *target* block
    /// keeps all its non-back-edge successors (`mark_parked_if_locked`'s loop
    /// header still branches to both returns). The strand is on the source
    /// side, and re-enabling the back edge would reintroduce the cycle.
    ///
    /// The fix is therefore option (c): a
    /// `..._loop_abandon_bb<src>_bb<dst>` return transition takes the
    /// stranded token to `frame_exit` when [`abandon_shape_allows`] says the
    /// latch does not still hold a guard. A guard that is live at the source
    /// block's exit, or a guard-less custom-lock method, keeps the cut: the
    /// early return would drop that held state. Any other cut back edge may
    /// return once, including a spawned closure whose guard was already
    /// dropped before the latch and a synchronous callee in a lock-using crate.
    ///
    /// This is an over-approximation in the same direction as unwind handling.
    /// The transition consumes one control token and produces one control
    /// token, so a state blocked on a lock stays blocked.
    ///
    /// A back edge whose source block still has another outgoing edge needs no
    /// fallback: the token can leave the block on that edge, so the frame can
    /// reach its `_end` without abandoning the loop.
    pub(super) fn emit_loop_abandon_returns(&mut self) {
        if !self.break_cfg_cycles {
            return;
        }
        let custom_lock_method = self
            .resources
            .custom_locks()
            .contains_key(&self.instance_id);
        let mut edges = self.cut_back_edges.clone();
        edges.sort_by_key(|edge| match edge {
            CutBackEdge::Direct { source, target } | CutBackEdge::After { source, target, .. } => {
                (source.index(), target.index())
            }
        });
        for edge in edges {
            let (source, target) = match edge {
                CutBackEdge::Direct { source, target }
                | CutBackEdge::After { source, target, .. } => (source, target),
            };
            let held = self.guards_held_at_back_edge(source);
            if !abandon_shape_allows(custom_lock_method, &held) {
                log::debug!(
                    "[loop-abandon] {}: bb{} -> bb{} custom_lock={} guards_at_cut={:?}; keeping the cut",
                    self.fn_path,
                    source.index(),
                    target.index(),
                    custom_lock_method,
                    held
                );
                continue;
            }
            let span = self.bb_span(source);
            let input = match edge {
                CutBackEdge::Direct { source, .. } => {
                    let Some(last) = self.bb_graph.last_opt(source) else {
                        continue;
                    };
                    if self.place_has_consumer(last) {
                        continue;
                    }
                    last
                }
                CutBackEdge::After { after, .. } => {
                    // The back edge was not wired, so this transition has no
                    // control successor. A resource output (the guard `Drop`
                    // unlock) does not count: the control token still needs a
                    // way out, or the frame's `_end` stays unreachable.
                    let trigger = self.net.add_place(
                        format!(
                            "{}_bb{}_loop_abandon_bb{}_trigger",
                            self.fn_path,
                            source.index(),
                            target.index()
                        ),
                        0,
                        usize::MAX,
                        PlaceClass::Control(ControlSub::FunctionEnd),
                        span.clone(),
                    );
                    self.net.arc_out(trigger, after, 1);
                    trigger
                }
            };
            let abandon = self.new_transition(
                format!(
                    "{}_bb{}_loop_abandon_bb{}",
                    self.fn_path,
                    source.index(),
                    target.index()
                ),
                TransitionType::Return(self.instance_id.index()),
                source,
                span,
            );
            self.net.arc_in(input, abandon, 1);
            self.net.arc_out(self.frame_exit, abandon, 1);
            log::debug!(
                "[loop-abandon] {}: bb{} -> bb{} returns the frame",
                self.fn_path,
                source.index(),
                target.index()
            );
        }
    }

    /// Remember that `edge` was dropped. Called at every site that implements
    /// cycle breaking; the summaries are emitted once the whole body exists.
    pub(super) fn record_cut_back_edge(&mut self, edge: CutBackEdge) {
        debug_assert!(self.break_cfg_cycles);
        self.cut_back_edges.push(edge);
    }

    /// Emit one loop-summary transition per cut back edge.
    ///
    /// For a `Direct` edge the summary is `last(source) + budget -> start(target)`;
    /// for an `After` edge it is `trigger + budget -> start(target)`, where
    /// `after` now produces `trigger`. The budget place holds exactly
    /// `loop_summary_k` initial tokens (one), so the loop body can be
    /// re-entered that many times and the cycle is still cut afterwards
    /// (bounded unroll k). No resource arc is added: the summary only moves
    /// control, so the resource accounting of the original transitions is
    /// unchanged.
    ///
    /// The budget and trigger places are `Control(FunctionEnd)`: their tokens
    /// are bookkeeping, never a thread position, and `is_terminal` is what
    /// keeps an unconsumed budget from turning a normal termination into a
    /// fake blocked place. They are not `Resource` places, so they are not
    /// slicing keys and a blocked summary never reads as a resource wait.
    ///
    /// Once the budget is spent, the back edge is cut again. A
    /// `..._fallback` transition from the same trigger makes that final cut
    /// *terminal*: without it the latch place would have an outgoing arc (the
    /// summary) and an exhausted budget token, which the state graph would
    /// report as a fresh control deadlock.
    ///
    /// The fallback now deposits the token in this frame's `_end`
    /// instead of a private cut sink. showed why the sink was wrong
    /// at a synchronous call boundary: a callee whose loop stopped at the
    /// fallback never produced `_end`, so every caller waiting in `bb_ret` was
    /// reported as a control-blocked deadlock. "The loop did not finish, so
    /// treat the frame as having returned" is an over-approximation in the
    /// same direction as the existing unwind handling. It cannot enable a
    /// resource wait (one control token in, one control token out), so a
    /// state blocked on a lock stays blocked; it can only remove the
    /// control-blocked states the sink produced. Guards that an abandoned
    /// loop body still holds stay consumed, unchanged from the old cut sink.
    ///
    /// The fallback is enabled before the summary fires; that only adds the
    /// "leave the loop after k iterations" marking (k = 0..loop_summary_k)
    /// and never removes a state reachable through the summary, so it cannot
    /// hide a real deadlock.
    pub(super) fn emit_loop_summaries(&mut self) {
        if !self.break_cfg_cycles {
            log::warn!(
                "loop_semantics=summary requires break_cfg_cycles; the loops of {} are left intact",
                self.fn_path
            );
            return;
        }
        let mut edges = self.cut_back_edges.clone();
        edges.sort_by_key(|edge| match edge {
            CutBackEdge::Direct { source, target } | CutBackEdge::After { source, target, .. } => {
                (source.index(), target.index())
            }
        });
        for edge in edges {
            let (source, target) = match edge {
                CutBackEdge::Direct { source, target }
                | CutBackEdge::After { source, target, .. } => (source, target),
            };
            let Some(target_start) = self.bb_graph.start_opt(target) else {
                log::warn!(
                    "loop summary bb{} -> bb{} skipped: target has no start place",
                    source.index(),
                    target.index()
                );
                continue;
            };
            let trigger = match edge {
                CutBackEdge::Direct { source, .. } => {
                    let Some(trigger) = self.bb_graph.last_opt(source) else {
                        continue;
                    };
                    trigger
                }
                CutBackEdge::After { source, after, .. } => {
                    let name = format!(
                        "{}_bb{}_loop_summary_bb{}_trigger",
                        self.fn_path,
                        source.index(),
                        target.index()
                    );
                    let span = self.bb_span(source);
                    let trigger = self.net.add_place(
                        name,
                        0,
                        usize::MAX,
                        PlaceClass::Control(ControlSub::FunctionEnd),
                        span,
                    );
                    self.net.arc_out(trigger, after, 1);
                    trigger
                }
            };

            let span = self.bb_span(source);
            let budget_name = format!(
                "{}_bb{}_loop_summary_bb{}_budget",
                self.fn_path,
                source.index(),
                target.index()
            );
            let budget = self.net.add_place(
                budget_name,
                self.loop_summary_k,
                usize::MAX,
                PlaceClass::Control(ControlSub::FunctionEnd),
                span.clone(),
            );
            let summary_name = format!(
                "{}_bb{}_loop_summary_bb{}",
                self.fn_path,
                source.index(),
                target.index()
            );
            let summary =
                self.new_transition(summary_name, TransitionType::Normal, source, span.clone());
            self.net.arc_in(trigger, summary, 1);
            self.net.arc_in(budget, summary, 1);
            self.net.arc_out(target_start, summary, 1);

            let fallback = self.new_transition(
                format!(
                    "{}_bb{}_loop_summary_bb{}_fallback",
                    self.fn_path,
                    source.index(),
                    target.index()
                ),
                TransitionType::Normal,
                source,
                span,
            );
            self.net.arc_in(trigger, fallback, 1);
            // "Loop unfinished -> normal return": see the doc comment above.
            // Any lock guard that is still held at the exit of `source` (across
            // the back edge `source -> target`, e.g. the guard re-acquired by
            // `Condvar::wait` inside `while !pred { guard = cv.wait(guard) }`)
            // must be released on `fallback` because this transition bypasses
            // the loop's normal exit `Drop` block and terminates the frame at
            // `frame_exit`.
            // Kept here. `ResourceBinder` only assigns the resource
            // place; this fallback is what puts the token back.
            for guard_id in self.guards_held_at_back_edge(source) {
                self.add_guard_id_release_arcs(fallback, guard_id);
            }
            self.net.arc_out(self.frame_exit, fallback, 1);

            self.net
                .provenance_mut()
                .functions
                .entry(self.fn_path.clone())
                .or_default()
                .loop_summaries
                .push(LoopSummaryFacts {
                    from_bb: source.index(),
                    to_bb: target.index(),
                    transition: summary.index(),
                    fallback_transition: fallback.index(),
                });
            log::debug!(
                "[loop-summary] {}: bb{} -> bb{} (k={})",
                self.fn_path,
                source.index(),
                target.index(),
                self.loop_summary_k
            );
        }
    }

    /// Lock guards of this frame that are still held at the exit of `source`
    /// (across the cut back edge `source -> target`).
    fn guards_held_at_back_edge(
        &self,
        source: BasicBlock,
    ) -> Vec<crate::analysis::primitives::blocking::LockGuardId> {
        let mut frame_guards: Vec<crate::analysis::primitives::blocking::LockGuardId> = self
            .lockguards
            .keys()
            .filter(|g| g.instance_id == self.instance_id)
            .copied()
            .collect();
        frame_guards.sort_by_key(|g| (g.local.as_u32(), g.field));

        frame_guards
            .into_iter()
            .filter(|&guard_id| self.guard_reaches_block_exit_held(guard_id, source))
            .collect()
    }

    pub(super) fn guard_reaches_block_exit_held(
        &self,
        guard_id: crate::analysis::primitives::blocking::LockGuardId,
        target_source: BasicBlock,
    ) -> bool {
        let num_bbs = self.body.basic_blocks.len();
        let mut entered_held = vec![false; num_bbs];
        let mut exited_held = vec![false; num_bbs];
        let mut worklist: VecDeque<BasicBlock> = VecDeque::new();

        for (bb_idx, bb) in self.body.basic_blocks.iter_enumerated() {
            if bb.is_cleanup || bb.is_empty_unreachable() {
                continue;
            }
            if self.eval_block_for_guard(bb, guard_id, false) {
                worklist.push_back(bb_idx);
            }
        }

        while let Some(bb_idx) = worklist.pop_front() {
            let bb = &self.body.basic_blocks[bb_idx];
            if bb.is_cleanup || bb.is_empty_unreachable() {
                continue;
            }
            let held_at_exit =
                self.eval_block_for_guard(bb, guard_id, entered_held[bb_idx.index()]);
            if held_at_exit && !exited_held[bb_idx.index()] {
                exited_held[bb_idx.index()] = true;
                if bb_idx == target_source {
                    return true;
                }
                if let Some(term) = &bb.terminator {
                    for succ in term.successors() {
                        if self.body.basic_blocks[succ].is_cleanup {
                            continue;
                        }
                        if self.is_back_edge(bb_idx, succ) {
                            continue;
                        }
                        if !entered_held[succ.index()] {
                            entered_held[succ.index()] = true;
                            worklist.push_back(succ);
                        }
                    }
                }
            }
        }

        exited_held
            .get(target_source.index())
            .copied()
            .unwrap_or(false)
    }

    /// Transfer function for `guard_id` across a single basic block `bb`:
    /// starting with `held` at block entry, updates `held` through statement
    /// moves/assignments and terminator drops/calls.
    fn eval_block_for_guard(
        &self,
        bb: &BasicBlockData<'tcx>,
        guard_id: crate::analysis::primitives::blocking::LockGuardId,
        mut held: bool,
    ) -> bool {
        for stmt in &bb.statements {
            if let StatementKind::Assign(boxed) = &stmt.kind {
                let (dest, rvalue) = &**boxed;
                if let Rvalue::Use(Operand::Move(src), _) = rvalue {
                    if Self::lockguard_id_for_dest(self.instance_id, src) == guard_id {
                        held = false;
                    }
                }
                if Self::lockguard_id_for_dest(self.instance_id, dest) == guard_id {
                    held = true;
                }
            }
        }
        if let Some(term) = &bb.terminator {
            match &term.kind {
                TerminatorKind::Drop { place, .. } => {
                    if Self::lockguard_id_for_dest(self.instance_id, place) == guard_id {
                        held = false;
                    }
                }
                TerminatorKind::Call {
                    args,
                    destination,
                    target: Some(_),
                    ..
                } => {
                    for arg in args.iter() {
                        if let Operand::Move(src) = &arg.node {
                            if Self::lockguard_id_for_dest(self.instance_id, src) == guard_id {
                                held = false;
                            }
                        }
                    }
                    if Self::lockguard_id_for_dest(self.instance_id, destination) == guard_id {
                        held = true;
                    }
                }
                _ => {}
            }
        }
        held
    }
}

#[cfg(test)]
mod tests {
    use super::abandon_shape_allows;
    use crate::analysis::callgraph::InstanceId;
    use crate::analysis::primitives::blocking::LockGuardId;
    use crate::translate::net::{
        NetBuilder, PlaceClass, PlaceId, ResourceKind, StateGraph, TransitionKind, TransitionType,
    };
    use rustc_middle::mir::Local;

    /// The caller waits on `callee_end` (its `bb_ret` transition); the callee
    /// latch holds a token but has no outgoing edge after the cut.
    fn boundary_net() -> (NetBuilder<'static>, PlaceId, PlaceId, PlaceId) {
        let mut net = NetBuilder::new();
        let wait = crate::translate::net::control_place(&mut net, "caller_bb_wait", 1);
        let latch = crate::translate::net::control_place(&mut net, "callee_bb_latch", 1);
        let callee_end = crate::translate::net::function_end(&mut net, "callee_end");
        let ret = net.transition(
            TransitionKind::new(TransitionType::Function),
            "caller_bb_ret",
        );
        net.arc_in(callee_end, ret, 1);
        net.arc_in(wait, ret, 1);
        (net, latch, wait, callee_end)
    }

    #[test]
    fn cut_loop_latch_without_substitute_is_a_control_deadlock() {
        let (net, _latch, _wait, _end) = boundary_net();
        let (pt, marking) = net.finish();
        let graph = StateGraph::from_net(&pt, marking);
        assert_eq!(
            graph.deadlock_states(&pt).len(),
            1,
            "the caller's wait on a callee `_end` that no transition produces \
             must be reported as a deadlock (that false candidate)"
        );
    }

    #[test]
    fn loop_abandon_transition_returns_the_frame_and_clears_the_deadlock() {
        let (mut net, latch, _wait, callee_end) = boundary_net();
        // Exactly what `emit_loop_abandon_returns` adds for a stranded latch:
        // one control token in, one `_end` token out.
        let abandon = net.transition(
            TransitionKind::new(TransitionType::Return(0)),
            "callee_bb_latch_loop_abandon",
        );
        net.arc_in(latch, abandon, 1);
        net.arc_out(callee_end, abandon, 1);
        let (pt, marking) = net.finish();
        let graph = StateGraph::from_net(&pt, marking);
        assert!(
            graph.deadlock_states(&pt).is_empty(),
            "the abandon transition must let the callee produce `_end` and the \
             caller's wait must become satisfiable"
        );
    }

    // the closure shape condition ───────────────────────────────

    #[test]
    fn abandon_allows_a_cut_whose_exit_holds_no_guard() {
        assert!(abandon_shape_allows(false, &[]));
    }

    #[test]
    fn abandon_refuses_a_cut_that_still_holds_a_guard() {
        let guard = LockGuardId::new(InstanceId::new(0), Local::from_u32(1));
        assert!(!abandon_shape_allows(false, &[guard]));
    }

    #[test]
    fn abandon_refuses_a_guardless_custom_lock_method() {
        assert!(!abandon_shape_allows(true, &[]));
    }

    #[test]
    fn loop_summary_fallback_releasing_held_guard_prevents_mutex_leak() {
        let mut net = NetBuilder::new();
        let mutex = net.place(PlaceClass::Resource(ResourceKind::Mutex), "Mutex_0", 1);
        let set_entry = crate::translate::net::control_place(&mut net, "set_1", 1);
        let set_end = crate::translate::net::function_end(&mut net, "set_end");
        let wait_latch = crate::translate::net::control_place(&mut net, "wait_for_10", 1);
        let wait_end = crate::translate::net::function_end(&mut net, "wait_for_end");

        let set_lock = net.transition(
            TransitionKind::new(TransitionType::Lock(mutex.index())),
            "set_lock",
        );
        net.arc_in(set_entry, set_lock, 1);
        net.arc_in(mutex, set_lock, 1);
        net.arc_out(set_end, set_lock, 1);

        let fallback = net.transition(
            TransitionKind::new(TransitionType::Unlock(mutex.index())),
            "wait_for_bb10_loop_summary_bb5_fallback",
        );
        net.arc_in(wait_latch, fallback, 1);
        net.arc_out(mutex, fallback, 1);
        net.arc_out(wait_end, fallback, 1);

        let (pt, marking) = net.finish();
        let graph = StateGraph::from_net(&pt, marking);
        assert!(
            graph.deadlock_states(&pt).is_empty(),
            "releasing the held mutex guard on the loop-summary fallback must allow `set` to acquire Mutex_0"
        );
    }
}
