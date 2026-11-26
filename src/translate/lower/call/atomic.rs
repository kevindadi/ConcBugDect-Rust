//! Atomic load, store, and read-modify-write.

use super::super::BodyToPetriNet;
use crate::analysis::memory::pointsto::AliasId;
use crate::analysis::primitives::atomic::AtomicApi;
use crate::analysis::primitives::atomic::AtomicOrdering;
use crate::translate::net::NetBuilder;
use crate::translate::net::{ControlSub, PlaceClass, PlaceId};
use crate::translate::net::{TransitionId, TransitionType};
use rustc_middle::mir::{BasicBlock, Operand};
use rustc_span::Spanned;

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// TODO: load, store, and RMW take their places from `find_atomic_matches`
    /// (an alias scan), not from `ResourceMap::place`.
    pub(in crate::translate::lower) fn handle_atomic_call(
        &mut self,
        callee_func_name: &str,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        bb_idx: &BasicBlock,
        span: &str,
    ) -> bool {
        match self.key_api_regex.atomic_api(callee_func_name) {
            Some(AtomicApi::Read) => {
                if !self.handle_atomic_load(args, bb_end, target, bb_idx, span) {
                    log::debug!("no alias found for atomic load in {:?}", span);
                    self.connect_to_target(*bb_idx, bb_end, target);
                }
                true
            }
            Some(AtomicApi::Write) => {
                if !self.handle_atomic_store(args, bb_end, target, bb_idx, span) {
                    log::debug!("no alias found for atomic store in {:?}", span);
                    self.connect_to_target(*bb_idx, bb_end, target);
                }
                true
            }
            Some(AtomicApi::ReadWrite) => {
                if !self.handle_atomic_rmw(args, bb_end, target, bb_idx, span) {
                    log::debug!("no alias found for atomic read-modify-write in {:?}", span);
                    self.connect_to_target(*bb_idx, bb_end, target);
                }
                true
            }
            _ => false,
        }
    }

    pub(in crate::translate::lower) fn handle_atomic_load(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        bb_idx: &BasicBlock,
        span: &str,
    ) -> bool {
        let current_id = AliasId::new(
            self.instance_id,
            args.first().unwrap().node.place().unwrap().local,
        );

        let instance_index = self.instance_id.index();
        self.handle_atomic_basic_op(
            "load",
            current_id,
            bb_end,
            target,
            bb_idx,
            span,
            move |alias_id, order, span_str| {
                TransitionType::AtomicLoad(
                    alias_id.clone().into(),
                    order.clone().into(),
                    span_str,
                    instance_index,
                )
            },
        )
    }

    pub(in crate::translate::lower) fn handle_atomic_store(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        bb_idx: &BasicBlock,
        span: &str,
    ) -> bool {
        let current_id = AliasId::new(
            self.instance_id,
            args.first().unwrap().node.place().unwrap().local,
        );
        let instance_index = self.instance_id.index();
        self.handle_atomic_basic_op(
            "store",
            current_id,
            bb_end,
            target,
            bb_idx,
            span,
            move |alias_id, order, span_str| {
                TransitionType::AtomicStore(
                    alias_id.clone().into(),
                    order.clone().into(),
                    span_str,
                    instance_index,
                )
            },
        )
    }

    /// Read-modify-write (`swap`, `compare_exchange`, `fetch_*`). Same token
    /// shape as load/store: the transition takes the atomic resource and puts
    /// it back. `TransitionType` has no separate RMW variant, so this uses
    /// `AtomicCmpXchg` with the one ordering the collector recorded for both
    /// the success and failure positions.
    pub(in crate::translate::lower) fn handle_atomic_rmw(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        bb_idx: &BasicBlock,
        span: &str,
    ) -> bool {
        let current_id = AliasId::new(
            self.instance_id,
            args.first().unwrap().node.place().unwrap().local,
        );
        let instance_index = self.instance_id.index();
        self.handle_atomic_basic_op(
            "rmw",
            current_id,
            bb_end,
            target,
            bb_idx,
            span,
            move |alias_id, order, span_str| {
                TransitionType::AtomicCmpXchg(
                    alias_id.clone().into(),
                    order.clone().into(),
                    order.clone().into(),
                    span_str,
                    instance_index,
                )
            },
        )
    }
}

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// All matching `(alias_id, place_id)` pairs (no longer first-match only).
    ///
    /// TODO: this is an `alias_atomic` scan. The operand local is not the
    /// collected atomic's `SiteKey`, and one call can touch several places,
    /// so it does not go through `ResourceMap::place`.
    pub(super) fn find_atomic_matches(&mut self, current_id: &AliasId) -> Vec<(AliasId, PlaceId)> {
        let mut matches = Vec::new();
        for (alias_id, place_ids) in self.resources.atomic_places().iter() {
            if self
                .alias
                .borrow_mut()
                .alias_atomic(*current_id, *alias_id)
                .may_alias(self.alias_unknown_policy)
            {
                for &place_id in place_ids {
                    if !matches.iter().any(|(_, matched)| *matched == place_id) {
                        matches.push((*alias_id, place_id));
                    }
                }
            }
        }
        matches
    }

    pub(super) fn handle_atomic_basic_op<F>(
        &mut self,
        op_name: &str,
        current_id: AliasId,
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        bb_idx: &BasicBlock,
        span: &str,
        mut transition_builder: F,
    ) -> bool
    where
        F: FnMut(&AliasId, &AtomicOrdering, String) -> TransitionType,
    {
        let matches = self.find_atomic_matches(&current_id);
        if matches.is_empty() {
            return false;
        }

        let Some(order) = self.resources.atomic_orders().get(&current_id).copied() else {
            log::warn!(
                "[atomicity] missing ordering for atomic {} @ {:?}",
                op_name,
                span
            );
            return false;
        };

        let tid = self.instance_id.index();
        let span_owned = span.to_string();
        let intermediate_name = format!(
            "atomic_{}_in_{:?}_{:?}",
            op_name,
            current_id.instance_id.index(),
            bb_idx.index()
        );
        let intermediate_id = crate::bb_place!(self.net, intermediate_name, span_owned.clone());
        self.net.arc_out(intermediate_id, bb_end, 1);

        // Ordering segments are computed once per MIR operation and shared by
        // every alias alternative, so an acquire/release/seqcst op advances the
        // thread's segment exactly once no matter which candidate fires.
        // Only modeled for `atomic` / `all` modes; other detectors skip the
        // memory-ordering sequencing.
        let seg_arcs = if self.translate_atomic_ordering {
            self.ordering_seg_arcs(tid, order)
        } else {
            Vec::new()
        };

        for (idx, (alias_id, resource_place)) in matches.into_iter().enumerate() {
            let transition_name = format!(
                "atomic_{:?}_{}_{:?}_{:?}_{}",
                self.instance_id.index(),
                op_name,
                order,
                bb_idx.index(),
                idx
            );
            let transition_type = transition_builder(&alias_id, &order, span_owned.clone());
            let span = span_owned.clone();
            let transition_id =
                self.new_transition(transition_name, transition_type, *bb_idx, span);

            self.net.arc_in(intermediate_id, transition_id, 1);
            wire_atomic_token(&mut self.net, resource_place, transition_id);

            for &(place_id, is_input) in &seg_arcs {
                if is_input {
                    self.net.arc_in(place_id, transition_id, 1);
                } else {
                    self.net.arc_out(place_id, transition_id, 1);
                }
            }

            if let Some(t) = target {
                self.net.arc_out(self.bb_graph.start(*t), transition_id, 1);
            }
        }
        true
    }

    pub(in crate::translate::lower) fn ensure_seg_place(
        &mut self,
        tid: usize,
        seg: usize,
    ) -> PlaceId {
        if let Some(&place_id) = self.seg.seg_place_of.get(&(tid, seg)) {
            return place_id;
        }

        let name = format!("seg_t{}_s{}", tid, seg);
        let tokens = if seg == 0 { 1 } else { 0 };
        let place_id = if tokens == 0 {
            self.net.place(
                PlaceClass::Control(ControlSub::BasicBlock),
                name,
                usize::MAX,
            )
        } else {
            self.net
                .marked_place(PlaceClass::Control(ControlSub::BasicBlock), name, tokens)
        };
        self.seg.seg_place_of.insert((tid, seg), place_id);
        place_id
    }

    fn ensure_seqcst_place(&mut self) -> PlaceId {
        if let Some(place_id) = self.seg.seqcst_place {
            return place_id;
        }

        let place_id = self.net.marked_place(
            PlaceClass::Resource(()),
            "SeqCst_Global",
            1,
        );
        self.seg.seqcst_place = Some(place_id);
        place_id
    }

    /// Segment arcs for one atomic operation: `(place, is_input)`.
    /// Relaxed keeps the current segment token in place; acquire/release/acqrel
    /// advance the per-thread segment; seqcst additionally synchronizes on a
    /// global place that serializes all seqcst operations across threads.
    fn ordering_seg_arcs(&mut self, tid: usize, ord: AtomicOrdering) -> Vec<(PlaceId, bool)> {
        let mut arcs = Vec::new();
        let current_seg = self.seg.current_seg(tid);
        let current_place = self.ensure_seg_place(tid, current_seg);

        match ord {
            AtomicOrdering::Relaxed => {
                arcs.push((current_place, true));
                arcs.push((current_place, false));
            }
            AtomicOrdering::Acquire | AtomicOrdering::Release | AtomicOrdering::AcqRel => {
                let next_seg = self.seg.bump(tid);
                let next_place = self.ensure_seg_place(tid, next_seg);
                arcs.push((current_place, true));
                arcs.push((next_place, false));
            }
            AtomicOrdering::SeqCst => {
                let next_seg = self.seg.bump(tid);
                let next_place = self.ensure_seg_place(tid, next_seg);
                let seqcst_place = self.ensure_seqcst_place();
                arcs.push((current_place, true));
                arcs.push((next_place, false));
                arcs.push((seqcst_place, true));
                arcs.push((seqcst_place, false));
            }
        }

        arcs
    }
}

/// Consume the atomic resource and put the token back on the same transition.
/// Load, store, and read-modify-write all use this shape.
pub(super) fn wire_atomic_token(
    net: &mut NetBuilder<'_>,
    place: PlaceId,
    transition: TransitionId,
) {
    net.arc_in(place, transition, 1);
    net.arc_out(place, transition, 1);
}

#[cfg(test)]
mod tests {
    use super::wire_atomic_token;
    use crate::translate::net::{NetBuilder, PlaceClass, TransitionKind, TransitionType};

    #[test]
    fn rmw_takes_the_atomic_token_and_puts_it_back() {
        let mut net = NetBuilder::new();
        let place = net.marked_place(PlaceClass::Resource(()), "Atomic(1,2)", 1);
        let transition = net.transition(TransitionKind::new(TransitionType::Normal), "rmw");
        wire_atomic_token(&mut net, place, transition);
        assert!(net.fans_out(place));
        let (_net, marking) = net.finish();
        assert_eq!(marking.tokens(place), 1);
    }
}
