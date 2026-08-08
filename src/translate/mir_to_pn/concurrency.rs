//! Concurrency primitives: locks, condvars, channels, atomics.

use super::BodyToPetriNet;
use crate::{
    concurrency::atomic::AtomicOrdering,
    memory::pointsto::AliasId,
    net::{Place, PlaceId, Transition, TransitionId, TransitionType, structure::PlaceType},
};
use rustc_middle::mir::BasicBlock;

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// All matching `(alias_id, place_id)` pairs (no longer first-match only).
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
        self.net.add_output_arc(intermediate_id, bb_end, 1);

        // Ordering segments are computed once per MIR operation and shared by
        // every alias alternative, so an acquire/release/seqcst op advances the
        // thread's segment exactly once no matter which candidate fires.
        let seg_arcs = self.ordering_seg_arcs(tid, order);

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
            let transition =
                Transition::new_with_transition_type(transition_name, transition_type);
            let transition_id = self.net.add_transition(transition);

            self.net.add_input_arc(intermediate_id, transition_id, 1);
            self.net.add_input_arc(resource_place, transition_id, 1);
            self.net.add_output_arc(resource_place, transition_id, 1);

            for &(place_id, is_input) in &seg_arcs {
                if is_input {
                    self.net.add_input_arc(place_id, transition_id, 1);
                } else {
                    self.net.add_output_arc(place_id, transition_id, 1);
                }
            }

            if let Some(t) = target {
                self.net
                    .add_output_arc(self.bb_graph.start(*t), transition_id, 1);
            }
        }
        true
    }

    pub(super) fn ensure_seg_place(&mut self, tid: usize, seg: usize) -> PlaceId {
        if let Some(&place_id) = self.seg.seg_place_of.get(&(tid, seg)) {
            return place_id;
        }

        let name = format!("seg_t{}_s{}", tid, seg);
        let tokens = if seg == 0 { 1 } else { 0 };
        let place = Place::new(name, tokens, u64::MAX, PlaceType::BasicBlock, String::new());
        let place_id = self.net.add_place(place);
        self.seg.seg_place_of.insert((tid, seg), place_id);
        place_id
    }

    fn ensure_seqcst_place(&mut self) -> PlaceId {
        if let Some(place_id) = self.seg.seqcst_place {
            return place_id;
        }

        let place = Place::new(
            "SeqCst_Global",
            1,
            u64::MAX,
            PlaceType::Resources,
            String::new(),
        );
        let place_id = self.net.add_place(place);
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

    pub(super) fn find_channel_place(&mut self, channel_alias: AliasId) -> Option<PlaceId> {
        for (alias_id, node) in self.resources.channel_places().iter() {
            let alias_kind = self
                .alias
                .borrow_mut()
                .alias_atomic(channel_alias, *alias_id);
            if alias_kind.may_alias(self.alias_unknown_policy) {
                return Some(*node);
            }
        }
        None
    }
}
