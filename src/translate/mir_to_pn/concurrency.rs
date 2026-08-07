//! Concurrency primitives: locks, condvars, channels, atomics.

use super::BodyToPetriNet;
#[cfg(feature = "atomic-violation")]
use crate::net::{Place, structure::PlaceType};
use crate::{
    concurrency::atomic::AtomicOrdering,
    memory::pointsto::AliasId,
    net::{PlaceId, TransitionId, TransitionType},
};
#[cfg(not(feature = "atomic-violation"))]
use crate::net::Transition;
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

    #[cfg(feature = "atomic-violation")]
    pub(super) fn handle_atomic_basic_op<F>(
        &mut self,
        op_name: &str,
        current_id: AliasId,
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        bb_idx: &BasicBlock,
        span: &str,
        _transition_builder: F,
    ) -> bool
    where
        F: FnMut(&AliasId, &AtomicOrdering, String) -> TransitionType,
    {
        self.link_atomic_operation(op_name, current_id, bb_end, target, bb_idx, span)
    }

    #[cfg(not(feature = "atomic-violation"))]
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
        let span_owned = span.to_string();
        let intermediate_name = format!(
            "atomic_{}_in_{:?}_{:?}",
            op_name,
            current_id.instance_id.index(),
            bb_idx.index()
        );
        let intermediate_id = crate::bb_place!(self.net, intermediate_name, span_owned.clone());
        self.net.add_input_arc(intermediate_id, bb_end, 1);

        if let Some(order) = self.resources.atomic_orders().get(&current_id) {
            for (idx, (alias_id, resource_place)) in matches.into_iter().enumerate() {
                let transition_name = format!(
                    "atomic_{:?}_{}_{:?}_{:?}_{}",
                    self.instance_id.index(),
                    op_name,
                    order,
                    bb_idx.index(),
                    idx
                );
                let transition_type = transition_builder(&alias_id, order, span_owned.clone());
                let transition =
                    Transition::new_with_transition_type(transition_name, transition_type);
                let transition_id = self.net.add_transition(transition);

                self.net.add_output_arc(intermediate_id, transition_id, 1);
                self.net.add_input_arc(resource_place, transition_id, 1);
                self.net.add_output_arc(resource_place, transition_id, 1);

                if let Some(t) = target {
                    self.net
                        .add_input_arc(self.bb_graph.start(*t), transition_id, 1);
                }
            }
        }
        true
    }

    #[cfg(feature = "atomic-violation")]
    fn link_atomic_operation(
        &mut self,
        op_name: &str,
        current_id: AliasId,
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        bb_idx: &BasicBlock,
        span: &str,
    ) -> bool {
        let matches = self.find_atomic_matches(&current_id);
        if matches.is_empty() {
            log::warn!("no alias found for atomic operation in {:?}", span);
            return false;
        }

        let Some(order) = self.resources.atomic_orders().get(&current_id).copied() else {
            log::warn!(
                "[atomic-violation] missing ordering for {} @ {:?}",
                op_name,
                span
            );
            self.connect_to_target(*bb_idx, bb_end, target);
            return true;
        };

        let tid = self.instance_id.index();
        let span_owned = span.to_string();
        let alias_id = matches.first().map(|(a, _)| *a).unwrap_or(current_id);

        let transition_name = {
            let name = format!(
                "atomic_{:?}_{}_ord={:?}_bb={}",
                self.instance_id.index(),
                op_name,
                order,
                bb_idx.index()
            );
            if let Some(transition) = self.net.get_transition_mut(bb_end) {
                transition.name = name.clone();
                transition.transition_type = match op_name {
                    "load" => TransitionType::AtomicLoad(alias_id, order, span_owned.clone(), tid),
                    "store" => {
                        TransitionType::AtomicStore(alias_id, order, span_owned.clone(), tid)
                    }
                    _ => transition.transition_type.clone(),
                };
            } else {
                return false;
            }
            name
        };

        for (_, resource_place) in matches {
            self.net.add_input_arc(resource_place, bb_end, 1);
            self.net.add_output_arc(resource_place, bb_end, 1);
        }
        self.wire_segment_for_ordering(bb_end, tid, order);
        self.connect_to_target(*bb_idx, bb_end, target);

        log::debug!(
            "[atomic-violation] wired {} at {:?} with ord={:?}, tid={}, alias={:?}",
            transition_name,
            span,
            order,
            tid,
            alias_id
        );

        true
    }

    #[cfg(feature = "atomic-violation")]
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

    #[cfg(feature = "atomic-violation")]
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

    #[cfg(feature = "atomic-violation")]
    fn wire_segment_for_ordering(&mut self, bb_end: TransitionId, tid: usize, ord: AtomicOrdering) {
        let current_seg = self.seg.current_seg(tid);
        let current_place = self.ensure_seg_place(tid, current_seg);

        match ord {
            AtomicOrdering::Relaxed => {
                self.net.add_input_arc(current_place, bb_end, 1);
                self.net.add_output_arc(current_place, bb_end, 1);
            }
            AtomicOrdering::Acquire | AtomicOrdering::Release | AtomicOrdering::AcqRel => {
                let next_seg = self.seg.bump(tid);
                let next_place = self.ensure_seg_place(tid, next_seg);
                self.net.add_input_arc(current_place, bb_end, 1);
                self.net.add_output_arc(next_place, bb_end, 1);
            }
            AtomicOrdering::SeqCst => {
                let next_seg = self.seg.bump(tid);
                let next_place = self.ensure_seg_place(tid, next_seg);
                self.net.add_input_arc(current_place, bb_end, 1);
                self.net.add_output_arc(next_place, bb_end, 1);
                let seqcst_place = self.ensure_seqcst_place();
                self.net.add_input_arc(seqcst_place, bb_end, 1);
                self.net.add_output_arc(seqcst_place, bb_end, 1);
            }
        }
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
