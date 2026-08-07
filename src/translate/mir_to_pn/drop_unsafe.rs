//! `Drop` and unsafe read/write helpers: `handle_drop`, `process_rvalue_reads`, `process_place_writes`.

use super::BodyToPetriNet;
use crate::{
    concurrency::blocking::{LockGuardId, LockGuardTy},
    memory::pointsto::AliasId,
    net::{Idx, PlaceId, Transition, TransitionType},
    translate::mir_utils::rvalue_read_places,
};
use rustc_middle::mir::{BasicBlock, BasicBlockData, Rvalue};

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    pub(super) fn handle_drop(
        &mut self,
        bb_idx: &BasicBlock,
        place: &rustc_middle::mir::Place<'tcx>,
        target: &BasicBlock,
        name: &str,
        bb: &BasicBlockData<'tcx>,
    ) {
        let bb_term_name = crate::transition_name!(name, bb_idx, "drop");
        let bb_term_transition =
            Transition::new_with_transition_type(bb_term_name, TransitionType::Drop);
        let bb_end = self.net.add_transition(bb_term_transition);

        self.net
            .add_input_arc(self.bb_graph.last(*bb_idx), bb_end, 1);

        if cfg!(feature = "atomic-violation") {
            if !self.is_back_edge(*bb_idx, *target) {
                self.net
                    .add_output_arc(self.bb_graph.start(*target), bb_end, 1);
            }
            return;
        }

        if !bb.is_cleanup {
            let lockguard_id = LockGuardId::new(self.instance_id, place.local);

            if self.lockguards.get(&lockguard_id).is_some() {
                let lock_alias = lockguard_id.get_alias_id();
                let lock_node = self.resources.locks().get(&lock_alias).unwrap();
                match &self.lockguards[&lockguard_id].lockguard_ty {
                    LockGuardTy::StdMutex(_)
                    | LockGuardTy::ParkingLotMutex(_)
                    | LockGuardTy::SpinMutex(_)
                    | LockGuardTy::StdRwLockRead(_)
                    | LockGuardTy::ParkingLotRead(_)
                    | LockGuardTy::SpinRead(_) => {
                        self.net.add_output_arc(*lock_node, bb_end, 1);
                    }
                    _ => {
                        self.net.add_output_arc(*lock_node, bb_end, 10);
                    }
                }

                if let Some(transition) = self.net.get_transition_mut(bb_end) {
                    transition.transition_type = TransitionType::Unlock(lock_node.index());
                }
            }
        }

        if !self.is_back_edge(*bb_idx, *target) {
            self.net
                .add_output_arc(self.bb_graph.start(*target), bb_end, 1);
        }
    }

    pub(super) fn has_unsafe_alias(&self, place_id: AliasId) -> (bool, PlaceId, Option<AliasId>) {
        for (unsafe_place, node_index) in self.resources.unsafe_places().iter() {
            if self
                .alias
                .borrow_mut()
                .alias_atomic(place_id, *unsafe_place)
                .may_alias(self.alias_unknown_policy)
            {
                return (true, *node_index, Some(*unsafe_place));
            }
        }
        (false, PlaceId::new(0), None)
    }

    fn wire_unsafe_transition(
        &mut self,
        bb_idx: BasicBlock,
        transition: Transition,
        unsafe_place: PlaceId,
        transition_name: &str,
        ready_suffix: &str,
        span_str: &str,
    ) {
        let transition_id = self.net.add_transition(transition);
        let last_node = self.bb_graph.last(bb_idx);
        self.net.add_input_arc(last_node, transition_id, 1);
        self.net.add_output_arc(unsafe_place, transition_id, 1);
        self.net.add_input_arc(unsafe_place, transition_id, 1);
        let place_name = format!("{transition_name}_{ready_suffix}");
        let temp_place_node = crate::bb_place!(self.net, place_name, span_str.to_string());
        self.net.add_output_arc(temp_place_node, transition_id, 1);
        self.bb_graph.push(bb_idx, temp_place_node);
    }

    pub(super) fn process_rvalue_reads(
        &mut self,
        rvalue: &Rvalue<'tcx>,
        fn_name: &str,
        bb_idx: BasicBlock,
        span_str: &str,
    ) {
        let places = rvalue_read_places(rvalue);

        for place in places {
            let place_id = AliasId::new(self.instance_id, place.local);
            let place_ty = format!("{:?}", place.ty(self.body, self.tcx));

            let alias_result = self.has_unsafe_alias(place_id);
            if alias_result.0 {
                let transition_name =
                    format!("{}_read_{:?}_in:{}", fn_name, place_id.local, span_str);
                let read_t = Transition::new_with_transition_type(
                    transition_name.clone(),
                    TransitionType::UnsafeRead(
                        alias_result.1.index(),
                        span_str.to_string(),
                        bb_idx.index(),
                        place_ty,
                    ),
                );
                self.wire_unsafe_transition(
                    bb_idx,
                    read_t,
                    alias_result.1,
                    &transition_name,
                    "rready",
                    span_str,
                );
            }
        }
    }

    pub(super) fn process_place_writes(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        fn_name: &str,
        bb_idx: BasicBlock,
        span_str: &str,
    ) {
        let place_id = AliasId::new(self.instance_id, place.local);
        let place_ty = format!("{:?}", place.ty(self.body, self.tcx));

        let alias_result = self.has_unsafe_alias(place_id);
        if alias_result.0 {
            let transition_name = format!("{}_write_{:?}_in:{}", fn_name, place_id.local, span_str);
            let write_t = Transition::new_with_transition_type(
                transition_name.clone(),
                TransitionType::UnsafeWrite(
                    alias_result.1.index(),
                    span_str.to_string(),
                    bb_idx.index(),
                    place_ty,
                ),
            );
            self.wire_unsafe_transition(
                bb_idx,
                write_t,
                alias_result.1,
                &transition_name,
                "wready",
                span_str,
            );
        }
    }
}
