//! `Drop` of a lock guard, including unwind release.

use super::super::BodyToPetriNet;
use crate::analysis::primitives::blocking::LockGuardTy;
use crate::translate::net::TransitionKind;
use crate::translate::net::{TransitionId, TransitionType};
use rustc_middle::mir::{BasicBlock, BasicBlockData};

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    pub(in crate::translate::lower) fn handle_drop(
        &mut self,
        bb_idx: &BasicBlock,
        place: &rustc_middle::mir::Place<'tcx>,
        target: &BasicBlock,
        name: &str,
        bb: &BasicBlockData<'tcx>,
    ) {
        let bb_term_name = crate::transition_name!(name, bb_idx, "drop");
        let span = self.bb_span(*bb_idx);
        let bb_end = self.new_transition(bb_term_name, TransitionType::Drop, *bb_idx, span);

        self.net.arc_in(self.bb_graph.last(*bb_idx), bb_end, 1);

        if !bb.is_cleanup {
            self.add_guard_release_arcs(bb_end, place);
        }

        if self.is_back_edge(*bb_idx, *target) {
            self.record_cut_back_edge(super::super::CutBackEdge::After {
                source: *bb_idx,
                target: *target,
                after: bb_end,
            });
        } else {
            self.net.arc_out(self.bb_graph.start(*target), bb_end, 1);
        }
    }

    /// Wire the release of a lock guard that is being dropped: the guard's
    /// resource place gets its token back (the full RwLock capacity for a
    /// write guard) and the transition is typed `Unlock`. No-op when `place`
    /// does not hold a known guard; returns whether a guard was released.
    ///
    /// Shared by ordinary `drop` terminators and the unwind cleanup chain, so
    /// a panicking frame releases exactly the guards its normal drops would.
    ///
    /// The place comes from `lock_node_for_guard`, the same resolver
    /// every acquire edge uses.
    pub(in crate::translate::lower) fn add_guard_release_arcs(
        &mut self,
        bb_end: TransitionId,
        place: &rustc_middle::mir::Place<'tcx>,
    ) -> bool {
        let lockguard_id = Self::lockguard_id_for_dest(self.instance_id, place);
        if self.add_guard_id_release_arcs(bb_end, lockguard_id) {
            return true;
        }
        if place.projection.is_empty() {
            // Kept here. `ResourceBinder` does not see
            // `let _ = cv.wait(g)`; the unextracted guard is released
            // through this lookup.
            if let Some(&wait_guard_id) = self.unextracted_wait_guards.get(&place.local) {
                return self.add_guard_id_release_arcs(bb_end, wait_guard_id);
            }
        }
        false
    }

    pub(in crate::translate::lower) fn add_guard_id_release_arcs(
        &mut self,
        bb_end: TransitionId,
        lockguard_id: crate::analysis::primitives::blocking::LockGuardId,
    ) -> bool {
        if self.lockguards.get(&lockguard_id).is_none() {
            return false;
        }

        let Some(lock_node) = self.lock_node_for_guard(lockguard_id) else {
            return false;
        };
        match &self.lockguards[&lockguard_id].lockguard_ty {
            LockGuardTy::StdMutex(_)
            | LockGuardTy::ParkingLotMutex(_)
            | LockGuardTy::SpinMutex(_)
            | LockGuardTy::StdRwLockRead(_)
            | LockGuardTy::ParkingLotRead(_)
            | LockGuardTy::SpinRead(_) => {
                self.net.arc_out(lock_node, bb_end, 1);
            }
            _ => {
                self.net.arc_out(
                    lock_node,
                    bb_end,
                    crate::analysis::api_patterns::RWLOCK_CAPACITY,
                );
            }
        }

        self.net.set_transition_kind(
            bb_end,
            TransitionKind::new(TransitionType::Unlock(lock_node.index())),
        );
        true
    }
}
