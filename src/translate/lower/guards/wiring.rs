//! Bool-guard predicates, unextracted wait guards, and custom-lock resources.

use super::super::BodyToPetriNet;
use crate::analysis::memory::ownership::{CustomLockMode, CustomLockOp};
use crate::translate::net::TransitionKind;
use crate::translate::net::TransitionType;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::{BasicBlock, Local, Operand, Rvalue, StatementKind, TerminatorKind};

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// For every basic block in this body that writes `*g = true`
    /// while holding a guard of a boolean-predicate mutex, attach
    /// `data.<var>.false -> t` and `t -> data.<var>.true` to the block's
    /// outgoing transition(s).
    pub(in crate::translate::lower) fn attach_bool_guard_true_writes(&mut self) {
        if self.bool_true_writes.is_empty() {
            return;
        }
        let writes = self.bool_true_writes.clone();
        for (write_bb, guard_id) in writes {
            let Some(lock_node) = self.lock_node_for_guard(guard_id) else {
                continue;
            };
            let Some(&(false_place, true_place)) = self.resources.bool_predicates().get(&lock_node)
            else {
                continue;
            };
            let Some(last_place) = self.bb_graph.last_opt(write_bb) else {
                continue;
            };
            let outgoing_transitions = self.net.consumer_transitions(last_place);
            for tid in outgoing_transitions {
                self.net.arc_in(false_place, tid, 1);
                self.net.arc_out(true_place, tid, 1);
            }
        }
    }

    /// Emit the resource edge of a *guard-less custom lock* method.
    ///
    /// The operation lives inside the method body (`RawMutex::lock`,
    /// `RawRwLock::unlock_shared`, `WordLock::lock`), not at the caller's call
    /// site: the call returns no guard whose type could key the resource. The
    /// edge is therefore attached to this frame's return transition — acquire
    /// is an input arc, release an output arc — with the same weights the
    /// guard model uses (mutex 1/1, read 1/1, write `RWLOCK_CAPACITY` /
    /// `RWLOCK_CAPACITY`). A frame with several `return` blocks shares one
    /// return transition, so one invocation takes/returns the token exactly
    /// once. Frames recognized as delegating wrappers have no entry in the
    /// registry; the inner callee performs the operation instead.
    pub(in crate::translate::lower) fn attach_custom_lock_resource(&mut self) {
        // TODO: a guard-less custom lock is keyed by `InstanceId`, not by a
        // `SyncSite` this frame can rebuild. `ResourceMap::place` is not used.
        let Some(entry) = self
            .resources
            .custom_locks()
            .get(&self.instance_id)
            .copied()
        else {
            return;
        };
        if self.return_transition.index() == 0 {
            // Abnormal frame (panic-only or coroutine suspend): no normal
            // return edge exists, so there is nothing to hang the resource on.
            log::debug!(
                "custom lock method {} has no return transition; resource edge omitted",
                self.fn_path
            );
            return;
        }
        let weight = match entry.mode {
            CustomLockMode::Mutex | CustomLockMode::RwLockRead => 1,
            CustomLockMode::RwLockWrite => crate::analysis::api_patterns::RWLOCK_CAPACITY,
        };
        let transition_type = match (entry.op, entry.mode) {
            (CustomLockOp::Acquire, CustomLockMode::Mutex) => {
                TransitionType::Lock(entry.place.index())
            }
            (CustomLockOp::Acquire, CustomLockMode::RwLockRead) => {
                TransitionType::RwLockRead(entry.place.index())
            }
            (CustomLockOp::Acquire, CustomLockMode::RwLockWrite) => {
                TransitionType::RwLockWrite(entry.place.index())
            }
            // `Unlock` with the matching weight is how the guard model
            // releases both read and write locks today.
            (CustomLockOp::Release, _) => TransitionType::Unlock(entry.place.index()),
        };
        match entry.op {
            CustomLockOp::Acquire => {
                self.net.arc_in(entry.place, self.return_transition, weight);
            }
            CustomLockOp::Release => {
                self.net
                    .arc_out(entry.place, self.return_transition, weight);
            }
        }
        self.net
            .set_transition_kind(self.return_transition, TransitionKind::new(transition_type));
    }

    /// Identify `Condvar::wait` destination locals (e.g. `Result<MutexGuard, _>`
    /// in `let _ = cv.wait(g2);`) that are never unpacked by `.unwrap()` /
    /// `.expect()`, mapping them to the `LockGuardId` of the input guard `g2`
    /// so that dropping the `Result` releases the re-acquired mutex token.
    pub(in crate::translate::lower) fn collect_unextracted_wait_guards(
        &self,
    ) -> FxHashMap<Local, crate::analysis::primitives::blocking::LockGuardId> {
        let call_def_id = |func: &Operand<'tcx>| match func.ty(self.body, self.tcx).kind() {
            rustc_middle::ty::TyKind::FnDef(id, _) | rustc_middle::ty::TyKind::Closure(id, _) => {
                Some(*id)
            }
            _ => None,
        };

        let mut extracted_sources: FxHashSet<Local> = FxHashSet::default();
        for bb in self.body.basic_blocks.iter() {
            let TerminatorKind::Call { func, args, .. } = &bb.terminator().kind else {
                continue;
            };
            let Some(def_id) = call_def_id(func) else {
                continue;
            };
            if crate::analysis::memory::ownership::is_wrapper_extract(def_id, self.tcx) {
                for arg in args.iter() {
                    if let Some(place) = arg.node.place() {
                        extracted_sources.insert(place.local);
                    }
                }
            }
        }

        let mut map: FxHashMap<Local, crate::analysis::primitives::blocking::LockGuardId> =
            FxHashMap::default();
        for bb in self.body.basic_blocks.iter() {
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
            let name = crate::util::format_name(def_id);
            let is_wait = crate::analysis::memory::ownership::is_condvar_wait(def_id, self.tcx)
                || crate::util::has_spn_attribute(self.tcx, def_id, "pn_condvar_wait")
                || (self.condvar_model.recognizes_std()
                    && self.key_api_regex.matches_condvar_wait(&name));
            if !is_wait {
                continue;
            }
            let dest_id = Self::lockguard_id_for_dest(self.instance_id, destination);
            if self.lockguards.contains_key(&dest_id)
                || extracted_sources.contains(&destination.local)
            {
                continue;
            }
            if let Some(guard_local) = self.condvar_guard_local(args) {
                let guard_id = crate::analysis::primitives::blocking::LockGuardId::new(
                    self.instance_id,
                    guard_local,
                );
                map.insert(destination.local, guard_id);
            }
        }

        // Propagate across plain move/copy assignments (`let _unused = cv.wait(g2);`)
        // as long as the destination is not extracted by `unwrap`/`expect`.
        loop {
            let mut changed = false;
            for bb in self.body.basic_blocks.iter() {
                for stmt in &bb.statements {
                    let StatementKind::Assign(boxed) = &stmt.kind else {
                        continue;
                    };
                    let (dest, rvalue) = &**boxed;
                    if !dest.projection.is_empty() || extracted_sources.contains(&dest.local) {
                        continue;
                    }
                    if let Rvalue::Use(Operand::Move(src) | Operand::Copy(src), _) = rvalue {
                        if src.projection.is_empty() {
                            if let Some(&guard_id) = map.get(&src.local) {
                                changed |= map.insert(dest.local, guard_id).is_none();
                            }
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }

        map
    }

    /// Whether any lock guard of this frame is held across a `SwitchInt`
    /// condition check on a path reaching `wait_bb` (the `while !pred { cv.wait(g) }`
    /// pattern). Returns `false` when the condition check `SwitchInt` executes
    /// while no lock guard is held (e.g. `let ready = *g; drop(g); if !ready { let g2 = lock(); cv.wait(g2); }`).
    pub(in crate::translate::lower) fn guard_checked_by_switch_before_wait(
        &self,
        _guard_local: Local,
        wait_bb: BasicBlock,
    ) -> bool {
        let frame_guards: Vec<crate::analysis::primitives::blocking::LockGuardId> = self
            .lockguards
            .keys()
            .filter(|g| g.instance_id == self.instance_id)
            .copied()
            .collect();

        for (bb_idx, bb) in self.body.basic_blocks.iter_enumerated() {
            if bb.is_cleanup || bb.is_empty_unreachable() {
                continue;
            }
            let is_switch = bb
                .terminator
                .as_ref()
                .is_some_and(|t| matches!(t.kind, TerminatorKind::SwitchInt { .. }));
            if !is_switch {
                continue;
            }
            let any_guard_held_at_switch = frame_guards
                .iter()
                .any(|&gid| self.guard_reaches_block_exit_held(gid, bb_idx));
            if any_guard_held_at_switch && self.block_reaches(bb_idx, wait_bb) {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use crate::translate::net::{
        NetBuilder, PlaceClass, StateGraph, TransitionKind, TransitionType,
    };

    /// Boolean guard predicate places (`data.Mutex_0.false` = 1,
    /// `data.Mutex_0.true` = 0, capacity 1 each) conserve `M(false) + M(true) == 1`
    /// across all reachable states and eliminate false deadlocks in both
    /// `notify`-first and `wait`-first interleavings.
    #[test]
    fn bool_guard_predicate_conserves_tokens_and_eliminates_false_deadlocks() {
        let mut net = NetBuilder::new();
        let mutex = net.place(PlaceClass::Resource(()), "Mutex_0", 1);
        net.set_tokens(mutex, 1);
        let data_false = net.place(PlaceClass::Resource(()), "data.Mutex_0.false", 1);
        net.set_tokens(data_false, 1);
        let data_true = net.place(PlaceClass::Resource(()), "data.Mutex_0.true", 1);

        // Waiter: lock -> header -> switch1 (reads false) / switch2 (reads true)
        let w0 = crate::translate::net::control_place(&mut net, "wait_0", 1);
        let w_hdr = crate::translate::net::control_place(&mut net, "wait_hdr", 0);
        let w_body = crate::translate::net::control_place(&mut net, "wait_body", 0);
        let w_parked = crate::translate::net::control_place(&mut net, "wait_parked", 0);
        let w_latch = crate::translate::net::control_place(&mut net, "wait_latch", 0);
        let w_exit = crate::translate::net::control_place(&mut net, "wait_exit", 0);
        let w_end = crate::translate::net::function_end(&mut net, "wait_end");

        let t_w_lock = net.transition(
            TransitionKind::new(TransitionType::Lock(mutex.index())),
            "wait_lock",
        );
        net.arc_in(w0, t_w_lock, 1);
        net.arc_in(mutex, t_w_lock, 1);
        net.arc_out(w_hdr, t_w_lock, 1);

        // switch1: !*g == true -> reads data_false
        let t_sw1 = net.transition(TransitionKind::new(TransitionType::Switch), "wait_switch1");
        net.arc_in(w_hdr, t_sw1, 1);
        net.arc_in(data_false, t_sw1, 1);
        net.arc_out(data_false, t_sw1, 1);
        net.arc_out(w_body, t_sw1, 1);

        // switch2: !*g == false -> reads data_true
        let t_sw2 = net.transition(TransitionKind::new(TransitionType::Switch), "wait_switch2");
        net.arc_in(w_hdr, t_sw2, 1);
        net.arc_in(data_true, t_sw2, 1);
        net.arc_out(data_true, t_sw2, 1);
        net.arc_out(w_exit, t_sw2, 1);

        // cv.wait entry: releases mutex
        let t_wait_enter =
            net.transition(TransitionKind::new(TransitionType::Function), "wait_call");
        net.arc_in(w_body, t_wait_enter, 1);
        net.arc_out(mutex, t_wait_enter, 1);
        net.arc_out(w_parked, t_wait_enter, 1);

        // cv.wait ret: re-acquires mutex and reads data_true
        let t_wait_ret = net.transition(TransitionKind::new(TransitionType::Wait), "wait_ret");
        net.arc_in(w_parked, t_wait_ret, 1);
        net.arc_in(mutex, t_wait_ret, 1);
        net.arc_in(data_true, t_wait_ret, 1);
        net.arc_out(data_true, t_wait_ret, 1);
        net.arc_out(w_latch, t_wait_ret, 1);

        // back edge: latch -> hdr
        let t_back = net.transition(TransitionKind::new(TransitionType::Goto), "wait_back");
        net.arc_in(w_latch, t_back, 1);
        net.arc_out(w_hdr, t_back, 1);

        // exit: unlock and return
        let t_w_unlock = net.transition(
            TransitionKind::new(TransitionType::Unlock(mutex.index())),
            "wait_unlock",
        );
        net.arc_in(w_exit, t_w_unlock, 1);
        net.arc_out(mutex, t_w_unlock, 1);
        net.arc_out(w_end, t_w_unlock, 1);

        // Notifier: lock -> *g = true (consumes false, produces true) -> unlock
        let n0 = crate::translate::net::control_place(&mut net, "notify_0", 1);
        let n1 = crate::translate::net::control_place(&mut net, "notify_1", 0);
        let n2 = crate::translate::net::control_place(&mut net, "notify_2", 0);
        let n_end = crate::translate::net::function_end(&mut net, "notify_end");

        let t_n_lock = net.transition(
            TransitionKind::new(TransitionType::Lock(mutex.index())),
            "notify_lock",
        );
        net.arc_in(n0, t_n_lock, 1);
        net.arc_in(mutex, t_n_lock, 1);
        net.arc_out(n1, t_n_lock, 1);

        let t_n_set = net.transition(
            TransitionKind::new(TransitionType::Function),
            "notify_set_true",
        );
        net.arc_in(n1, t_n_set, 1);
        net.arc_in(data_false, t_n_set, 1);
        net.arc_out(data_true, t_n_set, 1);
        net.arc_out(n2, t_n_set, 1);

        let t_n_unlock = net.transition(
            TransitionKind::new(TransitionType::Unlock(mutex.index())),
            "notify_unlock",
        );
        net.arc_in(n2, t_n_unlock, 1);
        net.arc_out(mutex, t_n_unlock, 1);
        net.arc_out(n_end, t_n_unlock, 1);

        let (pt, marking) = net.finish();
        let graph = StateGraph::from_net(&pt, marking);
        for state in &graph.states {
            let sum = state.marking.tokens(data_false) + state.marking.tokens(data_true);
            assert_eq!(
                sum, 1,
                "conservation invariant M(false) + M(true) == 1 violated"
            );
        }
        assert!(
            graph.deadlock_states(&pt).is_empty(),
            "boolean guard abstraction must have 0 deadlock states across all interleavings"
        );
    }
}
