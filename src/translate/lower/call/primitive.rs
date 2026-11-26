//! Lock acquire. Release is `add_guard_release_arcs` in `drop.rs`.

use super::super::BodyToPetriNet;
use crate::analysis::callgraph::InstanceId;
use crate::analysis::memory::pointsto::AliasId;
use crate::analysis::primitives::blocking::CondVarId;
use crate::analysis::primitives::blocking::{LockGuardId, LockGuardTy};
use crate::translate::net::{PlaceClass, ResourceKind, TransitionKind};
use crate::translate::net::{PlaceId, TransitionId, TransitionType};
use crate::util::has_spn_attribute;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Local;
use rustc_middle::mir::{BasicBlock, Operand, Place, ProjectionElem};
use rustc_span::Spanned;

/// The one resolution rule shared by every lock edge: the merged resource
/// place recorded for this guard alias.
fn resolve_lock_node(
    generic_locks: &rustc_data_structures::fx::FxHashMap<AliasId, PlaceId>,
    alias_id: AliasId,
) -> Option<PlaceId> {
    generic_locks.get(&alias_id).copied()
}

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// Resource place a guard operates on: the collected site's place when one
    /// exists, otherwise the merged place in the lock registry. Acquire and
    /// release both go through this function.
    pub(in crate::translate::lower) fn lock_node_for_guard(
        &self,
        guard_id: LockGuardId,
    ) -> Option<PlaceId> {
        if let Some(place) = self.place_for_guard(guard_id) {
            return Some(place);
        }
        resolve_lock_node(self.resources.locks(), guard_id.get_alias_id())
    }

    /// Registry place of a collected guard. `None` when the guard is not a
    /// collected site, so the caller keeps the registry lookup.
    fn place_for_guard(&self, guard_id: LockGuardId) -> Option<PlaceId> {
        let guard = self.lockguards.get(&guard_id)?;
        let kind = match &guard.lockguard_ty {
            LockGuardTy::StdMutex(_)
            | LockGuardTy::ParkingLotMutex(_)
            | LockGuardTy::SpinMutex(_) => crate::analysis::sync::SiteKind::Mutex,
            _ => crate::analysis::sync::SiteKind::RwLock,
        };
        let site = crate::analysis::sync::SyncSite {
            instance: guard_id.instance_id,
            local: guard_id.local,
            kind,
            ty: crate::analysis::sync::guard_protected_ty(&guard.lockguard_ty),
            role: crate::analysis::sync::SiteRole::Acquire,
            span: String::new(),
            object: AliasId::from(guard_id),
            origin: crate::analysis::sync::SiteOrigin::Guard(guard_id),
            atomic_order: None,
        };
        let Some(slot) = self.resource_map.slot_of(&site) else {
            log::error!(
                "unregistered sync site: guard {}:{} is not in the resource plan",
                guard_id.instance_id.index(),
                guard_id.local.as_u32()
            );
            return None;
        };
        self.place_binding.place(slot)
    }
    /// Build the guard id for a lock-call destination place, preserving the
    /// field index so guards stored in a coroutine/struct state projection
    /// (e.g. `(*_state as variant#N).k`) are distinguished from plain locals.
    pub(in crate::translate::lower) fn lockguard_id_for_dest(
        instance_id: InstanceId,
        destination: &Place<'tcx>,
    ) -> LockGuardId {
        let field = destination.projection.iter().find_map(|elem| {
            if let ProjectionElem::Field(f, _) = elem {
                Some(f.as_u32())
            } else {
                None
            }
        });
        LockGuardId::with_field(instance_id, destination.local, field)
    }
    /// Handle a lock-acquisition call if `destination` is a registered lock
    /// guard: wire the resource arcs with the weight the guard kind requires
    /// and return the matching `TransitionType`.
    ///
    /// The caller must backfill the returned type onto `bb_end` (see the call
    /// site in `handle_call`): the type and the arc weights have to come from
    /// the same branch here, so neither is complete on its own.
    pub(in crate::translate::lower) fn handle_lock_call(
        &mut self,
        bb_idx: BasicBlock,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        destination: &rustc_middle::mir::Place<'tcx>,
        target: &Option<BasicBlock>,
        bb_end: TransitionId,
    ) -> Option<TransitionType> {
        // A lock acquisition *creates* a guard from a non-guard source
        // (`Mutex::lock(&mu)`, `Result::unwrap(result)`). Calls that merely
        // forward an existing guard (e.g. `fn wait(g: MutexGuard) -> MutexGuard`)
        // also have a guard-typed destination but must NOT acquire a second
        // token. Distinguish them: if any argument is itself a lock guard, or
        // is the result of a condvar wait (which re-acquired the guard on its
        // return transition), this is a pass-through, not an acquisition.
        let arg_is_guard = args.iter().any(|a| {
            a.node
                .place()
                .map(|p| {
                    self.lockguards
                        .contains_key(&LockGuardId::new(self.instance_id, p.local))
                })
                .unwrap_or(false)
        });
        if arg_is_guard {
            return None;
        }

        // A `Condvar::wait(guard)` call returns the guard it re-acquired on the
        // wait's return transition. Extracting that result (`unwrap`, `expect`,
        // ...) forwards the guard; treating the extractor's guard-typed
        // destination as a fresh acquisition would take a second mutex token
        // and deadlock the net.
        let arg_is_wait_result = args.iter().any(|a| {
            a.node
                .place()
                .is_some_and(|p| self.wait_result_locals.contains(&p.local))
        });
        if arg_is_wait_result {
            return None;
        }

        let lockguard_id = Self::lockguard_id_for_dest(self.instance_id, destination);
        if let Some(guard) = self.lockguards.get(&lockguard_id) {
            let Some(lock_node) = self.lock_node_for_guard(lockguard_id) else {
                return None;
            };

            // A write lock is exclusive: it must consume the RwLock's *full*
            // capacity so no reader or other writer can proceed while it is
            // held (the matching unlock returns the same amount). Reads and
            // mutex locks take a single token.
            let (call_type, weight) = match &guard.lockguard_ty {
                LockGuardTy::StdMutex(_)
                | LockGuardTy::ParkingLotMutex(_)
                | LockGuardTy::SpinMutex(_) => (TransitionType::Lock(lock_node.index()), 1),
                LockGuardTy::StdRwLockRead(_)
                | LockGuardTy::ParkingLotRead(_)
                | LockGuardTy::SpinRead(_) => (TransitionType::RwLockRead(lock_node.index()), 1),
                _ => (
                    TransitionType::RwLockWrite(lock_node.index()),
                    crate::analysis::api_patterns::RWLOCK_CAPACITY,
                ),
            };

            self.update_lock_transition(bb_end, &lock_node, weight);
            self.connect_to_target(bb_idx, bb_end, target);
            Some(call_type)
        } else {
            None
        }
    }
    pub(in crate::translate::lower) fn update_lock_transition(
        &mut self,
        bb_end: TransitionId,
        lock_node: &PlaceId,
        weight: usize,
    ) {
        self.net.arc_in(*lock_node, bb_end, weight);
    }
}

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// TODO: mailboxes are matched with `alias_atomic` against
    /// `resources.condvars`. A condvar slot has no Petri-net place in
    /// `ResourceMap` (one initial token per local), so this does not call
    /// `ResourceMap::place`. The guard place does, via `lock_node_for_guard`.
    pub(in crate::translate::lower) fn handle_condvar_call(
        &mut self,
        callee_def_id: DefId,
        callee_func_name: &str,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        name: &str,
        bb_idx: BasicBlock,
        span: &str,
    ) -> bool {
        // The scenario-level model selects the recognised
        // call families. `std` keeps exactly the previous condition
        // (attributes + configured std patterns); `parking_lot` additionally
        // matches `parking_lot::Condvar::{notify*,wait*}` by def path.
        let is_notify = has_spn_attribute(self.tcx, callee_def_id, "pn_condvar_notify")
            || (self.condvar_model.recognizes_std()
                && self.key_api_regex.matches_condvar_notify(callee_func_name))
            || crate::analysis::primitives::blocking::parking_lot_condvar_call(
                &self.tcx.def_path_str(callee_def_id),
                self.condvar_model,
            ) == Some(crate::analysis::primitives::blocking::CondvarCallKind::Notify);
        let is_bool_wait_loop_call = self.bool_wait_loops.iter().any(|l| {
            l.wait_bb == bb_idx
                && self
                    .lock_node_for_guard(l.guard_id)
                    .is_some_and(|ln| self.resources.bool_predicates().contains_key(&ln))
        });
        let is_wait = has_spn_attribute(self.tcx, callee_def_id, "pn_condvar_wait")
            || (self.condvar_model.recognizes_std()
                && self.key_api_regex.matches_condvar_wait(callee_func_name))
            || crate::analysis::primitives::blocking::parking_lot_condvar_call(
                &self.tcx.def_path_str(callee_def_id),
                self.condvar_model,
            ) == Some(crate::analysis::primitives::blocking::CondvarCallKind::Wait)
            || is_bool_wait_loop_call;
        // `parking_lot::Condvar::notify_all` is classified as a notify above
        // and approximated as a single wakeup (one mailbox token). P/T cannot
        // express "wake every waiter"; the tool does not claim notify_all
        // support (evaluation, recorded in the design notes).
        let guard_plan = self.condvar_model.guard_plan();
        if is_notify {
            let condvar_id = CondVarId::new(
                self.instance_id,
                args.first().unwrap().node.place().unwrap().local,
            );
            let condvar_alias = condvar_id.get_alias_id();

            for (id, node) in self.resources.condvars().iter() {
                if self
                    .alias
                    .borrow_mut()
                    .alias_atomic(condvar_alias, *id)
                    .may_alias(self.alias_unknown_policy)
                {
                    self.net.arc_out(*node, bb_end, 1);

                    self.net.set_transition_kind(
                        bb_end,
                        TransitionKind::new(TransitionType::Notify(node.index())),
                    );

                    // With the ordering guard open, the
                    // normal branch may only fire when a waiter is parked —
                    // it requires and consumes one waiting token. The lost
                    // twin below stays unconditional (H1), so a notify that
                    // races ahead of the wait is still modelled as lost.
                    if let Some(waiting) = self.resources.condvar_waiting().get(node) {
                        self.net
                            .arc_in(*waiting, bb_end, guard_plan.notify_normal_waiting_weight);
                    }

                    // (H1): a real `notify` with no waiter is a
                    // no-op, so the call must also be able to fire *without*
                    // delivering a token — otherwise the unobserved notify is
                    // a stuck transition (a fake deadlock). The twin shares
                    // the block's input token and the same target but produces
                    // nothing; the P/T choice models "delivered or lost". The
                    // "lost" branch keeps the classic lost-wakeup deadlock
                    // reachable, so the abstraction stays conservative for
                    // deadlock detection.
                    let lost_id = self.new_transition(
                        crate::transition_name!(name, bb_idx, "notify_lost"),
                        TransitionType::Notify(node.index()),
                        bb_idx,
                        span.to_string(),
                    );
                    self.net.arc_in(self.bb_graph.last(bb_idx), lost_id, 1);
                    self.connect_to_target(bb_idx, lost_id, target);
                    break;
                }
            }
            self.connect_to_target(bb_idx, bb_end, target);
            true
        } else if is_wait {
            let (_bb_wait, bb_ret) = crate::add_wait_ret_subnet!(
                self,
                name,
                bb_idx,
                "wait",
                "ret",
                TransitionType::Wait,
                span.to_string(),
                bb_end
            );

            let condvar_id = CondVarId::new(
                self.instance_id,
                args.first().unwrap().node.place().unwrap().local,
            );
            let condvar_alias = condvar_id.get_alias_id();

            let mut matched_condvar = false;
            if !is_bool_wait_loop_call {
                for (id, node) in self.resources.condvars().iter() {
                    let r = self.alias.borrow_mut().alias_atomic(condvar_alias, *id);
                    log::warn!(
                        "[condvar-alias] {:?} (inst={:?},local={:?}) vs resource key {:?} => {:?}",
                        callee_func_name,
                        condvar_alias.instance_id,
                        condvar_alias.local,
                        *id,
                        r
                    );
                    if self
                        .alias
                        .borrow_mut()
                        .alias_atomic(condvar_alias, *id)
                        .may_alias(self.alias_unknown_policy)
                    {
                        matched_condvar = true;
                        self.net.arc_in(*node, bb_ret, 1);
                        // The parked waiter is counted at the
                        // wait entry transition (`bb_end`). A matching notify's
                        // normal branch consumes that token; the counter is not
                        // consumed on the return edge, so it counts waits not yet
                        // matched by a delivery (see the design note).
                        if let Some(waiting) = self.resources.condvar_waiting().get(node) {
                            self.net.arc_out(
                                *waiting,
                                bb_end,
                                guard_plan.wait_entry_waiting_weight,
                            );
                        }
                    }
                }
            }

            // Parking_lot's `wait(&self, &mut guard)` passes
            // a *reference* to the guard, while std passes the guard by
            // value. Resolve the guard argument by position: the first
            // post-receiver argument that is (or borrows/forwards to) a
            // registered lock guard. Std's arg 1 is the guard itself, so this
            // finds it directly and the historical behaviour is unchanged.
            let Some(guard_local) = self.condvar_guard_local(args) else {
                return false;
            };
            let guard_id = LockGuardId::new(self.instance_id, guard_local);
            let Some(lock_node) = self.lock_node_for_guard(guard_id) else {
                return false;
            };
            if !matched_condvar && !self.guard_checked_by_switch_before_wait(guard_local, bb_idx) {
                // Alias missed the collected mailboxes. This one-shot place is
                // the historical wait edge (`lib_lost_wakeup_real`); the wait
                // local is not itself a `SyncSite`, so it is not an unregistered
                // plan site.
                let condvar_node = self.net.add_place(
                    format!("Condvar:{span}"),
                    0,
                    1,
                    PlaceClass::Resource(ResourceKind::Condvar),
                    span.to_string(),
                );
                self.net.arc_in(condvar_node, bb_ret, 1);
            }
            self.net.arc_out(lock_node, bb_end, 1);
            self.net.arc_in(lock_node, bb_ret, 1);
            if is_bool_wait_loop_call
                && let Some(&(_false_place, true_place)) =
                    self.resources.bool_predicates().get(&lock_node)
            {
                self.net.arc_in(true_place, bb_ret, 1);
                self.net.arc_out(true_place, bb_ret, 1);
            }

            self.connect_to_target(bb_idx, bb_ret, target);
            true
        } else {
            false
        }
    }

    /// Locate the guard argument of a condvar wait.
    ///
    /// std: `Condvar::wait(guard)` — argument 1 is a registered guard local.
    /// parking_lot: `Condvar::wait(&self, &mut MutexGuard)` — argument 1 is a
    /// borrow temporary (`_12 = &mut _2`), so the guard is one or more
    /// borrow/forward hops behind it. The search starts at argument 1 (arg 0
    /// is the condvar receiver) and prefers a direct guard before tracing.
    pub(in crate::translate::lower) fn condvar_guard_local(
        &self,
        args: &[Spanned<Operand<'tcx>>],
    ) -> Option<Local> {
        let candidates: Vec<Local> = args
            .iter()
            .skip(1)
            .filter_map(|arg| arg.node.place().map(|place| place.local))
            .collect();
        for local in &candidates {
            if self
                .lockguards
                .contains_key(&LockGuardId::new(self.instance_id, *local))
            {
                return Some(*local);
            }
        }
        for local in candidates {
            if let Some(guard) = self.trace_local_to_guard(local) {
                return Some(guard);
            }
        }
        None
    }

    /// Follow `_dst = &/&mut _src` and `_dst = move/copy _src` chains until a
    /// registered lock guard is found (parking_lot's `&mut guard`
    /// wait argument).
    fn trace_local_to_guard(&self, start: Local) -> Option<Local> {
        let mut current = start;
        let mut seen = rustc_data_structures::fx::FxHashSet::default();
        while seen.insert(current) {
            let mut next = None;
            for bb in self.body.basic_blocks.iter() {
                for stmt in &bb.statements {
                    let rustc_middle::mir::StatementKind::Assign(boxed) = &stmt.kind else {
                        continue;
                    };
                    let (place, rvalue) = &**boxed;
                    if !place.projection.is_empty() || place.local != current {
                        continue;
                    }
                    let source = match rvalue {
                        rustc_middle::mir::Rvalue::Ref(_, _, src) => Some(src),
                        rustc_middle::mir::Rvalue::Use(
                            rustc_middle::mir::Operand::Move(src)
                            | rustc_middle::mir::Operand::Copy(src),
                            _,
                        ) => Some(src),
                        _ => None,
                    };
                    if let Some(src) = source
                        && src.projection.is_empty()
                    {
                        next = Some(src.local);
                    }
                }
            }
            current = next?;
            if self
                .lockguards
                .contains_key(&LockGuardId::new(self.instance_id, current))
            {
                return Some(current);
            }
        }
        None
    }
}

#[cfg(test)]
mod lock_tests {
    use super::resolve_lock_node;
    use crate::analysis::memory::pointsto::AliasId;
    use crate::translate::net::PlaceId;
    use petgraph::graph::NodeIndex;
    use rustc_data_structures::fx::FxHashMap;
    use rustc_middle::mir::Local;

    fn guard(instance: usize, local: u32) -> AliasId {
        AliasId::new(NodeIndex::new(instance), Local::from_u32(local))
    }

    fn locks(entries: &[(AliasId, usize)]) -> FxHashMap<AliasId, PlaceId> {
        entries
            .iter()
            .map(|(alias, place)| (*alias, PlaceId(*place)))
            .collect()
    }

    #[test]
    fn generic_guard_keeps_the_merged_place() {
        let guard = guard(3, 1);
        let generic = locks(&[(guard, 2)]);

        assert_eq!(resolve_lock_node(&generic, guard), Some(PlaceId(2)));
    }

    #[test]
    fn unknown_guard_has_no_resource() {
        let guard = guard(3, 1);
        assert_eq!(resolve_lock_node(&FxHashMap::default(), guard), None);
    }

    /// `drop(g); let g2 = lock(); let _ = cv.wait(g2)` shape.
    /// Asserts that `wait` entry and post-wait `drop` both have release arcs to
    /// `Mutex_0`, so `notify` is never blocked on `Mutex_0` and the blocked
    /// place is `wait_lost`'s `cv.wait` point.
    #[test]
    fn rebound_guard_wait_releases_mutex_and_blocks_on_condvar() {
        use crate::translate::net::{
            ArcDir, ControlSub, NetBuilder, PlaceClass, ResourceKind, StateGraph, TransitionKind,
            TransitionType,
        };

        let mut net = NetBuilder::new();
        let mutex = net.place(PlaceClass::Resource(ResourceKind::Mutex), "Mutex_0", 1);
        net.set_tokens(mutex, 1);
        let condvar = net.place(
            PlaceClass::Resource(ResourceKind::Condvar),
            "Condvar:wait",
            1,
        );
        let wl_start = net.marked_place(
            PlaceClass::Control(ControlSub::FunctionStart),
            "wait_lost_start",
            1,
        );
        let wl_end = net.place(
            PlaceClass::Control(ControlSub::FunctionEnd),
            "wait_lost_end",
            usize::MAX,
        );
        let p_g1 = net.place(
            PlaceClass::Control(ControlSub::BasicBlock),
            "wl_g1",
            usize::MAX,
        );
        let p_after_drop = net.place(
            PlaceClass::Control(ControlSub::BasicBlock),
            "wl_after_drop",
            usize::MAX,
        );
        let p_g2 = net.place(
            PlaceClass::Control(ControlSub::BasicBlock),
            "wl_g2",
            usize::MAX,
        );
        let p_wait = net.place(
            PlaceClass::Control(ControlSub::BasicBlock),
            "wait_lost_7_wait",
            usize::MAX,
        );
        let p_ret = net.place(
            PlaceClass::Control(ControlSub::BasicBlock),
            "wl_ret",
            usize::MAX,
        );

        let notify_start = net.marked_place(
            PlaceClass::Control(ControlSub::FunctionStart),
            "notify_start",
            1,
        );
        let notify_end = net.place(
            PlaceClass::Control(ControlSub::FunctionEnd),
            "notify_end",
            usize::MAX,
        );

        // `let g = lock()`
        let t_lock1 = net.transition(
            TransitionKind::new(TransitionType::Lock(mutex.index())),
            "wl_lock_g",
        );
        net.arc_in(wl_start, t_lock1, 1);
        net.arc_in(mutex, t_lock1, 1);
        net.arc_out(p_g1, t_lock1, 1);

        // `drop(g)`
        let t_drop1 = net.transition(
            TransitionKind::new(TransitionType::Unlock(mutex.index())),
            "wl_drop_g",
        );
        net.arc_in(p_g1, t_drop1, 1);
        net.arc_out(mutex, t_drop1, 1);
        net.arc_out(p_after_drop, t_drop1, 1);

        // `let g2 = lock()`
        let t_lock2 = net.transition(
            TransitionKind::new(TransitionType::Lock(mutex.index())),
            "wl_lock_g2",
        );
        net.arc_in(p_after_drop, t_lock2, 1);
        net.arc_in(mutex, t_lock2, 1);
        net.arc_out(p_g2, t_lock2, 1);

        // `cv.wait(g2)` entry: releases `mutex` and parks at `p_wait`.
        let t_wait_call = net.transition(
            TransitionKind::new(TransitionType::Function),
            "wl_wait_call",
        );
        net.arc_in(p_g2, t_wait_call, 1);
        net.arc_out(mutex, t_wait_call, 1);
        net.arc_out(p_wait, t_wait_call, 1);

        // `cv.wait(g2)` return: consumes `p_wait`, `condvar`, and `mutex`.
        let t_wait_ret = net.transition(TransitionKind::new(TransitionType::Wait), "wl_wait_ret");
        net.arc_in(p_wait, t_wait_ret, 1);
        net.arc_in(condvar, t_wait_ret, 1);
        net.arc_in(mutex, t_wait_ret, 1);
        net.arc_out(p_ret, t_wait_ret, 1);

        // Post-wait drop of unextracted `Result<MutexGuard, _>`: releases `mutex`.
        let t_drop_res = net.transition(
            TransitionKind::new(TransitionType::Unlock(mutex.index())),
            "wl_drop_wait_result",
        );
        net.arc_in(p_ret, t_drop_res, 1);
        net.arc_out(mutex, t_drop_res, 1);
        net.arc_out(wl_end, t_drop_res, 1);

        // `notify` locks and unlocks `mutex`.
        let t_notify = net.transition(
            TransitionKind::new(TransitionType::Lock(mutex.index())),
            "notify_lock_unlock",
        );
        net.arc_in(notify_start, t_notify, 1);
        net.arc_in(mutex, t_notify, 1);
        net.arc_out(mutex, t_notify, 1);
        net.arc_out(notify_end, t_notify, 1);

        let (pt, marking) = net.finish();
        assert!(
            pt.arcs_of(t_wait_call, ArcDir::Output)
                .any(|a| a.place == mutex && a.weight == 1),
            "wait entry transition must have release arc to Mutex_0"
        );
        assert!(
            pt.arcs_of(t_drop_res, ArcDir::Output)
                .any(|a| a.place == mutex && a.weight == 1),
            "unextracted wait-result drop transition must have release arc to Mutex_0"
        );

        let sg = StateGraph::from_net(&pt, marking);
        let deadlocks = sg.deadlock_states(&pt);
        assert_eq!(deadlocks.len(), 1);
        let dl_marking = &sg.states[deadlocks[0]].marking;
        let blocked = pt.blocked_places(dl_marking);
        assert_eq!(blocked, vec![p_wait]);
        assert_eq!(dl_marking.tokens(mutex), 1);
    }
}
