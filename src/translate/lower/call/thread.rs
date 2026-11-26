//! Thread control: spawn, join, scope, and rayon, plus `JoinHandle` dataflow
//! tracking. Every entry point here is reached from `call::handle_call`.

use super::super::BodyToPetriNet;
use crate::analysis::callgraph::{
    ThreadControlKind, classify_async_join_by_ty, classify_thread_control,
};
use crate::analysis::memory::pointsto::AliasId;
use crate::translate::net::TransitionKind;
use crate::translate::net::{TransitionId, TransitionType};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Local, Operand, Rvalue};
use rustc_span::Spanned;

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// Prefer joining in textual spawn/join order inside the function body.
    fn connect_join_from_recorded_order(&mut self, bb_end: TransitionId) -> bool {
        if let Some(spawn_end) = self.ordered_spawn_ends.pop_front() {
            self.net.arc_in(spawn_end, bb_end, 1);
            return true;
        }
        false
    }
    pub(in crate::translate::lower) fn handle_thread_call(
        &mut self,
        callee_def_id: DefId,
        callee_func_name: &str,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        destination: Local,
        target: &Option<BasicBlock>,
        bb_end: TransitionId,
        bb_idx: &BasicBlock,
        span: &str,
    ) -> bool {
        let awaited_ty = args
            .first()
            .and_then(|arg| arg.node.place())
            .map(|place| format!("{:?}", place.ty(self.body, self.tcx).ty))
            .unwrap_or_default();
        let kind = classify_thread_control(
            self.tcx,
            callee_def_id,
            callee_func_name,
            self.key_api_regex,
        )
        .or_else(|| classify_async_join_by_ty(callee_func_name, &awaited_ty));
        if let Some(kind) = kind {
            match kind {
                ThreadControlKind::Spawn => {
                    self.handle_spawn(callee_func_name, args, destination, target, *bb_idx, bb_end);
                    return true;
                }
                ThreadControlKind::ScopeSpawn => {
                    self.handle_scope_spawn(callee_func_name, bb_idx, args, target, bb_end);
                    return true;
                }
                ThreadControlKind::Join => {
                    self.handle_join(callee_func_name, args, target, *bb_idx, bb_end);
                    return true;
                }
                ThreadControlKind::ScopeJoin => {
                    self.handle_scope_join(callee_func_name, args, target, *bb_idx, bb_end);
                    return true;
                }
                ThreadControlKind::RayonJoin => {
                    self.handle_rayon_join(callee_func_name, bb_idx, args, target, bb_end, span);
                    return true;
                }
                ThreadControlKind::AsyncSpawn => {
                    log::info!("[async] AsyncSpawn: {}", callee_func_name);
                    self.handle_spawn(callee_func_name, args, destination, target, *bb_idx, bb_end);
                    return true;
                }
                ThreadControlKind::AsyncJoin => {
                    log::info!(
                        "[async] AsyncJoin: {} (ty={})",
                        callee_func_name,
                        awaited_ty
                    );
                    self.handle_join(callee_func_name, args, target, *bb_idx, bb_end);
                    return true;
                }
            }
        }
        false
    }
    pub(in crate::translate::lower) fn handle_spawn(
        &mut self,
        callee_func_name: &str,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        destination: Local,
        target: &Option<BasicBlock>,
        bb_idx: BasicBlock,
        bb_end: TransitionId,
    ) {
        if let Some((closure_start, closure_end)) = self.resolve_closure_places(args) {
            self.net.arc_out(closure_start, bb_end, 1);
            let thread_place = self.emit_thread_place(Some(destination));
            self.net.arc_out(thread_place, bb_end, 1);
            self.ordered_spawn_ends.push_back(closure_end);
            self.spawn_handle_end.insert(destination, closure_end);
            log::debug!(
                "[vec-track] SPAWN: dest={:?}, closure_end={:?}, spawn_handle_end={:?}",
                destination,
                closure_end,
                self.spawn_handle_end
            );
        } else {
            let first_ty = args
                .first()
                .and_then(|a| a.node.place())
                .map(|p| format!("{:?}", p.ty(self.body, self.tcx).ty))
                .unwrap_or_default();
            log::warn!(
                "[async] spawn: failed to resolve future from arg (ty={})",
                first_ty
            );
        }

        self.net.set_transition_kind(
            bb_end,
            TransitionKind::new(TransitionType::Spawn(callee_func_name.to_string())),
        );
        self.connect_to_target(bb_idx, bb_end, target);
    }
    pub(in crate::translate::lower) fn handle_join(
        &mut self,
        callee_func_name: &str,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        target: &Option<BasicBlock>,
        bb_idx: BasicBlock,
        bb_end: TransitionId,
    ) {
        self.net.set_transition_kind(
            bb_end,
            TransitionKind::new(TransitionType::Join(callee_func_name.to_string())),
        );

        let mut joined = false;
        if let Some(handle_local) = args.first().and_then(|a| a.node.place()).map(|p| p.local) {
            log::debug!(
                "[vec-track] JOIN: handle_local={:?}, handle_vec={:?}, option_vec={:?}, spawn_end_keys={:?}, vec_spawn_ends={:?}",
                handle_local,
                self.handle_vec_source,
                self.option_vec_source,
                self.spawn_handle_end.keys().collect::<Vec<_>>(),
                self.vec_spawn_ends,
            );
            if let Some(vec_local) = self.handle_vec_source.get(&handle_local).copied() {
                let all_ends: Vec<_> = self
                    .vec_spawn_ends
                    .entry(vec_local)
                    .or_default()
                    .drain(..)
                    .collect();
                let thread_places: Vec<_> = self
                    .vec_thread_places
                    .entry(vec_local)
                    .or_default()
                    .drain(..)
                    .collect();
                for spawn_end in all_ends {
                    self.net.arc_in(spawn_end, bb_end, 1);
                    joined = true;
                }
                for thread_place in thread_places {
                    self.net.arc_in(thread_place, bb_end, 1);
                }
            } else if let Some(vec_local) = self.option_vec_source.get(&handle_local).copied() {
                self.handle_vec_source.insert(handle_local, vec_local);
                let all_ends: Vec<_> = self
                    .vec_spawn_ends
                    .entry(vec_local)
                    .or_default()
                    .drain(..)
                    .collect();
                for spawn_end in all_ends {
                    self.net.arc_in(spawn_end, bb_end, 1);
                    joined = true;
                }
                let thread_places: Vec<_> = self
                    .vec_thread_places
                    .entry(vec_local)
                    .or_default()
                    .drain(..)
                    .collect();
                for thread_place in thread_places {
                    self.net.arc_in(thread_place, bb_end, 1);
                }
            } else if let Some(spawn_end) = self.spawn_handle_end.get(&handle_local).copied() {
                self.net.arc_in(spawn_end, bb_end, 1);
                if let Some(thread_place) = self.spawn_thread_by_local.get(&handle_local).copied() {
                    self.net.arc_in(thread_place, bb_end, 1);
                    self.ordered_thread_places
                        .retain(|place| *place != thread_place);
                }
                joined = true;
            }
        }

        if !joined && self.connect_join_from_recorded_order(bb_end) {
            if let Some(thread_place) = self.ordered_thread_places.pop_front() {
                self.net.arc_in(thread_place, bb_end, 1);
            }
            joined = true;
        }

        if !joined {
            let have_local = args
                .first()
                .and_then(|a| a.node.place())
                .is_some_and(|p| self.spawn_thread_by_local.contains_key(&p.local));
            if crate::translate::net::subnets::join_decision(have_local)
                == crate::translate::net::subnets::JoinDecision::UnsupportedCrossFunction
            {
                // Spawn lives in another function. Do not wire that function's
                // end place and do not fall through to an ordinary call.
                self.coverage.note_unsupported_cross_fn_join(&self.fn_path);
            }
        }

        self.connect_to_target(bb_idx, bb_end, target);
    }
}

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    pub(in crate::translate::lower) fn handle_scope_join(
        &mut self,
        callee_func_name: &str,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        target: &Option<BasicBlock>,
        bb_idx: BasicBlock,
        bb_end: TransitionId,
    ) {
        let join_id = AliasId::from_place(
            self.instance_id,
            args.first().unwrap().node.place().unwrap().as_ref(),
        );

        let matching_callees = self.get_matching_spawn_callees(join_id);

        if matching_callees.is_empty() {
            if crate::translate::net::subnets::join_decision(false)
                == crate::translate::net::subnets::JoinDecision::UnsupportedCrossFunction
            {
                self.coverage.note_unsupported_cross_fn_join(&self.fn_path);
            }
        }

        self.net.set_transition_kind(
            bb_end,
            TransitionKind::new(TransitionType::Join(callee_func_name.to_string())),
        );

        for spawn_def_id in matching_callees {
            if let Some((_, spawn_end)) = self.functions_map().get(&spawn_def_id).copied() {
                self.net.arc_in(spawn_end, bb_end, 1);
            }
        }

        self.connect_to_target(bb_idx, bb_end, target);
    }

    pub(in crate::translate::lower) fn handle_scope_spawn(
        &mut self,
        callee_func_name: &str,
        bb_idx: &BasicBlock,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        target: &Option<BasicBlock>,
        bb_end: TransitionId,
    ) {
        if self.return_transition.index() == 0 {
            let bb_term_name = crate::transition_name!(callee_func_name, bb_idx, "return");
            let span = self.bb_span(*bb_idx);
            self.return_transition =
                self.new_transition(bb_term_name, TransitionType::Function, *bb_idx, span);
        }

        if let Some((closure_start, closure_end)) = self.resolve_closure_places_at(args, 1) {
            self.net.arc_out(closure_start, bb_end, 1);
            let thread_place = self.emit_thread_place(None);
            self.ordered_thread_places
                .retain(|place| *place != thread_place);
            self.net.arc_out(thread_place, bb_end, 1);
            self.net.arc_in(closure_end, self.return_transition, 1);
            self.net.arc_in(thread_place, self.return_transition, 1);
        }
        self.connect_to_target(*bb_idx, bb_end, target);
    }

    pub(in crate::translate::lower) fn handle_rayon_join(
        &mut self,
        callee_func_name: &str,
        bb_idx: &BasicBlock,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        target: &Option<BasicBlock>,
        bb_end: TransitionId,
        span: &str,
    ) {
        log::debug!("handle_rayon_join: {:?}", callee_func_name);
        let (_bb_wait, bb_join) = crate::add_wait_ret_subnet!(
            self,
            callee_func_name,
            *bb_idx,
            "wait_closure",
            "join",
            TransitionType::Join(callee_func_name.to_string()),
            span.to_string(),
            bb_end
        );

        self.connect_to_target(*bb_idx, bb_join, target);

        for (i, _) in args.iter().enumerate() {
            if let Some((closure_start, closure_end)) = self.resolve_closure_places_at(args, i) {
                self.net.arc_out(closure_start, bb_end, 1);
                self.net.arc_in(closure_end, bb_join, 1);
            }
        }
    }
}

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    pub(in crate::translate::lower) fn resolve_vec_local(&self, local: Local) -> Local {
        self.vec_alias_source.get(&local).copied().unwrap_or(local)
    }

    pub(in crate::translate::lower) fn track_joinhandle_container_call(
        &mut self,
        callee_func_name: &str,
        args: &[Spanned<Operand<'tcx>>],
        destination: Local,
    ) {
        log::debug!(
            "[vec-track] ENTER track_joinhandle_container_call: callee={}",
            callee_func_name
        );
        if callee_func_name.contains("::push") {
            let Some(vec_ref_local) = args.first().and_then(|a| a.node.place()).map(|p| p.local)
            else {
                return;
            };
            let vec_local = self
                .local_ref_source
                .get(&vec_ref_local)
                .copied()
                .unwrap_or(vec_ref_local);
            let vec_root = self.resolve_vec_local(vec_local);
            log::debug!(
                "[vec-track] push: callee={}, vec_ref={:?}, vec_local={:?}, vec_root={:?}, in_jh_set={}, jh_locals={:?}",
                callee_func_name,
                vec_ref_local,
                vec_local,
                vec_root,
                self.joinhandle_vec_locals.contains(&vec_root),
                self.joinhandle_vec_locals
            );
            if !self.joinhandle_vec_locals.contains(&vec_root) {
                return;
            }
            let Some(handle_local) = args.get(1).and_then(|a| a.node.place()).map(|p| p.local)
            else {
                return;
            };
            self.vec_alias_source.insert(vec_local, vec_root);
            if let Some(spawn_end) = self.spawn_handle_end.get(&handle_local).copied() {
                self.vec_spawn_ends
                    .entry(vec_root)
                    .or_default()
                    .push_back(spawn_end);
                if let Some(thread_place) = self.spawn_thread_by_local.get(&handle_local).copied() {
                    self.vec_thread_places
                        .entry(vec_root)
                        .or_default()
                        .push_back(thread_place);
                }
                log::info!(
                    "[vec-track] push OK: handle={:?} -> vec_root={:?}, vec_spawn_ends={:?}",
                    handle_local,
                    vec_root,
                    self.vec_spawn_ends
                );
            } else {
                log::info!(
                    "[vec-track] push MISS: handle={:?} not in spawn_handle_end={:?}",
                    handle_local,
                    self.spawn_handle_end
                );
            }
            return;
        }

        if callee_func_name.contains("into_iter") {
            let Some(src_local) = args.first().and_then(|a| a.node.place()).map(|p| p.local) else {
                return;
            };
            let vec_local = self.resolve_vec_local(src_local);
            if self.joinhandle_vec_locals.contains(&vec_local)
                || self.vec_spawn_ends.contains_key(&vec_local)
            {
                self.iter_vec_source.insert(destination, vec_local);
                log::info!(
                    "[vec-track] into_iter: src={:?} -> vec={:?}, iter_vec_source[{:?}]={:?}",
                    src_local,
                    vec_local,
                    destination,
                    vec_local
                );
            }
            return;
        }

        if callee_func_name.contains("::next") {
            let Some(iter_ref_local) = args.first().and_then(|a| a.node.place()).map(|p| p.local)
            else {
                return;
            };
            let iter_local = self
                .local_ref_source
                .get(&iter_ref_local)
                .copied()
                .unwrap_or(iter_ref_local);
            if let Some(vec_local) = self.iter_vec_source.get(&iter_local).copied() {
                self.option_vec_source.insert(destination, vec_local);
                log::info!(
                    "[vec-track] next: iter_ref={:?} -> iter={:?} -> option_vec_source[{:?}]={:?}",
                    iter_ref_local,
                    iter_local,
                    destination,
                    vec_local
                );
            }
        }
    }
    /// Match `join_id` against `spawn_calls` via alias analysis; returns plausible spawn callee `DefId`s.
    pub(in crate::translate::lower) fn get_matching_spawn_callees(
        &mut self,
        join_id: AliasId,
    ) -> Vec<DefId> {
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

    pub(in crate::translate::lower) fn track_joinhandle_dataflow(
        &mut self,
        dest: Local,
        rvalue: &Rvalue<'tcx>,
    ) {
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
