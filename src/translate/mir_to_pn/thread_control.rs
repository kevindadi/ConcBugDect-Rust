//! Thread control: spawn/join/scope/rayon.

use super::BodyToPetriNet;
use crate::{
    memory::pointsto::AliasId,
    net::{Idx, Transition, TransitionId, TransitionType},
    translate::callgraph::{ThreadControlKind, classify_thread_control},
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Local, Operand};
use rustc_span::Spanned;

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// Prefer joining in textual spawn/join order inside the function body.
    fn connect_join_from_recorded_order(&mut self, bb_end: TransitionId) -> bool {
        if let Some(spawn_end) = self.ordered_spawn_ends.pop_front() {
            self.net.add_input_arc(spawn_end, bb_end, 1);
            return true;
        }
        false
    }

    pub(super) fn resolve_vec_local(&self, local: Local) -> Local {
        self.vec_alias_source.get(&local).copied().unwrap_or(local)
    }

    pub(super) fn track_joinhandle_container_call(
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

    pub(super) fn handle_thread_call(
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
        if let Some(kind) = classify_thread_control(
            self.tcx,
            callee_def_id,
            callee_func_name,
            self.key_api_regex,
        ) {
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
            }
        }
        false
    }

    pub(super) fn handle_scope_join(
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
            log::error!(
                "No matching spawn call found for join in {:?}",
                self.instance.def_id()
            );
        }

        if let Some(transition) = self.net.get_transition_mut(bb_end) {
            transition.transition_type = TransitionType::Join(callee_func_name.to_string());
        }

        for spawn_def_id in matching_callees {
            if let Some((_, spawn_end)) = self.functions_map().get(&spawn_def_id).copied() {
                self.net.add_input_arc(spawn_end, bb_end, 1);
            }
        }

        self.connect_to_target(bb_idx, bb_end, target);
    }

    pub(super) fn handle_scope_spawn(
        &mut self,
        callee_func_name: &str,
        bb_idx: &BasicBlock,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        target: &Option<BasicBlock>,
        bb_end: TransitionId,
    ) {
        if self.return_transition.index() == 0 {
            let bb_term_name = crate::transition_name!(callee_func_name, bb_idx, "return");
            let bb_term_transition =
                Transition::new_with_transition_type(bb_term_name, TransitionType::Function);
            self.return_transition = self.net.add_transition(bb_term_transition);
        }

        if let Some((closure_start, closure_end)) = self.resolve_closure_places_at(args, 1) {
            self.net.add_output_arc(closure_start, bb_end, 1);
            self.net
                .add_input_arc(closure_end, self.return_transition, 1);
        }
        self.connect_to_target(*bb_idx, bb_end, target);
    }

    pub(super) fn handle_rayon_join(
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
            bb_idx,
            "wait_closure",
            "join",
            TransitionType::Join(callee_func_name.to_string()),
            span.to_string(),
            bb_end
        );

        self.connect_to_target(*bb_idx, bb_join, target);

        for (i, _) in args.iter().enumerate() {
            if let Some((closure_start, closure_end)) = self.resolve_closure_places_at(args, i) {
                self.net.add_output_arc(closure_start, bb_end, 1);
                self.net.add_input_arc(closure_end, bb_join, 1);
            }
        }
    }

    pub(super) fn handle_spawn(
        &mut self,
        callee_func_name: &str,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        destination: Local,
        target: &Option<BasicBlock>,
        bb_idx: BasicBlock,
        bb_end: TransitionId,
    ) {
        if let Some((closure_start, closure_end)) = self.resolve_closure_places(args) {
            self.net.add_output_arc(closure_start, bb_end, 1);
            self.ordered_spawn_ends.push_back(closure_end);
            self.spawn_handle_end.insert(destination, closure_end);
            log::debug!(
                "[vec-track] SPAWN: dest={:?}, closure_end={:?}, spawn_handle_end={:?}",
                destination,
                closure_end,
                self.spawn_handle_end
            );
        }

        if let Some(transition) = self.net.get_transition_mut(bb_end) {
            transition.transition_type = TransitionType::Spawn(callee_func_name.to_string());
        }
        self.connect_to_target(bb_idx, bb_end, target);
    }

    pub(super) fn handle_join(
        &mut self,
        callee_func_name: &str,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        target: &Option<BasicBlock>,
        bb_idx: BasicBlock,
        bb_end: TransitionId,
    ) {
        if let Some(transition) = self.net.get_transition_mut(bb_end) {
            transition.transition_type = TransitionType::Join(callee_func_name.to_string());
        }

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
                for spawn_end in all_ends {
                    self.net.add_input_arc(spawn_end, bb_end, 1);
                    joined = true;
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
                    self.net.add_input_arc(spawn_end, bb_end, 1);
                    joined = true;
                }
            } else if let Some(spawn_end) = self.spawn_handle_end.get(&handle_local).copied() {
                self.net.add_input_arc(spawn_end, bb_end, 1);
                joined = true;
            }
        }

        if !joined && self.connect_join_from_recorded_order(bb_end) {
            joined = true;
        }

        if !joined {
            let join_id = AliasId::from_place(
                self.instance_id,
                args.first().unwrap().node.place().unwrap().as_ref(),
            );

            let matching_callees = self.get_matching_spawn_callees(join_id);

            if matching_callees.is_empty() {
                log::error!(
                    "No matching spawn call found for join in {:?}",
                    self.instance.def_id()
                );
            }

            for spawn_def_id in matching_callees {
                if let Some((_, spawn_end)) = self.functions_map().get(&spawn_def_id).copied() {
                    self.net.add_input_arc(spawn_end, bb_end, 1);
                }
            }
        }

        self.connect_to_target(bb_idx, bb_end, target);
    }
}
