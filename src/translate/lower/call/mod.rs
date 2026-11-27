//! `handle_call` dispatch. The match order is the lowering order.

mod atomic;
mod drop;
mod indirect;
mod normal;
mod primitive;
mod thread;

use super::BodyToPetriNet;
use crate::translate::net::TransitionKind;
use crate::translate::net::{TransitionId, TransitionType};
use rustc_middle::mir::{BasicBlock, Operand};
use rustc_span::Spanned;

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// Extract a struct field name (e.g. `r0_main_sem` on `Shared`) by walking
    /// back from the first call argument (receiver `&self`) through local
    /// copies/refs/derefs in the current MIR body.
    pub(crate) fn place_adt_field_name(
        body: &rustc_middle::mir::Body<'tcx>,
        place: &rustc_middle::mir::Place<'tcx>,
    ) -> Option<String> {
        let mut ty = body.local_decls[place.local].ty;
        for elem in place.projection.iter() {
            match elem {
                rustc_middle::mir::ProjectionElem::Deref => {
                    ty = ty.builtin_deref(true)?;
                }
                rustc_middle::mir::ProjectionElem::Field(field_idx, field_ty) => {
                    let peeled = ty.peel_refs();
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = peeled.kind()
                        && adt_def.is_struct()
                    {
                        let field = adt_def.non_enum_variant().fields.get(field_idx)?;
                        let name = field.name.as_str();
                        if !name.is_empty()
                            && name != "ptr"
                            && name != "inner"
                            && name != "data"
                            && name != "phantom"
                        {
                            return Some(name.to_string());
                        }
                    }
                    ty = field_ty;
                }
                _ => {}
            }
        }
        None
    }

    fn extract_receiver_field_name(&self, args: &[Spanned<Operand<'tcx>>]) -> Option<String> {
        let first_place = args.first()?.node.place()?;
        if let Some(name) = Self::place_adt_field_name(self.body, &first_place) {
            return Some(name);
        }
        let mut current = first_place.local;
        let mut seen = rustc_data_structures::fx::FxHashSet::default();
        while seen.insert(current) {
            let mut next_local = None;
            for bb in self.body.basic_blocks.iter() {
                for stmt in &bb.statements {
                    let rustc_middle::mir::StatementKind::Assign(boxed) = &stmt.kind else {
                        continue;
                    };
                    let (dst, rvalue) = &**boxed;
                    if !dst.projection.is_empty() || dst.local != current {
                        continue;
                    }
                    let src_place = match rvalue {
                        rustc_middle::mir::Rvalue::Ref(_, _, p)
                        | rustc_middle::mir::Rvalue::RawPtr(_, p)
                        | rustc_middle::mir::Rvalue::CopyForDeref(p)
                        | rustc_middle::mir::Rvalue::Reborrow(_, _, p) => Some(p),
                        rustc_middle::mir::Rvalue::Use(
                            Operand::Copy(p) | Operand::Move(p),
                            _,
                        ) => Some(p),
                        _ => None,
                    };
                    if let Some(p) = src_place {
                        if let Some(name) = Self::place_adt_field_name(self.body, p) {
                            return Some(name);
                        }
                        next_local = Some(p.local);
                    }
                }
                if let Some(term) = &bb.terminator
                    && let rustc_middle::mir::TerminatorKind::Call {
                        args: call_args,
                        destination,
                        ..
                    } = &term.kind
                    && destination.projection.is_empty()
                    && destination.local == current
                    && let Some(p) = call_args.first().and_then(|a| a.node.place())
                {
                    if let Some(name) = Self::place_adt_field_name(self.body, &p) {
                        return Some(name);
                    }
                    next_local = Some(p.local);
                }
            }
            current = next_local?;
        }
        None
    }

    /// Form B of the sync registry: replace the call with a small summary subnet
    /// instead of inlining or dropping it.
    pub(in crate::translate::lower) fn try_apply_sync_summary(
        &mut self,
        callee: &str,
        args: &[Spanned<Operand<'tcx>>],
        bb_idx: BasicBlock,
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        span: &str,
    ) -> bool {
        use crate::analysis::primitives::sync_registry::SyncEffect;
        use crate::translate::net::{ControlSub, PlaceClass};
        let Some(op) = self.key_api_regex.sync.lookup(callee) else {
            return false;
        };
        if op.effect != SyncEffect::Summary {
            return false;
        }
        let summary_kind = op
            .summary
            .as_ref()
            .map(|s| s.kind.as_str())
            .unwrap_or_default()
            .to_string();
        if summary_kind == "silent" {
            self.connect_to_target(bb_idx, bb_end, target);
            return true;
        }
        let res_hint = if matches!(
            summary_kind.as_str(),
            "sem_acquire" | "sem_release" | "channel_send" | "channel_recv"
        ) {
            self.extract_receiver_field_name(args)
        } else {
            None
        };
        let places_n = op.summary.as_ref().map(|s| s.places).unwrap_or(1).max(1);
        let transitions_n = op
            .summary
            .as_ref()
            .map(|s| s.transitions)
            .unwrap_or(1)
            .max(1);
        let mut places = Vec::with_capacity(places_n);
        for i in 0..places_n {
            places.push(self.net.add_place(
                format!("{}_summary_p{i}", callee),
                0,
                1,
                PlaceClass::Control(ControlSub::BasicBlock),
                span.to_string(),
            ));
        }
        self.net.arc_out(places[0], bb_end, 1);
        let mut cursor = places[0];
        for i in 0..transitions_n {
            let trans_name = match summary_kind.as_str() {
                "sem_acquire" | "sem_release" | "channel_send" | "channel_recv" => {
                    if let Some(ref field) = res_hint {
                        format!("cir_sync::{summary_kind}::{field}::{callee}_summary_t{i}")
                    } else {
                        format!("cir_sync::{summary_kind}::{callee}_summary_t{i}")
                    }
                }
                _ => format!("{callee}_summary_t{i}"),
            };
            let t = self.new_transition(trans_name, TransitionType::Function, bb_idx, span.to_string());
            if i == 0
                && let Some(ref field) = res_hint
            {
                match summary_kind.as_str() {
                    "channel_send" => {
                        let ch_place = self.net.cir_channel_place(field);
                        self.net.arc_out(ch_place, t, 1);
                    }
                    "channel_recv" => {
                        let ch_place = self.net.cir_channel_place(field);
                        self.net.arc_in(ch_place, t, 1);
                    }
                    _ => {}
                }
            }
            self.net.arc_in(cursor, t, 1);
            let next = places.get(i + 1).copied().unwrap_or(cursor);
            if i + 1 < places.len() {
                self.net.arc_out(next, t, 1);
                cursor = next;
            } else if let Some(return_block) = target {
                if self.is_back_edge(bb_idx, *return_block) {
                    self.record_cut_back_edge(super::CutBackEdge::After {
                        source: bb_idx,
                        target: *return_block,
                        after: t,
                    });
                } else {
                    self.net.arc_out(self.bb_graph.start(*return_block), t, 1);
                }
            }
        }
        let _ = cursor;
        true
    }
    pub(in crate::translate::lower) fn handle_call(
        &mut self,
        bb_idx: BasicBlock,
        func: &Operand<'tcx>,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        destination: &rustc_middle::mir::Place<'tcx>,
        target: &Option<BasicBlock>,
        name: &str,
        span: &str,
        unwind: &rustc_middle::mir::UnwindAction,
    ) {
        // Frame-terminating calls. A call whose normal target is a cleanup
        // block, or that has no normal target at all, does not return to the
        // caller; the frame ends here (through its unwind chain when one
        // exists, otherwise directly at this frame's end place).
        match (target, unwind) {
            (Some(t), _) => {
                if self.body.basic_blocks[*t].is_cleanup {
                    self.handle_panic(bb_idx, name, Some(*t));
                    return;
                }
            }
            (None, rustc_middle::mir::UnwindAction::Continue) => {
                self.handle_unwind_continue(bb_idx, name);
                return;
            }
            (None, rustc_middle::mir::UnwindAction::Cleanup(bb)) => {
                // No normal target but a cleanup successor: the frame exits
                // abnormally through its unwind chain.
                self.handle_panic(bb_idx, name, Some(*bb));
                return;
            }
            (None, rustc_middle::mir::UnwindAction::Terminate(_))
            | (None, rustc_middle::mir::UnwindAction::Unreachable) => {
                self.handle_abort(bb_idx, name);
                return;
            }
        }

        let bb_term_name = crate::transition_name!(name, bb_idx, "call");
        let bb_end = self.create_call_transition(bb_idx, &bb_term_name, span);
        let callee_ty = func.ty(self.body, self.tcx);
        let callee_def_id = match callee_ty.kind() {
            rustc_middle::ty::TyKind::FnPtr(..) => {
                log::debug!("call fnptr: {:?}", callee_ty);
                self.connect_to_target(bb_idx, bb_end, target);
                return;
            }
            rustc_middle::ty::TyKind::FnDef(id, _) | rustc_middle::ty::TyKind::Closure(id, _) => {
                *id
            }
            _ => {
                panic!("TyKind::FnDef, a function definition, but got: {callee_ty:?}");
            }
        };

        let callee_func_name = crate::util::format_name(callee_def_id);
        if self.try_apply_sync_summary(&callee_func_name, args, bb_idx, bb_end, target, span) {
            return;
        }
        log::debug!("[CALLS] before track_joinhandle: {}", callee_func_name);
        self.track_joinhandle_container_call(&callee_func_name, args, destination.local);

        // `handle_lock_call` has already wired the lock arcs (with the weight
        // its guard kind requires) and connected the target; the type has to be
        // backfilled here, at the single call site, so that the transition type
        // and the arc weights always come from the same branch of
        // `handle_lock_call`. The order relative to `connect_to_target` is
        // irrelevant — the transition already exists in the builder either way.
        if let Some(call_type) = self.handle_lock_call(bb_idx, args, destination, target, bb_end) {
            self.net
                .set_transition_kind(bb_end, TransitionKind::new(call_type));
            log::debug!("callee_func_name with lock: {:?}", callee_func_name);
            return;
        }

        if self.handle_condvar_call(
            callee_def_id,
            &callee_func_name,
            args,
            bb_end,
            target,
            name,
            bb_idx,
            span,
        ) {
            log::debug!("callee_func_name with condvar: {:?}", callee_func_name);
            return;
        }

        if callee_func_name.contains("::drop") {
            log::debug!("callee_func_name with drop: {:?}", callee_func_name);
            if let Some(arg_place) = args.first().and_then(|a| a.node.place()) {
                self.add_guard_release_arcs(bb_end, &arg_place);
            }
            self.connect_to_target(bb_idx, bb_end, target);
            return;
        }

        if self.handle_thread_call(
            callee_def_id,
            &callee_func_name,
            args,
            destination.local,
            target,
            bb_end,
            &bb_idx,
            span,
        ) {
            log::debug!("callee_func_name with thread: {:?}", callee_func_name);
            return;
        }

        if self.handle_atomic_call(&callee_func_name, args, bb_end, target, &bb_idx, span) {
            log::debug!("callee_func_name with atomic: {:?}", callee_func_name);
            return;
        }

        log::debug!("callee_func_name with normal: {:?}", callee_func_name);
        if callee_func_name.contains("core::panic") {
            // An untranslated panic entry point: the call never returns, so it
            // ends this frame at the frame's own end place. (A more precise
            // unwind chain is translated where the cleanup successor is known;
            // this branch is the fallback for shapes it cannot see.)
            self.net.arc_out(self.frame_exit, bb_end, 1);
            return;
        }
        self.handle_normal_call(bb_end, target, name, bb_idx, span, &callee_def_id, args);
    }
}
