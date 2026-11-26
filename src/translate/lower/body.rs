//! Basic-block walk: statements and terminators.

use super::BodyToPetriNet;
use super::control_flow;
use crate::translate::net::PlaceId;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Body, Statement, StatementKind, Terminator, TerminatorKind,
    visit::Visitor,
};
use rustc_middle::mir::{Const, Operand};
use rustc_span::Spanned;

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    fn handle_terminator(
        &mut self,
        term: &Terminator<'tcx>,
        bb_idx: BasicBlock,
        name: &str,
        bb: &BasicBlockData<'tcx>,
    ) {
        match &term.kind {
            TerminatorKind::Goto { target, .. } => self.handle_goto(bb_idx, target, name),
            TerminatorKind::SwitchInt { targets, .. } => self.handle_switch(bb_idx, targets, name),
            TerminatorKind::Return => self.handle_return(bb_idx, name),
            TerminatorKind::Assert { target, .. } => {
                self.handle_assert(bb_idx, target, name);
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                ..
            } => {
                self.handle_call(
                    bb_idx,
                    func,
                    args,
                    destination,
                    target,
                    name,
                    &format!("{:?}", term.source_info.span),
                    unwind,
                );
            }
            TerminatorKind::Drop { place, target, .. } => {
                self.handle_drop(&bb_idx, place, target, name, bb)
            }
            TerminatorKind::FalseEdge { real_target, .. } => {
                self.handle_fallthrough(bb_idx, real_target, name, "false_edge");
            }
            TerminatorKind::FalseUnwind { real_target, .. } => {
                self.handle_fallthrough(bb_idx, real_target, name, "false_unwind");
            }
            TerminatorKind::Yield { resume, .. } => {
                self.handle_fallthrough(bb_idx, resume, name, "yield");
            }
            TerminatorKind::InlineAsm {
                targets, unwind: _, ..
            } => {
                if let Some(target) = targets.first() {
                    self.handle_fallthrough(bb_idx, target, name, "inline_asm");
                } else {
                    self.handle_terminal_block(bb_idx, name, "inline_asm_noreturn");
                }
            }
            TerminatorKind::Unreachable => {
                self.handle_terminal_block(bb_idx, name, "unreachable");
            }
            TerminatorKind::UnwindResume => {
                self.handle_terminal_block(bb_idx, name, "unwind_resume");
            }
            TerminatorKind::UnwindTerminate(_) => {
                self.handle_terminal_block(bb_idx, name, "unwind_terminate");
            }
            TerminatorKind::CoroutineDrop => {
                self.handle_terminal_block(bb_idx, name, "coroutine_drop");
            }
            TerminatorKind::TailCall { .. } => {
                self.handle_terminal_block(bb_idx, name, "tail_call");
            }
        }
    }

    fn visit_statement_body(&mut self, statement: &Statement<'tcx>, bb_idx: BasicBlock) {
        let span_str = format!("{:?}", statement.source_info.span);
        if let StatementKind::Assign((dest, rvalue)) = &statement.kind {
            let fn_name = self.frame_name.clone();
            self.track_joinhandle_dataflow(dest.local, rvalue);

            self.process_rvalue_reads(rvalue, &fn_name, bb_idx, &span_str);

            self.process_place_writes(dest, &fn_name, bb_idx, &span_str);
        }
    }
}

impl<'translate, 'analysis, 'tcx> Visitor<'tcx> for BodyToPetriNet<'translate, 'analysis, 'tcx> {
    fn visit_body(&mut self, body: &Body<'tcx>) {
        let fn_name = self.frame_name.clone();

        if fn_name.contains("::deserialize")
            || fn_name.contains("::serialize")
            || fn_name.contains("::visit_seq")
            || fn_name.contains("::visit_map")
        {
            log::warn!("Skipping serialization function: {}", fn_name);
            return;
        }

        self.init_basic_block(body, &fn_name);

        if self.break_cfg_cycles {
            self.back_edges = control_flow::compute_back_edges(body);
        }

        for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
            if bb.is_cleanup || bb.is_empty_unreachable() {
                continue;
            }

            for stmt in bb.statements.iter() {
                if let Some(ref term) = bb.terminator {
                    if let TerminatorKind::Assert { .. } = &term.kind {
                        break;
                    }
                }
                self.visit_statement_body(stmt, bb_idx);
            }

            self.flush_unsafe_ops(bb_idx);

            if bb_idx.index() == 0 {
                self.handle_start_block(&fn_name, bb_idx);
            }

            if let Some(term) = &bb.terminator {
                self.handle_terminator(term, bb_idx, &fn_name, bb);
            }
        }
    }
}

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// Parse closure/fn `DefId` from an `Operand`.
    pub(super) fn resolve_closure_def_id(&self, arg: &Operand<'tcx>) -> Option<DefId> {
        match arg {
            Operand::Move(place) | Operand::Copy(place) => {
                let place_ty = place.ty(self.body, self.tcx).ty;
                match place_ty.kind() {
                    rustc_middle::ty::TyKind::Closure(def_id, _)
                    | rustc_middle::ty::TyKind::FnDef(def_id, _)
                    | rustc_middle::ty::TyKind::Coroutine(def_id, _) => Some(*def_id),
                    rustc_middle::ty::TyKind::CoroutineClosure(def_id, _) => {
                        Some(self.tcx.coroutine_for_closure(*def_id))
                    }
                    _ => None,
                }
            }
            Operand::Constant(constant) => {
                let const_val = constant.const_;
                match const_val {
                    Const::Unevaluated(unevaluated, _) => Some(unevaluated.def),
                    _ => {
                        if let rustc_middle::ty::TyKind::Closure(def_id, _)
                        | rustc_middle::ty::TyKind::FnDef(def_id, _)
                        | rustc_middle::ty::TyKind::Coroutine(def_id, _) = constant.ty().kind()
                        {
                            Some(*def_id)
                        } else {
                            None
                        }
                    }
                }
            }
            #[allow(unreachable_patterns)]
            _ => None,
        }
    }

    /// Parse the first closure in `args`; returns `(closure_start, closure_end)`.
    pub(super) fn resolve_closure_places(
        &self,
        args: &[Spanned<Operand<'tcx>>],
    ) -> Option<(PlaceId, PlaceId)> {
        args.first()
            .and_then(|arg| self.resolve_closure_def_id(&arg.node))
            .and_then(|def_id| self.functions_map().get(&def_id).copied())
    }

    /// Parse the closure at `args[idx]`; returns `(closure_start, closure_end)`.
    pub(super) fn resolve_closure_places_at(
        &self,
        args: &[Spanned<Operand<'tcx>>],
        index: usize,
    ) -> Option<(PlaceId, PlaceId)> {
        args.get(index)
            .and_then(|arg| self.resolve_closure_def_id(&arg.node))
            .and_then(|def_id| self.functions_map().get(&def_id).copied())
    }
}
