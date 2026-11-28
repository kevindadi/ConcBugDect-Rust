//! Indirect call: a closure or fn value passed as an argument, when the
//! callee itself has no frame.

use super::super::BodyToPetriNet;
use crate::translate::net::{TransitionId, TransitionType};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Operand};
use rustc_span::Spanned;

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    pub(in crate::translate::lower) fn handle_indirect_call(
        &mut self,
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        bb_idx: BasicBlock,
        span: &str,
        callee_id: &DefId,
        args: &Box<[Spanned<Operand<'tcx>>]>,
    ) -> bool {
        let name = self.tcx.def_path_str(*callee_id);
        for i in 0..args.len() {
            if let Some((callee_start, callee_end)) = self.resolve_closure_places_at(args, i) {
                let (_bb_wait, bb_ret) = crate::add_wait_ret_subnet!(
                    self,
                    name,
                    bb_idx,
                    "wait",
                    "return",
                    TransitionType::Function,
                    span.to_string(),
                    bb_end
                );

                self.net.arc_out(callee_start, bb_end, 1);
                if let Some(return_block) = target {
                    self.net.arc_in(callee_end, bb_ret, 1);
                    if self.is_back_edge(bb_idx, *return_block) {
                        self.record_cut_back_edge(super::super::CutBackEdge::After {
                            source: bb_idx,
                            target: *return_block,
                            after: bb_ret,
                        });
                    } else {
                        self.net
                            .arc_out(self.bb_graph.start(*return_block), bb_ret, 1);
                    }
                }
                return true;
            }
        }
        false
    }
}
