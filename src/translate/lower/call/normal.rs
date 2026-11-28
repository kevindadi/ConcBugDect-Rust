//! Inlined call: wait/return subnet when the callee has a frame, otherwise a black box.

use super::super::BodyToPetriNet;
use crate::translate::net::{PlaceId, TransitionId, TransitionType};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Operand};
use rustc_span::Spanned;

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// The frame a call to `callee` enters. Each function is modeled once.
    fn callee_frame(&self, callee: &DefId) -> Option<(PlaceId, PlaceId)> {
        self.functions_map().get(callee).copied()
    }
    pub(in crate::translate::lower) fn handle_normal_call(
        &mut self,
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
        name: &str,
        bb_idx: BasicBlock,
        span: &str,
        callee_id: &DefId,
        args: &Box<[Spanned<Operand<'tcx>>]>,
    ) {
        if let Some((callee_start, callee_end)) = self.callee_frame(callee_id) {
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
            return;
        }

        if self.handle_indirect_call(bb_end, target, bb_idx, span, callee_id, args) {
            return;
        }
        self.record_opaque_call(callee_id, span);
        self.connect_to_target(bb_idx, bb_end, target);
    }
    fn record_opaque_call(&mut self, callee_id: &DefId, span: &str) {
        let mut has_with_body = false;
        let mut has_without_body = false;
        for node in self.callgraph.graph.node_weights() {
            if node.instance().def_id() == *callee_id {
                match node {
                    crate::analysis::callgraph::CallGraphNode::WithBody(_) => {
                        has_with_body = true;
                    }
                    crate::analysis::callgraph::CallGraphNode::WithoutBody(_) => {
                        has_without_body = true;
                    }
                }
            }
        }
        let callee_name = crate::util::format_name(*callee_id);
        let registered = self.key_api_regex.sync.lookup(&callee_name).is_some();
        let reason = if self.key_api_regex.sync.uses_table() && !registered {
            crate::report::coverage::OpaqueCallReason::Unregistered
        } else if has_with_body {
            crate::report::coverage::OpaqueCallReason::Filtered
        } else if has_without_body {
            crate::report::coverage::OpaqueCallReason::WithoutBody
        } else if !self.tcx.is_mir_available(*callee_id) {
            crate::report::coverage::OpaqueCallReason::NoMir
        } else {
            crate::report::coverage::OpaqueCallReason::Filtered
        };
        self.coverage.record_opaque_call(
            callee_name,
            self.fn_path.clone(),
            reason,
            span.to_string(),
        );
    }
}
