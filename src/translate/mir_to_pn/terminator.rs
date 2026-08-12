//! Terminators: `init_basic_block`, `handle_start_block`, `handle_goto`, `handle_switch`, `handle_return`, …

use super::BodyToPetriNet;
use unipn::pt::{PtTransition, TransitionType};
use unipn::TransitionId;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, SwitchTargets};

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    pub(super) fn init_basic_block(&mut self, body: &Body<'tcx>, body_name: &str) {
        for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
            if bb.is_cleanup || bb.is_empty_unreachable() {
                self.exclude_bb.insert(bb_idx.index());
                continue;
            }
            let bb_span = bb.terminator.as_ref().map_or("".to_string(), |term| {
                format!("{:?}", term.source_info.span)
            });

            let bb_name = format!("{}_{}", body_name, bb_idx.index());
            let bb_start = crate::bb_place!(self.net, bb_name, bb_span);
            self.bb_graph.register(bb_idx, bb_start);
        }
    }

    pub(super) fn handle_start_block(&mut self, name: &str, bb_idx: BasicBlock, def_id: DefId) {
        let bb_start_name = format!("{}_{}_start", name, bb_idx.index());
        let bb_start_transition = Transition::new_with_transition_type(
            bb_start_name,
            TransitionType::Start(self.instance_id.index()),
        );
        let bb_start = self.net.add_transition(bb_start_transition);

        if let Some((func_start, _)) = self.functions_map().get(&def_id).copied() {
            self.net.add_input_arc(func_start, bb_start, 1);
        }
        self.net
            .add_output_arc(self.bb_graph.start(bb_idx), bb_start, 1);
    }

    pub(super) fn handle_assert(&mut self, bb_idx: BasicBlock, target: &BasicBlock, name: &str) {
        if self.is_back_edge(bb_idx, *target) {
            return;
        }
        crate::add_fallthrough_transition!(
            self,
            bb_idx,
            name,
            "assert",
            TransitionType::Assert,
            target
        );
    }

    pub(super) fn handle_fallthrough(
        &mut self,
        bb_idx: BasicBlock,
        target: &BasicBlock,
        name: &str,
        kind: &str,
    ) {
        if self.exclude_bb.contains(&target.index()) {
            log::debug!(
                "Fallthrough {} from bb{} to excluded bb{}",
                kind,
                bb_idx.index(),
                target.index()
            );
            return;
        }
        if self.is_back_edge(bb_idx, *target) {
            return;
        }

        crate::add_fallthrough_transition!(self, bb_idx, name, kind, TransitionType::Goto, target);
    }

    pub(super) fn handle_terminal_block(&mut self, bb_idx: BasicBlock, name: &str, kind: &str) {
        crate::add_terminal_transition!(
            self,
            bb_idx,
            name,
            kind,
            TransitionType::Return(self.instance_id.index())
        );
    }

    pub(super) fn handle_goto(&mut self, bb_idx: BasicBlock, target: &BasicBlock, name: &str) {
        if self.body.basic_blocks[*target].is_cleanup {
            self.handle_panic(bb_idx, name);
            return;
        }
        if self.is_back_edge(bb_idx, *target) {
            return;
        }

        crate::add_fallthrough_transition!(
            self,
            bb_idx,
            name,
            "goto",
            TransitionType::Goto,
            target
        );
    }

    pub(super) fn handle_switch(
        &mut self,
        bb_idx: BasicBlock,
        targets: &SwitchTargets,
        name: &str,
    ) {
        let mut t_num = 1u8;
        for t in targets.all_targets() {
            if self.exclude_bb.contains(&t.index()) {
                continue;
            }
            if self.is_back_edge(bb_idx, *t) {
                continue;
            }
            let bb_term_name = crate::transition_name!(name, bb_idx, "switch", t_num.to_string());
            t_num += 1;
            let bb_term_transition =
                Transition::new_with_transition_type(bb_term_name, TransitionType::Switch);
            let bb_end = self.net.add_transition(bb_term_transition);

            self.net
                .add_input_arc(self.bb_graph.last(bb_idx), bb_end, 1);
            let target_bb_start = self.bb_graph.start(*t);
            self.net.add_output_arc(target_bb_start, bb_end, 1);
        }
    }

    pub(super) fn handle_return(&mut self, bb_idx: BasicBlock, name: &str) {
        let return_node = self
            .functions_map()
            .get(&self.instance.def_id())
            .map(|(_, end)| *end)
            .expect("return place missing");

        if self.return_transition.raw() == 0 {
            let bb_term_name = crate::transition_name!(name, bb_idx, "return");
            let bb_term_transition = Transition::new_with_transition_type(
                bb_term_name,
                TransitionType::Return(self.instance_id.index()),
            );
            let bb_end = self.net.add_transition(bb_term_transition);

            self.return_transition = bb_end.clone();
        }

        self.net
            .add_input_arc(self.bb_graph.last(bb_idx), self.return_transition, 1);
        self.net
            .add_output_arc(return_node, self.return_transition, 1);
    }

    pub(super) fn create_call_transition(
        &mut self,
        bb_idx: BasicBlock,
        bb_term_name: &str,
    ) -> TransitionId {
        let bb_term_transition = Transition::new_with_transition_type(
            bb_term_name.to_string(),
            TransitionType::Function,
        );
        let bb_end = self.net.add_transition(bb_term_transition);

        self.net
            .add_input_arc(self.bb_graph.last(bb_idx), bb_end, 1);
        bb_end
    }

    pub(super) fn connect_to_target(
        &mut self,
        _bb_idx: BasicBlock,
        bb_end: TransitionId,
        target: &Option<BasicBlock>,
    ) {
        if let Some(target_bb) = target {
            self.net
                .add_output_arc(self.bb_graph.start(*target_bb), bb_end, 1);
        }
    }

    pub(super) fn handle_unwind_continue(&mut self, bb_idx: BasicBlock, name: &str) {
        crate::add_terminal_transition!(
            self,
            bb_idx,
            name,
            "unwind",
            TransitionType::Return(self.instance_id.index())
        );
    }

    pub(super) fn handle_panic(&mut self, bb_idx: BasicBlock, name: &str) {
        crate::add_terminal_transition!(
            self,
            bb_idx,
            name,
            "panic",
            TransitionType::Return(self.instance_id.index())
        );
    }
}
