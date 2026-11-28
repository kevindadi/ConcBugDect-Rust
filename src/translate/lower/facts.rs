//! Body-lowering helpers that fill function facts and guard maps.
//! Transition origins are recorded by `NetBuilder::transition`.

use super::BodyToPetriNet;
use rustc_middle::mir::{BasicBlock, StatementKind, TerminatorKind};

pub use crate::translate::net::provenance::{
    BbFacts, DefRecord, FunctionFacts, GuardFacts, LoopSummaryFacts, TransOrigin,
    TranslationProvenance, call_summary, def_operands, is_guard_terminator, operand_root_local,
    operand_summary, root_locals, rvalue_summary,
};
use crate::translate::net::{TransitionId, TransitionKind, TransitionType};

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// Forward a transition to `NetBuilder::transition`.
    ///
    /// The origin is stored on the kind. `NetBuilder::transition` is the only
    /// place that appends it. This function does not write the provenance table.
    pub(super) fn new_transition(
        &mut self,
        name: String,
        transition_type: TransitionType,
        bb: BasicBlock,
        span: String,
    ) -> TransitionId {
        self.net.transition(
            TransitionKind::with_origin(
                transition_type,
                TransOrigin {
                    fn_def_path: self.fn_path.clone(),
                    bb: bb.index(),
                    span,
                },
            ),
            name,
        )
    }

    /// The span recorded for `bb`'s terminator, in the `{:?}` form the rest of
    /// the translation uses for places.
    pub(super) fn bb_span(&self, bb: BasicBlock) -> String {
        self.body.basic_blocks[bb]
            .terminator
            .as_ref()
            .map_or(String::new(), |term| format!("{:?}", term.source_info.span))
    }

    /// Record that `transition` implements the data-dependent branch of `bb`
    /// (a `SwitchInt` target or the `Assert` success edge).
    pub(super) fn record_guard_transition(&mut self, bb: BasicBlock, transition: TransitionId) {
        self.net
            .provenance_mut()
            .guard_transitions
            .entry(self.fn_path.clone())
            .or_default()
            .entry(bb.index())
            .or_default()
            .push(transition.index());
    }

    /// Record the MIR facts of this body: per-block definitions and branch
    /// guards, and the local spans. Runs before the body is translated.
    pub(super) fn record_function_facts(&mut self) {
        let mut function = FunctionFacts {
            arg_count: self.body.arg_count,
            ..FunctionFacts::default()
        };

        for (local, decl) in self.body.local_decls.iter_enumerated() {
            function
                .locals
                .insert(local.index(), format!("{:?}", decl.source_info.span));
        }

        for (bb_idx, bb) in self.body.basic_blocks.iter_enumerated() {
            if bb.is_empty_unreachable() {
                continue;
            }
            let mut facts = BbFacts::default();
            for stmt in &bb.statements {
                if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                    facts.defs.push(DefRecord {
                        local: place.local.index(),
                        span: format!("{:?}", stmt.source_info.span),
                        rhs: rvalue_summary(rvalue),
                        operands: def_operands(rvalue),
                        stop_recursion: false,
                    });
                }
            }
            if let Some(term) = &bb.terminator {
                match &term.kind {
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        ..
                    } => {
                        let arg_places: Vec<rustc_middle::mir::Place<'tcx>> =
                            args.iter().filter_map(|arg| arg.node.place()).collect();
                        facts.defs.push(DefRecord {
                            local: destination.local.index(),
                            span: format!("{:?}", term.source_info.span),
                            rhs: call_summary(func, args, self.body, self.tcx),
                            operands: root_locals(arg_places.iter()),
                            // The chain stops at a call; the span points into
                            // the caller, and the callee is a separate frame
                            // when it is translated at all.
                            stop_recursion: true,
                        });
                    }
                    TerminatorKind::SwitchInt { discr, targets } => {
                        let mut list: Vec<(Option<u128>, usize)> = targets
                            .iter()
                            .map(|(value, target)| (Some(value), target.index()))
                            .collect();
                        list.push((None, targets.otherwise().index()));
                        facts.guard = Some(GuardFacts::Switch {
                            operand: operand_summary(discr),
                            operand_local: operand_root_local(discr),
                            targets: list,
                        });
                    }
                    TerminatorKind::Assert {
                        cond,
                        expected,
                        target,
                        ..
                    } => {
                        facts.guard = Some(GuardFacts::Assert {
                            operand: operand_summary(cond),
                            operand_local: operand_root_local(cond),
                            expected: *expected,
                            target: target.index(),
                        });
                    }
                    _ => {}
                }
            }
            function.bbs.insert(bb_idx.index(), facts);
        }

        self.net
            .provenance_mut()
            .functions
            .insert(self.fn_path.clone(), function);
    }

    /// Record the back edges cycle breaking removed from this body. Called
    /// after `visit_body`, which computes them.
    pub(super) fn record_cut_back_edges(&mut self) {
        if self.back_edges.is_empty() {
            return;
        }
        let mut list: Vec<(usize, usize)> = self
            .back_edges
            .iter()
            .map(|(from, to)| (from.index(), to.index()))
            .collect();
        list.sort_unstable();
        self.net
            .provenance_mut()
            .functions
            .entry(self.fn_path.clone())
            .or_default()
            .cut_back_edges = list;
    }
}
