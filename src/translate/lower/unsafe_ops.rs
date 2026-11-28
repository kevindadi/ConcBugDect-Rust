//! Unsafe accesses merged into one transition per basic block
//! (`process_rvalue_reads`, `process_place_writes`, `flush_unsafe_ops`).
//! Guard drops live in `crate::translate::lower::call::drop`.

use super::BodyToPetriNet;
use crate::translate::net::{TransitionType, UnsafeOp};
use crate::{analysis::memory::pointsto::AliasId, translate::mir_utils::rvalue_read_places};
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::{BasicBlock, Rvalue};

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// Whether `place_id` accesses an unsafe variable; returns the alias-group id
    /// when it does. No Petri-net place is involved — the group id is what gets
    /// recorded in the merged `UnsafeAccess` transition.
    ///
    /// TODO: unsafe classes are not `ResourceMap` places. The group id is the
    /// registry's `unsafe_groups` entry.
    pub(super) fn has_unsafe_alias(&self, place_id: AliasId) -> (bool, u32, Option<AliasId>) {
        for (unsafe_alias, group_id) in self.resources.unsafe_groups().iter() {
            if self
                .alias
                .borrow_mut()
                .alias_atomic(place_id, *unsafe_alias)
                .may_alias(self.alias_unknown_policy)
            {
                return (true, *group_id, Some(*unsafe_alias));
            }
        }
        (false, 0, None)
    }

    pub(super) fn process_rvalue_reads(
        &mut self,
        rvalue: &Rvalue<'tcx>,
        _fn_name: &str,
        bb_idx: BasicBlock,
        span_str: &str,
    ) {
        let places = rvalue_read_places(rvalue);

        for place in places {
            let place_id = AliasId::new(self.instance_id, place.local);
            let place_ty = format!("{:?}", place.ty(self.body, self.tcx));

            let alias_result = self.has_unsafe_alias(place_id);
            if alias_result.0 {
                self.pending_unsafe_ops.push(UnsafeOp {
                    alias: alias_result.1 as usize,
                    is_write: false,
                    span: span_str.to_string(),
                    basic_block: bb_idx.index(),
                    ty: place_ty,
                });
            }
        }
    }

    pub(super) fn process_place_writes(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        _fn_name: &str,
        bb_idx: BasicBlock,
        span_str: &str,
    ) {
        let place_id = AliasId::new(self.instance_id, place.local);
        let place_ty = format!("{:?}", place.ty(self.body, self.tcx));

        let alias_result = self.has_unsafe_alias(place_id);
        if alias_result.0 {
            self.pending_unsafe_ops.push(UnsafeOp {
                alias: alias_result.1 as usize,
                is_write: true,
                span: span_str.to_string(),
                basic_block: bb_idx.index(),
                ty: place_ty,
            });
        }
    }

    /// Emit one merged unsafe transition for the current basic block, collapsing
    /// every buffered access to one operation per alias-group (a write wins over
    /// reads for the same variable). The transition needs no unsafe resource
    /// places; the data-race detector compares the group ids carried here.
    pub(super) fn flush_unsafe_ops(&mut self, bb_idx: BasicBlock) {
        if self.pending_unsafe_ops.is_empty() {
            return;
        }

        let mut merged: FxHashMap<usize, UnsafeOp> = FxHashMap::default();
        for op in self.pending_unsafe_ops.drain(..) {
            match merged.entry(op.alias) {
                std::collections::hash_map::Entry::Occupied(mut e) => {
                    if op.is_write {
                        e.insert(op);
                    }
                }
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(op);
                }
            }
        }
        let ops: Vec<UnsafeOp> = merged.into_values().collect();

        let fn_name = crate::util::format_name(self.instance.def_id());
        let transition_name = format!("{}_unsafe_bb{}", fn_name, bb_idx.index());
        let span = self.bb_span(bb_idx);
        let transition_id = self.new_transition(
            transition_name.clone(),
            TransitionType::UnsafeAccess(ops),
            bb_idx,
            span,
        );
        let last_node = self.bb_graph.last(bb_idx);
        self.net.arc_in(last_node, transition_id, 1);
        let temp_place = crate::bb_place!(
            self.net,
            format!("{}_unsafe_ready", transition_name),
            String::new()
        );
        self.net.arc_out(temp_place, transition_id, 1);
        self.bb_graph.push(bb_idx, temp_place);
    }
}
