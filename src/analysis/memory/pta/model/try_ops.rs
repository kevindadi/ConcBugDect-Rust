//! Models for `?` plumbing: `ok_or`, `Try::branch`, and `FromResidual`.
//! The payload moves from input variant field 0 to output variant field 0.
//! They do not distinguish `Ok` from `Err`.

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, TyCtxt};

use super::{CallModel, CallNodes};
use crate::analysis::memory::pta::constraint::{Constraint, ConstraintSet};
use crate::analysis::memory::pta::loc::{LocArena, ProjElem};

/// `Option::<T>::ok_or` / `ok_or_else`, `Try::branch` on `Result`, and
/// `FromResidual::from_residual` on `Result`.
pub struct TryPayloadModel;

impl CallModel for TryPayloadModel {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        _substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool {
        if n_args == 0 {
            return false;
        }
        let path = tcx.def_path_str(def_id);
        // `def_path_str` renders the *call-site* method resolution: inherent
        // `Option` methods print as `std::option::Option::<T>::ok_or_else`,
        // trait dispatch prints as `std::ops::Try::branch` /
        // `std::ops::FromResidual::from_residual` (the `core::...` definitions
        // appear only when the definition path is requested directly).
        if path.starts_with("std::option::") || path.starts_with("core::option::") {
            return path.ends_with("::ok_or") || path.ends_with("::ok_or_else");
        }
        if path.ends_with("Try::branch") || path.ends_with("FromResidual::from_residual") {
            return true;
        }
        false
    }

    fn emit(&self, nodes: &CallNodes, arena: &mut LocArena, out: &mut ConstraintSet) {
        let Some(Some(src)) = nodes.args.first().copied() else {
            return;
        };
        let empty = arena.empty_path();
        let payload = arena.extend_path(empty, ProjElem::Field(0));
        // `Ok`/`Err` (and `Continue`/`Break`) variants are merged, so the payload
        // of both is field 0 on either side.
        let (Some(dst), Some(src_slot)) = (
            arena.project(nodes.dest, payload),
            arena.project(src, payload),
        ) else {
            return;
        };
        out.add(Constraint::Copy { dst, src: src_slot });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::memory::pta::model::CallNodes;
    use smallvec::smallvec;

    #[test]
    fn payload_passes_through_field_zero() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let dest = arena.var(0, 0u32, empty);
        let src = arena.var(0, 1u32, empty);
        let nodes = CallNodes {
            dest,
            args: smallvec![Some(src), None],
            fresh_heap: 9,
            temps: smallvec![],
            arg_consts: smallvec![None, None],
            predicate: None,
        };
        let mut cs = ConstraintSet::default();
        TryPayloadModel.emit(&nodes, &mut arena, &mut cs);
        let payload = arena.extend_path(empty, ProjElem::Field(0));
        let dst = arena.project(dest, payload).unwrap();
        let src_slot = arena.project(src, payload).unwrap();
        assert_eq!(cs.len(), 1);
        assert!(
            cs.iter()
                .any(|c| *c == Constraint::Copy { dst, src: src_slot })
        );
    }

    #[test]
    fn no_source_operand_emits_nothing() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let dest = arena.var(0, 0u32, empty);
        let nodes = CallNodes {
            dest,
            args: smallvec![None, None],
            fresh_heap: 9,
            temps: smallvec![],
            arg_consts: smallvec![None, None],
            predicate: None,
        };
        let mut cs = ConstraintSet::default();
        TryPayloadModel.emit(&nodes, &mut arena, &mut cs);
        assert!(cs.is_empty());
    }
}
