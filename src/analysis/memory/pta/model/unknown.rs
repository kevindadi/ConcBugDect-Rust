//! Model for callees with no MIR.
//! The result is a fresh object that may alias any pointer argument.
//! It does not recover the callee's real points-to set.

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, TyCtxt};

use super::{CallModel, CallNodes};
use crate::analysis::memory::pta::constraint::{Constraint, ConstraintSet};
use crate::analysis::memory::pta::loc::LocArena;

pub struct UnknownModel;

impl CallModel for UnknownModel {
    fn matches<'tcx>(
        &self,
        _tcx: TyCtxt<'tcx>,
        _def_id: DefId,
        _substs: &'tcx List<GenericArg<'tcx>>,
        _n_args: usize,
    ) -> bool {
        true
    }

    fn emit(&self, nodes: &CallNodes, _arena: &mut LocArena, out: &mut ConstraintSet) {
        out.add(Constraint::AddressOf {
            dst: nodes.dest,
            obj: nodes.fresh_heap,
        });
        for arg in &nodes.args {
            if let Some(arg) = arg {
                out.add(Constraint::Copy {
                    dst: nodes.dest,
                    src: *arg,
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::memory::pta::model::CallNodes;
    use smallvec::smallvec;

    #[test]
    fn unknown_seeds_heap_and_copies_pointer_args() {
        let model = UnknownModel;
        let nodes = CallNodes {
            dest: 0,
            args: smallvec![Some(1u32), None, Some(2u32)],
            fresh_heap: 9,
            temps: smallvec![],
            arg_consts: smallvec![],
            predicate: None,
        };
        let mut cs = ConstraintSet::default();
        model.emit(&nodes, &mut LocArena::default(), &mut cs);
        assert_eq!(cs.len(), 3);
        assert!(
            cs.iter()
                .any(|c| *c == Constraint::AddressOf { dst: 0, obj: 9 })
        );
        assert!(cs.iter().any(|c| *c == Constraint::Copy { dst: 0, src: 1 }));
        assert!(cs.iter().any(|c| *c == Constraint::Copy { dst: 0, src: 2 }));
    }
}
