//! Conservative model for callees the analysis cannot see (no MIR, FFI, etc.).
//!
//! Default (sound baseline): the result gets a fresh allocation object and may
//! alias any pointer argument (`dest ⊇ arg`). Write-through `&mut` arguments
//! under the conservative alias policy is layered on in a later task.

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, TyCtxt};

use super::{CallModel, CallNodes};
use crate::memory::pta::constraint::{Constraint, ConstraintSet};

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

    fn emit(&self, nodes: &CallNodes, out: &mut ConstraintSet) {
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
    use crate::memory::pta::model::CallNodes;
    use smallvec::smallvec;

    #[test]
    fn unknown_seeds_heap_and_copies_pointer_args() {
        let model = UnknownModel;
        let nodes = CallNodes {
            dest: 0,
            args: smallvec![Some(1u32), None, Some(2u32)],
            fresh_heap: 9,
        };
        let mut cs = ConstraintSet::default();
        model.emit(&nodes, &mut cs);
        assert_eq!(cs.len(), 3);
        assert!(cs
            .iter()
            .any(|c| *c == Constraint::AddressOf { dst: 0, obj: 9 }));
        assert!(cs.iter().any(|c| *c == Constraint::Copy { dst: 0, src: 1 }));
        assert!(cs.iter().any(|c| *c == Constraint::Copy { dst: 0, src: 2 }));
    }
}
