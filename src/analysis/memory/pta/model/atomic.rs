//! `AtomicPtr::store(self, ptr, ordering)`: the atomic comes to hold the stored
//! pointer. Modeled as `self ⊇ ptr` (a `Copy`), matching the legacy analysis.

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, TyCtxt};

use super::{CallModel, CallNodes};
use crate::analysis::memory::pta::constraint::{Constraint, ConstraintSet};
use crate::analysis::memory::pta::loc::LocArena;
use crate::analysis::primitives::atomic::is_atomic_ptr_store;

pub struct AtomicPtrStoreModel;

impl CallModel for AtomicPtrStoreModel {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool {
        n_args == 3 && is_atomic_ptr_store(def_id, substs, tcx)
    }

    fn emit(&self, nodes: &CallNodes, _arena: &mut LocArena, out: &mut ConstraintSet) {
        let atomic = nodes.args.first().copied().flatten();
        let value = nodes.args.get(1).copied().flatten();
        if let (Some(atomic), Some(value)) = (atomic, value) {
            out.add(Constraint::Copy {
                dst: atomic,
                src: value,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::memory::pta::model::CallNodes;
    use smallvec::smallvec;

    #[test]
    fn atomic_store_copies_value_into_atomic() {
        let model = AtomicPtrStoreModel;
        let nodes = CallNodes {
            dest: 0,
            args: smallvec![Some(3u32), Some(4u32), None],
            fresh_heap: 9,
            temps: smallvec![],
            arg_consts: smallvec![],
            predicate: None,
        };
        let mut cs = ConstraintSet::default();
        model.emit(&nodes, &mut LocArena::default(), &mut cs);
        assert_eq!(cs.len(), 1);
        assert!(cs.iter().any(|c| *c == Constraint::Copy { dst: 3, src: 4 }));
    }
}
