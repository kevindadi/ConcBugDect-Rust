//! `AtomicPtr::store(self, ptr, ordering)`: the atomic comes to hold the stored
//! pointer. Modeled as `self ⊇ ptr` (a `Copy`), matching the legacy analysis.

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, TyCtxt};

use super::{CallModel, CallNodes};
use crate::concurrency::atomic::is_atomic_ptr_store;
use crate::memory::pta::constraint::{Constraint, ConstraintSet};

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

    fn emit(&self, nodes: &CallNodes, out: &mut ConstraintSet) {
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
    use crate::memory::pta::model::CallNodes;
    use smallvec::smallvec;

    #[test]
    fn atomic_store_copies_value_into_atomic() {
        let model = AtomicPtrStoreModel;
        let nodes = CallNodes {
            dest: 0,
            args: smallvec![Some(3u32), Some(4u32), None],
            fresh_heap: 9,
        };
        let mut cs = ConstraintSet::default();
        model.emit(&nodes, &mut cs);
        assert_eq!(cs.len(), 1);
        assert!(cs
            .iter()
            .any(|c| *c == Constraint::Copy { dst: 3, src: 4 }));
    }
}
