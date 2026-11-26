//! `Index::index` (e.g. `Vec`/slice indexing): the result aliases the
//! container. Modeled as `dest ⊇ container` (a `Copy`), matching the legacy
//! analysis behavior.

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, TyCtxt};

use super::{CallModel, CallNodes};
use crate::analysis::memory::ownership;
use crate::analysis::memory::pta::constraint::{Constraint, ConstraintSet};
use crate::analysis::memory::pta::loc::LocArena;

pub struct IndexModel;

impl CallModel for IndexModel {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        _substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool {
        n_args == 2 && ownership::is_index(def_id, tcx)
    }

    fn emit(&self, nodes: &CallNodes, _arena: &mut LocArena, out: &mut ConstraintSet) {
        if let Some(Some(container)) = nodes.args.first().copied() {
            out.add(Constraint::Copy {
                dst: nodes.dest,
                src: container,
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
    fn index_emits_copy_from_container() {
        let model = IndexModel;
        let nodes = CallNodes {
            dest: 5,
            args: smallvec![Some(2u32), None],
            fresh_heap: 9,
            temps: smallvec![],
            arg_consts: smallvec![],
            predicate: None,
        };
        let mut cs = ConstraintSet::default();
        model.emit(&nodes, &mut LocArena::default(), &mut cs);
        assert_eq!(cs.len(), 1);
        assert!(cs.iter().any(|c| *c == Constraint::Copy { dst: 5, src: 2 }));
    }
}
