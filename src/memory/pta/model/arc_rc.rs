//! `Arc::clone` / `Rc::clone` / `ptr::read`: the result shares the source's
//! pointee. Modeled as `dest ⊇ *arg` (a `Load`), which is sound: `dest` gains
//! every object the source pointer can reach.

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, TyCtxt};

use super::{CallModel, CallNodes};
use crate::memory::ownership;
use crate::memory::pta::constraint::{Constraint, ConstraintSet};

pub struct CloneModel;

impl CallModel for CloneModel {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool {
        n_args == 1
            && (ownership::is_arc_or_rc_clone(def_id, substs, tcx)
                || ownership::is_ptr_read(def_id, tcx))
    }

    fn emit(&self, nodes: &CallNodes, out: &mut ConstraintSet) {
        if let Some(Some(arg)) = nodes.args.first().copied() {
            out.add(Constraint::Load {
                dst: nodes.dest,
                src: arg,
            });
        }
    }
}

/// `<Arc<T>/Rc<T> as Deref/DerefMut>::deref(&self) -> &T`: the result points at
/// the smart pointer's pointee. Modeled as `dest ⊇ *arg` (a `Load`) — identical
/// in shape to `CloneModel`, but matched for the deref methods so it intercepts
/// the call before the driver tries to analyze the unsafe `Arc::deref` body
/// (which would return a fresh, disconnected object).
pub struct ArcRcDerefModel;

impl CallModel for ArcRcDerefModel {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool {
        n_args == 1 && ownership::is_arc_rc_deref(def_id, substs, tcx)
    }

    fn emit(&self, nodes: &CallNodes, out: &mut ConstraintSet) {
        if let Some(Some(arg)) = nodes.args.first().copied() {
            out.add(Constraint::Load {
                dst: nodes.dest,
                src: arg,
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
    fn clone_emits_load_from_arg() {
        let model = CloneModel;
        let nodes = CallNodes {
            dest: 0,
            args: smallvec![Some(1u32)],
            fresh_heap: 9,
        };
        let mut cs = ConstraintSet::default();
        model.emit(&nodes, &mut cs);
        assert_eq!(cs.len(), 1);
        assert!(cs
            .iter()
            .any(|c| *c == Constraint::Load { dst: 0, src: 1 }));
    }

    #[test]
    fn clone_with_constant_arg_emits_nothing() {
        let model = CloneModel;
        let nodes = CallNodes {
            dest: 0,
            args: smallvec![None],
            fresh_heap: 9,
        };
        let mut cs = ConstraintSet::default();
        model.emit(&nodes, &mut cs);
        assert!(cs.is_empty());
    }

    #[test]
    fn arc_deref_emits_load_from_self_arg() {
        let model = ArcRcDerefModel;
        let nodes = CallNodes {
            dest: 0,
            args: smallvec![Some(1u32)],
            fresh_heap: 9,
        };
        let mut cs = ConstraintSet::default();
        model.emit(&nodes, &mut cs);
        assert_eq!(cs.len(), 1);
        assert!(cs
            .iter()
            .any(|c| *c == Constraint::Load { dst: 0, src: 1 }));
    }
}
