//! Library call models that emit inclusion constraints for selected callees.
//! A new API is a `CallModel` registration; the solver stays unchanged.
//! Models do not translate the callee's MIR.

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, TyCtxt};
use smallvec::SmallVec;

use super::constraint::{ConstraintSet, FindValue};
use super::loc::{FieldPath, LocArena, LocId};

pub mod arc_rc;
pub mod atomic;
pub mod collections;
pub mod index;
pub mod try_ops;
pub mod unknown;

/// A solved `find` predicate: the closure selects the element whose `field`
/// equals `value`. `element_field` is the projection path from the element
/// object to the compared scalar (Deref steps included, so cursor levels stay
/// distinguishable); `value` is the captured scalar (or a literal).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FindPredicate {
    pub element_field: FieldPath,
    pub value: FindValue,
}

/// Resolved location ids at a call site. `args[i]` is `None` for non-place
/// operands (e.g. constants), preserving positional alignment.
pub struct CallNodes {
    pub dest: LocId,
    pub args: SmallVec<[Option<LocId>; 4]>,
    /// A fresh allocation object available to conservative models.
    pub fresh_heap: LocId,
    /// Scratch nodes for models that need intermediate points-to values
    /// (e.g. the pointer slot read by `Vec::deref`). Distinct per call site.
    pub temps: SmallVec<[LocId; 2]>,
    /// Proven-constant integer value of each argument at this call site
    /// (`None` when not a compile-time constant / unknown). Positional like
    /// `args`; used by index-sensitive models to distinguish `[0]` from `[1]`.
    pub arg_consts: SmallVec<[Option<u64>; 4]>,
    /// Optional scalar predicate certificate for iterator-selector models
    /// (`find`): when `Some`, the model may split the selected element by the
    /// predicate identity instead of returning the merged element.
    pub predicate: Option<FindPredicate>,
}

/// A library/language call-semantics plugin.
pub trait CallModel: Send + Sync {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool;

    /// Emit the call's inclusion constraints. The arena is available so models
    /// can name field-projected slots (`Constraint::Offset`/`Copy` on
    /// `dest·p`); `nodes.temps` supplies scratch nodes for multi-step loads.
    fn emit(&self, nodes: &CallNodes, arena: &mut LocArena, out: &mut ConstraintSet);
}

/// Ordered registry of library models plus a conservative fallback.
pub struct ModelRegistry {
    models: Vec<Box<dyn CallModel>>,
    fallback: unknown::UnknownModel,
}

impl Default for ModelRegistry {
    fn default() -> Self {
        Self::builtin()
    }
}

impl ModelRegistry {
    pub fn builtin() -> Self {
        Self {
            models: vec![
                Box::new(arc_rc::CloneModel),
                Box::new(arc_rc::ArcRcDerefModel),
                Box::new(collections::VecDerefModel),
                Box::new(collections::SliceIterModel),
                Box::new(collections::SliceIterFindModel),
                Box::new(collections::SliceGetModel),
                Box::new(index::IndexModel),
                Box::new(atomic::AtomicPtrStoreModel),
                Box::new(try_ops::TryPayloadModel),
            ],
            fallback: unknown::UnknownModel,
        }
    }

    /// Register an additional model (matched before the conservative fallback).
    pub fn register(&mut self, model: Box<dyn CallModel>) {
        self.models.push(model);
    }

    /// Apply the first matching library model. Returns `true` if a model
    /// handled the call; `false` means the caller should fall back to
    /// interprocedural binding or [`Self::apply_unknown`].
    pub fn try_known_model<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        substs: &'tcx List<GenericArg<'tcx>>,
        nodes: &CallNodes,
        arena: &mut LocArena,
        out: &mut ConstraintSet,
    ) -> bool {
        let n = nodes.args.len();
        for m in &self.models {
            if m.matches(tcx, def_id, substs, n) {
                if log::log_enabled!(log::Level::Debug) {
                    log::debug!(
                        "[pta-model] hit def={} n_args={} dest={}",
                        tcx.def_path_str(def_id),
                        n,
                        nodes.dest
                    );
                }
                m.emit(nodes, arena, out);
                return true;
            }
        }
        false
    }

    /// Apply the conservative unknown-callee model.
    pub fn apply_unknown(&self, nodes: &CallNodes, arena: &mut LocArena, out: &mut ConstraintSet) {
        self.fallback.emit(nodes, arena, out);
    }
}
