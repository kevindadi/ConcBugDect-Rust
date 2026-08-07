//! Library / language call-semantics models.
//!
//! Each [`CallModel`] matches a callee (by `DefId` / generic args / arity) and
//! emits inclusion constraints for the call. This is the extension point for
//! teaching the analysis about new APIs: implement [`CallModel`] and register
//! it — the solver never changes. Constraint emission (`emit`) is rustc-free
//! and unit tested per model.

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, TyCtxt};
use smallvec::SmallVec;

use super::constraint::ConstraintSet;
use super::loc::LocId;

pub mod arc_rc;
pub mod atomic;
pub mod index;
pub mod unknown;

/// Resolved location ids at a call site. `args[i]` is `None` for non-place
/// operands (e.g. constants), preserving positional alignment.
pub struct CallNodes {
    pub dest: LocId,
    pub args: SmallVec<[Option<LocId>; 4]>,
    /// A fresh allocation object available to conservative models.
    pub fresh_heap: LocId,
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

    fn emit(&self, nodes: &CallNodes, out: &mut ConstraintSet);
}

/// Ordered registry of specialized models plus a conservative fallback.
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
                Box::new(index::IndexModel),
                Box::new(atomic::AtomicPtrStoreModel),
            ],
            fallback: unknown::UnknownModel,
        }
    }

    /// Register an additional model (matched before the conservative fallback).
    pub fn register(&mut self, model: Box<dyn CallModel>) {
        self.models.push(model);
    }

    /// Apply the first matching specialized model. Returns `true` if a model
    /// handled the call; `false` means the caller should fall back to
    /// interprocedural binding or [`Self::apply_unknown`].
    pub fn try_specialized<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        substs: &'tcx List<GenericArg<'tcx>>,
        nodes: &CallNodes,
        out: &mut ConstraintSet,
    ) -> bool {
        let n = nodes.args.len();
        for m in &self.models {
            if m.matches(tcx, def_id, substs, n) {
                m.emit(nodes, out);
                return true;
            }
        }
        false
    }

    /// Apply the conservative unknown-callee model.
    pub fn apply_unknown(&self, nodes: &CallNodes, out: &mut ConstraintSet) {
        self.fallback.emit(nodes, out);
    }
}
