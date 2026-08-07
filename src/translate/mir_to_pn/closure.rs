//! Shared closure lowering: resolve closure/fn `DefId` and places from `Operand`.

use super::BodyToPetriNet;
use crate::net::PlaceId;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Const, Operand};
use rustc_span::Spanned;

impl<'translate, 'analysis, 'tcx> BodyToPetriNet<'translate, 'analysis, 'tcx> {
    /// Parse closure/fn `DefId` from an `Operand`.
    pub(super) fn resolve_closure_def_id(&self, arg: &Operand<'tcx>) -> Option<DefId> {
        match arg {
            Operand::Move(place) | Operand::Copy(place) => {
                let place_ty = place.ty(self.body, self.tcx).ty;
                match place_ty.kind() {
                    rustc_middle::ty::TyKind::Closure(def_id, _)
                    | rustc_middle::ty::TyKind::FnDef(def_id, _) => Some(*def_id),
                    _ => None,
                }
            }
            Operand::Constant(constant) => {
                let const_val = constant.const_;
                match const_val {
                    Const::Unevaluated(unevaluated, _) => Some(unevaluated.def),
                    _ => {
                        if let rustc_middle::ty::TyKind::Closure(def_id, _)
                        | rustc_middle::ty::TyKind::FnDef(def_id, _) = constant.ty().kind()
                        {
                            Some(*def_id)
                        } else {
                            None
                        }
                    }
                }
            }
            #[allow(unreachable_patterns)]
            _ => None,
        }
    }

    /// Parse the first closure in `args`; returns `(closure_start, closure_end)`.
    pub(super) fn resolve_closure_places(
        &self,
        args: &[Spanned<Operand<'tcx>>],
    ) -> Option<(PlaceId, PlaceId)> {
        args.first()
            .and_then(|arg| self.resolve_closure_def_id(&arg.node))
            .and_then(|def_id| self.functions_map().get(&def_id).copied())
    }

    /// Parse the closure at `args[idx]`; returns `(closure_start, closure_end)`.
    pub(super) fn resolve_closure_places_at(
        &self,
        args: &[Spanned<Operand<'tcx>>],
        index: usize,
    ) -> Option<(PlaceId, PlaceId)> {
        args.get(index)
            .and_then(|arg| self.resolve_closure_def_id(&arg.node))
            .and_then(|def_id| self.functions_map().get(&def_id).copied())
    }
}
