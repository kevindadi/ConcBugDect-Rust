//! Normalize the four collectors into [`SyncSite`]s.
//!
//! This does not create Petri-net places. Lock guards, condition variables,
//! atomics, and unsafe places are read from the collectors
//! that already feed resource construction.

use rustc_middle::mir::Local;
use rustc_middle::ty::{Instance, Ty, TyCtxt};
use rustc_span::Span;

use crate::analysis::callgraph::CallGraph;
use crate::analysis::primitives::blocking::{CondVarId, LockGuardTy};
use crate::options::Options;

use super::ty::normalized_local_ty;
use super::{SiteKind, SyncSite};

/// One collector pass. Printed only when `SPN_LOG=info`.
#[derive(Clone, Copy, Debug, Default)]
pub struct CollectStats {
    pub bodies_visited: usize,
    pub alias_queries: usize,
    pub elapsed_ms: u128,
}

/// Run the lock, atomic, and unsafe collectors and return one site
/// per collected object. Custom guard-less lock methods are included so the
/// same partition can see them; with an empty `custom_lock_types` list this
/// adds nothing.
pub fn collect_sync_sites<'tcx>(
    tcx: TyCtxt<'tcx>,
    callgraph: &CallGraph<'tcx>,
    options: &Options,
    local_built: &mut dyn FnMut(&Instance<'tcx>, Local) -> bool,
) -> Vec<SyncSite<'tcx>> {
    super::extract::harvest_resources(tcx, callgraph, options, local_built).sites
}

pub(super) fn condvar_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    id: CondVarId,
) -> Option<Ty<'tcx>> {
    body.local_decls
        .get(id.local)
        .map(|_| normalized_local_ty(tcx, instance, body, id.local))
}

pub(crate) fn guard_protected_ty<'tcx>(ty: &LockGuardTy<'tcx>) -> Ty<'tcx> {
    guard_class(ty).1
}

pub(super) fn guard_class<'tcx>(ty: &LockGuardTy<'tcx>) -> (SiteKind, Ty<'tcx>) {
    match *ty {
        LockGuardTy::StdMutex(inner)
        | LockGuardTy::ParkingLotMutex(inner)
        | LockGuardTy::SpinMutex(inner) => (SiteKind::Mutex, inner),
        LockGuardTy::StdRwLockRead(inner)
        | LockGuardTy::StdRwLockWrite(inner)
        | LockGuardTy::ParkingLotRead(inner)
        | LockGuardTy::ParkingLotWrite(inner)
        | LockGuardTy::SpinRead(inner)
        | LockGuardTy::SpinWrite(inner) => (SiteKind::RwLock, inner),
    }
}

pub(super) fn span_string(span: Span) -> String {
    format!("{span:?}")
}
