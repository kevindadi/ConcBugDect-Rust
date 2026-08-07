//! Interprocedural binding primitives.
//!
//! [`bind_call_edges`] is the pure (rustc-free) core: given a callee's formal
//! parameter nodes and return node, and the caller's actual-argument nodes and
//! destination node, it produces the `Copy` constraints that link them
//! (`param ⊇ arg`, `dest ⊇ return`). [`FuncMap`] assigns a dense `u32` id to
//! each monomorphized `Instance`, used as the `func` component of `AbstractLoc`.

extern crate rustc_middle;

use smallvec::SmallVec;

use rustc_middle::ty::Instance;

use super::constraint::Constraint;
use super::intern::Interner;
use super::loc::LocId;

/// Emit the inclusion constraints binding a call.
///
/// - For each positional pair, `callee_param ⊇ caller_arg` (skipping `None`
///   args, e.g. constants).
/// - `caller_dest ⊇ callee_return`.
pub fn bind_call_edges(
    callee_params: &[LocId],
    callee_return: LocId,
    caller_args: &[Option<LocId>],
    caller_dest: LocId,
) -> SmallVec<[Constraint; 4]> {
    let mut out = SmallVec::new();
    for (param, arg) in callee_params.iter().zip(caller_args.iter()) {
        if let Some(arg) = arg {
            out.push(Constraint::Copy {
                dst: *param,
                src: *arg,
            });
        }
    }
    out.push(Constraint::Copy {
        dst: caller_dest,
        src: callee_return,
    });
    out
}

/// Assigns dense `u32` ids to monomorphized instances (the `func` of a node).
#[derive(Default)]
pub struct FuncMap<'tcx> {
    inner: Interner<Instance<'tcx>>,
}

impl<'tcx> FuncMap<'tcx> {
    pub fn intern(&mut self, instance: Instance<'tcx>) -> u32 {
        self.inner.intern(instance)
    }

    pub fn instance(&self, id: u32) -> Instance<'tcx> {
        *self.inner.get(id)
    }

    /// Existing id for an instance, without interning a new one.
    pub fn get_id(&self, instance: &Instance<'tcx>) -> Option<u32> {
        self.inner.get_id(instance)
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binds_params_args_and_return() {
        // callee params _1, _2 = (10, 11); return _0 = 12.
        // caller args = [Some(20), None, Some(22)]; dest = 30.
        let params = [10u32, 11u32];
        let args = [Some(20u32), None, Some(22u32)];
        let edges = bind_call_edges(&params, 12, &args, 30);
        // _1 ⊇ 20 ; (_2 ⊇ None skipped) ; dest ⊇ return(12)
        assert!(edges.contains(&Constraint::Copy { dst: 10, src: 20 }));
        assert!(edges.contains(&Constraint::Copy { dst: 30, src: 12 }));
        // _2's arg is None, so no edge for it.
        assert!(!edges.iter().any(|c| matches!(c, Constraint::Copy { dst: 11, .. })));
        assert_eq!(edges.len(), 2);
    }

    #[test]
    fn extra_args_beyond_params_are_ignored() {
        let params = [10u32];
        let args = [Some(20u32), Some(21u32)];
        let edges = bind_call_edges(&params, 12, &args, 30);
        assert!(edges.contains(&Constraint::Copy { dst: 10, src: 20 }));
        assert!(edges.contains(&Constraint::Copy { dst: 30, src: 12 }));
        assert_eq!(edges.len(), 2);
    }
}
