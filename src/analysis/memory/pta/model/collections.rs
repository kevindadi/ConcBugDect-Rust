//! Call models for `Vec` and slice iterators.
//! They give the buffer an abstract identity the raw-pointer MIR would drop.
//! They do not model locks themselves.

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, TyCtxt};

use super::{CallModel, CallNodes};
use crate::analysis::memory::ownership;
use crate::analysis::memory::pta::constraint::{Constraint, ConstraintSet};
use crate::analysis::memory::pta::loc::{LocArena, ProjElem};

/// Field path from the *container object* of a slice reference to its element
/// slots. We identify the slice a `Vec` derefs to with the `Vec`'s own
/// container object: the element at a constant index `i` is then the stable
/// abstract slot `container·ConstIndex(i)`, which keeps distinct indices
/// distinct without having to model the raw data pointer.
const ITER_PTR_PATH: [ProjElem; 2] = [ProjElem::Field(0), ProjElem::Field(0)];

fn intern_elems(
    arena: &mut LocArena,
    elems: &[ProjElem],
) -> crate::analysis::memory::pta::loc::FieldPath {
    let mut p = arena.empty_path();
    for e in elems {
        p = arena.extend_path(p, *e);
    }
    p
}

/// `<Vec<T> as Deref>::deref(&self) -> &[T]`: the resulting slice reference
/// denotes the Vec's element container. The analysis has no object for the
/// raw data pointer (allocator/raw-pointer plumbing carries no identity), so
/// the container object itself is used as the element owner: `get(i)` then
/// yields `container·ConstIndex(i)`, keeping indices distinct. This is an
/// over-approximation of the slice's pointee (it additionally aliases the
/// container), never a loss of a real element.
pub struct VecDerefModel;

impl CallModel for VecDerefModel {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool {
        n_args == 1 && ownership::is_vec_deref(def_id, substs, tcx)
    }

    fn emit(&self, nodes: &CallNodes, _arena: &mut LocArena, out: &mut ConstraintSet) {
        let Some(Some(arg)) = nodes.args.first().copied() else {
            return;
        };
        out.add(Constraint::Copy {
            dst: nodes.dest,
            src: arg,
        });
    }
}

/// `<[T]>::iter(&self) -> slice::Iter<'_, T>`: the iterator's data pointer
/// refers to the slice's element (merged `Index` element: iteration may start
/// anywhere inside the buffer).
pub struct SliceIterModel;

impl CallModel for SliceIterModel {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        _substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool {
        n_args == 1 && ownership::is_slice_iter(def_id, tcx)
    }

    fn emit(&self, nodes: &CallNodes, arena: &mut LocArena, out: &mut ConstraintSet) {
        let Some(Some(slice)) = nodes.args.first().copied() else {
            return;
        };
        let Some(temp) = nodes.temps.first().copied() else {
            return;
        };
        // temp = &buffer[Index] (a reference to an element slot).
        let elem_path = intern_elems(arena, &[ProjElem::Index]);
        out.add(Constraint::Offset {
            dst: temp,
            src: slice,
            suffix: elem_path,
        });
        // Iterator.ptr.pointer now points at that element.
        let iter_ptr_path = intern_elems(arena, &ITER_PTR_PATH);
        if let Some(slot) = arena.project(nodes.dest, iter_ptr_path) {
            out.add(Constraint::Copy {
                dst: slot,
                src: temp,
            });
        }
    }
}

/// `<slice::Iter as Iterator>::find(&mut self, predicate) -> Option<&T>`.
///
/// `find` is a generic std function whose loop calls `next` through a trait
/// call; the engine cannot materialize those instances, so the element never
/// flowed out and the returned option's payload was empty. The model routes
/// the iterator's element reference (the same slot [`SliceIterModel`] wrote)
/// into the option payload.
///
/// The chosen element is *some* element of the buffer: which one is decided
/// by the predicate, which this analysis does not evaluate, so the model
/// keeps the merged `Index` element (an over-approximation of the real
/// choice, never a loss of a possible element).
pub struct SliceIterFindModel;

impl CallModel for SliceIterFindModel {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool {
        n_args == 2 && ownership::is_slice_iter_find(def_id, substs, tcx)
    }

    fn emit(&self, nodes: &CallNodes, arena: &mut LocArena, out: &mut ConstraintSet) {
        // `find` takes `&mut self`: arg 0 points at the iterator value.
        let Some(Some(iter_ref)) = nodes.args.first().copied() else {
            return;
        };
        let Some(temp) = nodes.temps.first().copied() else {
            return;
        };
        // temp = *(*iter_ref)·0·0 — the element reference slot.
        let iter_ptr_path = intern_elems(arena, &ITER_PTR_PATH);
        out.add(Constraint::Offset {
            dst: temp,
            src: iter_ref,
            suffix: iter_ptr_path,
        });
        // Option payload (variant field 0) = the element reference value.
        let payload_path = intern_elems(arena, &[ProjElem::Field(0)]);
        if let Some(payload) = arena.project(nodes.dest, payload_path) {
            match nodes.predicate {
                // The closure predicate `element.field == value` is
                // evaluable. The solver tags the matching element with the
                // predicate identity, splitting it from the elements selected
                // by other values. When the captured value turns out dynamic
                // the solver keeps the merged element (sound).
                Some(pred) => {
                    out.add(Constraint::FindElement {
                        dst: payload,
                        src: temp,
                        field: pred.element_field,
                        value: pred.value,
                    });
                }
                // No predicate certificate: merged element (conservative).
                None => {
                    out.add(Constraint::Load {
                        dst: payload,
                        src: temp,
                    });
                }
            }
        }
    }
}

/// `Index::index(&self, index) -> &T` (the `[]` operator): the result points
/// at one element of the container. With a proven-constant index the element
/// is `ConstIndex(v)`; a dynamic index stays the merged `Index`.
pub struct IndexElemModel;

impl CallModel for IndexElemModel {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        _substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool {
        n_args == 2 && ownership::is_index(def_id, tcx)
    }

    fn emit(&self, nodes: &CallNodes, arena: &mut LocArena, out: &mut ConstraintSet) {
        let Some(Some(container)) = nodes.args.first().copied() else {
            return;
        };
        let elem = match nodes.arg_consts.get(1).copied().flatten() {
            Some(v) => ProjElem::ConstIndex(v),
            None => ProjElem::Index,
        };
        let suffix = intern_elems(arena, &[elem]);
        out.add(Constraint::Offset {
            dst: nodes.dest,
            src: container,
            suffix,
        });
    }
}

/// `<[T]>::get(&self, index) -> Option<&T>`: the returned option's payload
/// refers to one element of the slice (constant-index narrowed like
/// [`IndexElemModel`]).
pub struct SliceGetModel;

impl CallModel for SliceGetModel {
    fn matches<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        _substs: &'tcx List<GenericArg<'tcx>>,
        n_args: usize,
    ) -> bool {
        n_args == 2 && ownership::is_slice_get(def_id, tcx)
    }

    fn emit(&self, nodes: &CallNodes, arena: &mut LocArena, out: &mut ConstraintSet) {
        let Some(Some(slice)) = nodes.args.first().copied() else {
            return;
        };
        let Some(temp) = nodes.temps.first().copied() else {
            return;
        };
        let elem = match nodes.arg_consts.get(1).copied().flatten() {
            Some(v) => ProjElem::ConstIndex(v),
            None => ProjElem::Index,
        };
        let elem_path = intern_elems(arena, &[elem]);
        out.add(Constraint::Offset {
            dst: temp,
            src: slice,
            suffix: elem_path,
        });
        // `Option`/`Result` payload: the payload lives at the variant's field 0
        // (the variant tag is merged by the engine, matching the
        // `Downcast`-dropping place projection used at payload reads).
        let payload_path = intern_elems(arena, &[ProjElem::Field(0)]);
        if let Some(slot) = arena.project(nodes.dest, payload_path) {
            out.add(Constraint::Copy {
                dst: slot,
                src: temp,
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
    fn vec_deref_denotes_the_container() {
        let nodes = CallNodes {
            dest: 7,
            args: smallvec![Some(3u32)],
            fresh_heap: 9,
            temps: smallvec![11u32],
            arg_consts: smallvec![None],
            predicate: None,
        };
        let mut arena = LocArena::default();
        let mut cs = ConstraintSet::default();
        VecDerefModel.emit(&nodes, &mut arena, &mut cs);
        assert!(cs.iter().any(|c| *c == Constraint::Copy { dst: 7, src: 3 }));
    }

    #[test]
    fn slice_iter_points_iterator_at_buffer_element() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        // Model callers always pass an interned destination node.
        let dest = arena.var(0, 0u32, empty);
        let nodes = CallNodes {
            dest,
            args: smallvec![Some(2u32)],
            fresh_heap: 9,
            temps: smallvec![13u32],
            arg_consts: smallvec![None],
            predicate: None,
        };
        let mut cs = ConstraintSet::default();
        SliceIterModel.emit(&nodes, &mut arena, &mut cs);
        let elem = intern_elems(&mut arena, &[ProjElem::Index]);
        assert!(cs.iter().any(|c| *c
            == Constraint::Offset {
                dst: 13,
                src: 2,
                suffix: elem
            }));
        let ptr_path = intern_elems(&mut arena, &ITER_PTR_PATH);
        let ptr_slot = arena.project(dest, ptr_path).unwrap();
        assert!(cs.iter().any(|c| *c
            == Constraint::Copy {
                dst: ptr_slot,
                src: 13
            }));
    }

    #[test]
    fn slice_iter_find_loads_the_element_into_the_option_payload() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let dest = arena.var(0, 0u32, empty);
        let nodes = CallNodes {
            dest,
            // `find(&mut self, predicate)`: arg 0 is the `&mut Iter`.
            args: smallvec![Some(2u32), None],
            fresh_heap: 9,
            temps: smallvec![19u32],
            arg_consts: smallvec![None, None],
            predicate: None,
        };
        let mut cs = ConstraintSet::default();
        SliceIterFindModel.emit(&nodes, &mut arena, &mut cs);
        let ptr_path = intern_elems(&mut arena, &ITER_PTR_PATH);
        // temp = *(*iter_ref).ptr.pointer — the element-reference slot.
        assert!(cs.iter().any(|c| *c
            == Constraint::Offset {
                dst: 19,
                src: 2,
                suffix: ptr_path
            }));
        // The option payload reads that slot (variant field 0).
        let payload_path = intern_elems(&mut arena, &[ProjElem::Field(0)]);
        let payload = arena.project(dest, payload_path).unwrap();
        assert!(cs.iter().any(|c| *c
            == Constraint::Load {
                dst: payload,
                src: 19
            }));
    }

    #[test]
    fn slice_iter_find_emits_a_predicate_split_when_certified() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let dest = arena.var(0, 0u32, empty);
        let field = intern_elems(&mut arena, &[ProjElem::Deref, ProjElem::Field(0)]);
        let nodes = CallNodes {
            dest,
            args: smallvec![Some(2u32), None],
            fresh_heap: 9,
            temps: smallvec![19u32],
            arg_consts: smallvec![None, None],
            predicate: Some(crate::analysis::memory::pta::model::FindPredicate {
                element_field: field,
                value: crate::analysis::memory::pta::constraint::FindValue::Literal(3),
            }),
        };
        let mut cs = ConstraintSet::default();
        SliceIterFindModel.emit(&nodes, &mut arena, &mut cs);
        let payload_path = intern_elems(&mut arena, &[ProjElem::Field(0)]);
        let payload = arena.project(dest, payload_path).unwrap();
        assert!(cs.iter().any(|c| *c
            == Constraint::FindElement {
                dst: payload,
                src: 19,
                field,
                value: crate::analysis::memory::pta::constraint::FindValue::Literal(3),
            }));
        // The unevaluable-predicate fallback is the solver's job; the model
        // must not *also* emit the merged load (the FindElement constraint is
        // exactly a predicate-certified Load).
        assert!(!cs.iter().any(|c| *c
            == Constraint::Load {
                dst: payload,
                src: 19
            }));
    }

    #[test]
    fn slice_get_separates_constant_indices() {
        let mut arena = LocArena::default();
        let empty = arena.empty_path();
        let dest = arena.var(0, 0u32, empty);
        let nodes = CallNodes {
            dest,
            args: smallvec![Some(2u32), None],
            fresh_heap: 9,
            temps: smallvec![17u32],
            arg_consts: smallvec![None, Some(1u64)],
            predicate: None,
        };
        let mut cs = ConstraintSet::default();
        SliceGetModel.emit(&nodes, &mut arena, &mut cs);
        let elem0 = intern_elems(&mut arena, &[ProjElem::ConstIndex(0)]);
        let elem1 = intern_elems(&mut arena, &[ProjElem::ConstIndex(1)]);
        // The emitted offset must use the proven index 1, and not be the
        // merged dynamic `Index` element.
        assert!(cs.iter().any(|c| *c
            == Constraint::Offset {
                dst: 17,
                src: 2,
                suffix: elem1
            }));
        assert!(!cs.iter().any(|c| *c
            == Constraint::Offset {
                dst: 17,
                src: 2,
                suffix: elem0
            }));
    }
}
