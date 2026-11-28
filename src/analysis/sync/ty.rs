//! Whether two sites' types may denote the same synchronization object.
//!
//! Rules, in order:
//!
//! 1. **Same type.** After references (and raw pointers) are peeled, identical
//!    types are compatible. `Mutex<u64>` matches `Mutex<u64>`.
//! 2. **Same struct, compatible arguments.** The same ADT with pairwise
//!    compatible generic arguments is compatible. A lifetime-only difference
//!    is ignored; a const-generic difference is not.
//! 3. **Generic upper bound.** A type parameter is compatible with a concrete
//!    type only when one of its declared bounds is that type. Two parameters
//!    are compatible when they are the same parameter, or when both carry the
//!    same non-empty bound list (the bounds are the upper bound we can see).
//! 4. **Undecided means do not merge.** A parameter with no bound against a
//!    concrete type, two parameters with different or empty bounds, a
//!    projection we cannot normalize, or two different structs (including
//!    fields whose types differ, such as `Mutex<Chan<T>>` and
//!    `Mutex<Option<T>>`) are not compatible.

use rustc_middle::ty::{EarlyBinder, GenericArgKind, Ty, TyCtxt, TyKind, TypingEnv};

/// Structural type used by the predicate tests and by the partitioner when it
/// needs to talk about bounds. Production sites carry a real [`Ty`];
/// [`type_compatible`] is the same four rules on that `Ty` (bounds are empty
/// there, so a bare parameter does not merge with a concrete type).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeKey {
    Adt {
        path: String,
        args: Vec<TypeKey>,
    },
    /// `bounds` empty means the upper bound is not known.
    Param {
        name: String,
        bounds: Vec<TypeKey>,
    },
    Tuple(Vec<TypeKey>),
    Ref(Box<TypeKey>),
    /// A type the comparison cannot read. Never compatible, including with
    /// another `Unknown`.
    Unknown,
}

pub fn type_keys_compatible(left: &TypeKey, right: &TypeKey) -> bool {
    let left = peel_key(left);
    let right = peel_key(right);
    match (left, right) {
        (TypeKey::Unknown, _) | (_, TypeKey::Unknown) => false,
        (TypeKey::Adt { path: p1, args: a1 }, TypeKey::Adt { path: p2, args: a2 }) => {
            p1 == p2
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(x, y)| type_keys_compatible(x, y))
        }
        (TypeKey::Tuple(a), TypeKey::Tuple(b)) => {
            a.len() == b.len()
                && a.iter()
                    .zip(b.iter())
                    .all(|(x, y)| type_keys_compatible(x, y))
        }
        (
            TypeKey::Param {
                name: n1,
                bounds: b1,
            },
            TypeKey::Param {
                name: n2,
                bounds: b2,
            },
        ) => {
            if n1 == n2 && b1 == b2 {
                true
            } else {
                // Same non-empty upper bound: the parameters are bounded by
                // the same type, so a shared object of that bound is possible.
                !b1.is_empty() && b1 == b2
            }
        }
        (TypeKey::Param { bounds, .. }, other) | (other, TypeKey::Param { bounds, .. }) => bounds
            .iter()
            .any(|bound| type_keys_compatible(bound, other)),
        _ => false,
    }
}

fn peel_key(key: &TypeKey) -> &TypeKey {
    let mut key = key;
    while let TypeKey::Ref(inner) = key {
        key = inner;
    }
    key
}

/// [`type_keys_compatible`] on rustc types. Parameters carry no bound list
/// here, so rule 3 only fires for the key tests; a `Ty` parameter is
/// compatible with another type only when the two types are already equal
/// (rule 1) and is otherwise left unmerged (rule 4).
pub fn type_compatible<'tcx>(left: Ty<'tcx>, right: Ty<'tcx>) -> bool {
    let left = peel_ty(left);
    let right = peel_ty(right);
    if left == right {
        return true;
    }
    match (left.kind(), right.kind()) {
        (TyKind::Adt(def_a, args_a), TyKind::Adt(def_b, args_b)) if def_a.did() == def_b.did() => {
            generic_args_compatible(args_a, args_b)
        }
        (TyKind::Tuple(a), TyKind::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| type_compatible(x, y))
        }
        // Different structs, a parameter we cannot bound, a projection, or
        // anything else we cannot prove: do not merge.
        _ => false,
    }
}

fn generic_args_compatible<'tcx>(
    left: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    right: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
) -> bool {
    if left.len() != right.len() {
        return false;
    }
    left.iter()
        .zip(right.iter())
        .all(|(left, right)| match (left.kind(), right.kind()) {
            (GenericArgKind::Type(a), GenericArgKind::Type(b)) => type_compatible(a, b),
            (GenericArgKind::Lifetime(_), GenericArgKind::Lifetime(_)) => true,
            (GenericArgKind::Const(a), GenericArgKind::Const(b)) => a == b,
            _ => false,
        })
}

fn peel_ty<'tcx>(mut ty: Ty<'tcx>) -> Ty<'tcx> {
    loop {
        ty = match ty.kind() {
            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => *inner,
            _ => return ty,
        };
    }
}

pub(crate) fn normalized_local_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: rustc_middle::ty::Instance<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    local: rustc_middle::mir::Local,
) -> Ty<'tcx> {
    let typing_env = TypingEnv::post_analysis(tcx, instance.def_id());
    instance.instantiate_mir_and_normalize_erasing_regions(
        tcx,
        typing_env,
        EarlyBinder::bind(tcx, body.local_decls[local].ty),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn adt(path: &str, args: Vec<TypeKey>) -> TypeKey {
        TypeKey::Adt {
            path: path.to_string(),
            args,
        }
    }

    fn param(name: &str, bounds: Vec<TypeKey>) -> TypeKey {
        TypeKey::Param {
            name: name.to_string(),
            bounds,
        }
    }

    #[test]
    fn same_adt_is_compatible() {
        let ty = adt("std::sync::Mutex", vec![adt("u64", vec![])]);
        assert!(type_keys_compatible(&ty, &ty));
    }

    #[test]
    fn different_structs_are_not_compatible() {
        let chan = adt("flume::Chan", vec![adt("u64", vec![])]);
        let hook = adt("core::option::Option", vec![adt("u64", vec![])]);
        assert!(!type_keys_compatible(&chan, &hook));
    }

    #[test]
    fn reference_to_the_same_struct_is_compatible() {
        let inner = adt("std::sync::Mutex", vec![adt("u64", vec![])]);
        let borrowed = TypeKey::Ref(Box::new(inner.clone()));
        assert!(type_keys_compatible(&borrowed, &inner));
    }

    #[test]
    fn parameter_without_a_bound_does_not_merge_with_a_concrete_type() {
        let concrete = adt("std::sync::Mutex", vec![adt("u64", vec![])]);
        assert!(!type_keys_compatible(&param("T", vec![]), &concrete));
    }

    #[test]
    fn parameter_merges_with_its_upper_bound() {
        let bound = adt("std::sync::Mutex", vec![adt("u64", vec![])]);
        assert!(type_keys_compatible(
            &param("T", vec![bound.clone()]),
            &bound
        ));
    }

    #[test]
    fn parameters_with_the_same_upper_bound_are_compatible() {
        let bound = adt("std::sync::Mutex", vec![adt("u64", vec![])]);
        assert!(type_keys_compatible(
            &param("T", vec![bound.clone()]),
            &param("U", vec![bound])
        ));
    }

    #[test]
    fn parameters_with_empty_bounds_and_different_names_do_not_merge() {
        assert!(!type_keys_compatible(
            &param("T", vec![]),
            &param("U", vec![])
        ));
    }

    #[test]
    fn unknown_never_merges() {
        assert!(!type_keys_compatible(&TypeKey::Unknown, &TypeKey::Unknown));
        assert!(!type_keys_compatible(
            &TypeKey::Unknown,
            &adt("u64", vec![])
        ));
    }
}
