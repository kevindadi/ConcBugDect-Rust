//! Type-driven enumeration of an aggregate's leaf field paths, used to expand
//! by-value struct / tuple / closure copies into field-wise copies so field
//! contents (e.g. closure upvars) flow across assignments and call binds.

extern crate rustc_middle;

use rustc_middle::ty::{Ty, TyCtxt, TypingEnv};

use super::loc::{FieldPath, LocArena, ProjElem};

/// Maximum nesting depth explored when flattening an aggregate value into leaf
/// field paths. Mirrors the spirit of `FIELD_DEPTH_CAP`.
const FLATTEN_DEPTH: usize = 6;

/// Append to `out` the interned field paths of every immediate-or-nested
/// *aggregate leaf* of `ty`. A "leaf" is a non-aggregate field (pointer,
/// scalar, reference) or an aggregate reached at `FLATTEN_DEPTH`. Arrays/slices
/// contribute a single `Index` element (index-merged). Enums contribute their
/// fields ignoring the variant tag (sound merge). The empty path is included
/// when `ty` itself is a leaf, so callers can always fall back to a base copy.
pub fn leaf_field_paths<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    arena: &mut LocArena,
) -> Vec<FieldPath> {
    let mut out = Vec::new();
    let empty = arena.empty_path();
    flatten(tcx, typing_env, ty, empty, 0, arena, &mut out);
    if out.is_empty() {
        out.push(empty);
    }
    out
}

fn flatten<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    path: FieldPath,
    depth: usize,
    arena: &mut LocArena,
    out: &mut Vec<FieldPath>,
) {
    use rustc_middle::ty::TyKind;
    if depth >= FLATTEN_DEPTH {
        out.push(path);
        return;
    }
    match ty.kind() {
        TyKind::Tuple(elems) => {
            for (i, e) in elems.iter().enumerate() {
                let p = arena.extend_path(path, ProjElem::Field(i as u32));
                flatten(tcx, env, e, p, depth + 1, arena, out);
            }
        }
        TyKind::Adt(def, args) if def.is_struct() => {
            let variant = def.non_enum_variant();
            for (i, f) in variant.fields.iter().enumerate() {
                let fty = tcx.normalize_erasing_regions(env, f.ty(tcx, args));
                let p = arena.extend_path(path, ProjElem::Field(i as u32));
                flatten(tcx, env, fty, p, depth + 1, arena, out);
            }
        }
        TyKind::Closure(_, args) => {
            for (i, uty) in args.as_closure().upvar_tys().iter().enumerate() {
                let p = arena.extend_path(path, ProjElem::Field(i as u32));
                flatten(tcx, env, uty, p, depth + 1, arena, out);
            }
        }
        TyKind::Array(elem, _) | TyKind::Slice(elem) => {
            let p = arena.extend_path(path, ProjElem::Index);
            flatten(tcx, env, *elem, p, depth + 1, arena, out);
        }
        // Enums, unions, and everything else are treated as a single leaf
        // (sound: a base copy over-approximates by merging the fields).
        _ => out.push(path),
    }
}
