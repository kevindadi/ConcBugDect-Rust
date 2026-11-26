pub mod mem_watcher;
pub mod mir_dot;

use std::io::Write;
use std::rc::Rc;

use rustc_attr_ir::HasAttrs;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;
use rustc_middle::ty::TyCtxt;

#[macro_export]
macro_rules! unrecoverable {
    ($fmt:expr) => (
        panic!(concat!("unrecoverable: ", stringify!($fmt)));
    );
    ($fmt:expr, $($arg:tt)+) => (
        panic!(concat!("unrecoverable: ", stringify!($fmt)), $($arg)+)
    );
}

fn crate_name(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    tcx.crate_name(def_id.krate).as_str().to_string()
}

pub fn format_name(def_id: DefId) -> String {
    let tmp1 = format!("{def_id:?}");
    let tmp2: &str = tmp1.split("~ ").collect::<Vec<&str>>()[1];
    let tmp3 = tmp2.replace(')', "");
    let lhs = tmp3.split('[').collect::<Vec<&str>>()[0];
    let rhs = tmp3.split(']').collect::<Vec<&str>>()[1];
    format!("{lhs}{rhs}").to_string()
}

pub fn def_id_as_qualified_name_str(tcx: TyCtxt<'_>, def_id: DefId) -> Rc<str> {
    let mut name = format!("/{}/", crate_name(tcx, def_id));
    name.push_str(&tcx.def_path_str(def_id));
    if tcx.def_kind(def_id).is_fn_like() {
        let fn_ty = tcx.type_of(def_id).skip_binder();
        name.push('(');
        let fn_sig = if fn_ty.is_fn() {
            fn_ty.fn_sig(tcx).skip_binder()
        } else if let ty::Closure(_, args) = fn_ty.kind() {
            args.as_closure().sig().skip_binder()
        } else {
            unreachable!()
        };
        let mut first = true;
        for param_ty in fn_sig.inputs() {
            if first {
                first = false;
            } else {
                name.push(',')
            }
            name.push_str(&format!("{param_ty:?}"));
        }
        name.push_str(")->");
        name.push_str(&format!("{:?}", fn_sig.output()));
    }
    Rc::from(name.as_str())
}

/// Attribute names accepted for `stem`.
///
/// `stem` may be `pn_condvar_wait`, `spn_condvar_wait`, or `condvar_wait`.
/// The first name is the `spn_` form and the second is the `pn_` form.
pub fn spn_attribute_names(stem: &str) -> [String; 2] {
    let suffix = stem
        .strip_prefix("spn_")
        .or_else(|| stem.strip_prefix("pn_"))
        .unwrap_or(stem);
    [format!("spn_{suffix}"), format!("pn_{suffix}")]
}

/// Whether `present` carries either spelling of `stem`.
pub fn attribute_matches(present: &[&str], stem: &str) -> bool {
    let names = spn_attribute_names(stem);
    present
        .iter()
        .any(|attr| *attr == names[0] || *attr == names[1])
}

pub fn has_spn_attribute(tcx: TyCtxt<'_>, def_id: DefId, attr_stem: &str) -> bool {
    let names = spn_attribute_names(attr_stem);
    let symbols = [
        rustc_span::symbol::Symbol::intern(&names[0]),
        rustc_span::symbol::Symbol::intern(&names[1]),
    ];
    def_id
        .get_attrs(&tcx)
        .iter()
        .any(|attr| symbols.iter().any(|name| attr.has_name(*name)))
}

#[cfg(test)]
mod tests {
    use super::attribute_matches;

    const STEMS: &[&str] = &[
        "pn_condvar",
        "pn_condvar_wait",
        "pn_condvar_notify",
        "pn_spawn",
        "pn_join",
        "pn_scope_spawn",
        "pn_scope_join",
        "pn_rayon_join",
        "pn_mutex_guard",
        "pn_rwlock_read_guard",
        "pn_rwlock_write_guard",
    ];

    #[test]
    fn pn_and_spn_attribute_spellings_match_the_same_queries() {
        for stem in STEMS {
            let spn = stem.replacen("pn_", "spn_", 1);
            let marked_pn = [*stem];
            let marked_spn = [spn.as_str()];
            for query in [*stem, spn.as_str()] {
                assert_eq!(
                    attribute_matches(&marked_pn, query),
                    attribute_matches(&marked_spn, query),
                    "{stem} via {query}"
                );
                assert!(attribute_matches(&marked_pn, query));
                assert!(attribute_matches(&marked_spn, query));
            }
            assert!(!attribute_matches(&["pn_other"], stem));
        }
    }
}

/// Extracts the generic arguments of an `FnDef` type.
///
/// `ty::FnDef` stores its arguments inside a `Binder` now; the regions are
/// always erased when a function definition is used as a value, so
/// instantiating the bound regions with `'erased` recovers the arguments
/// without panicking (unlike `no_bound_vars`).
pub fn fn_def_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    args: ty::Binder<'tcx, ty::GenericArgsRef<'tcx>>,
) -> ty::GenericArgsRef<'tcx> {
    tcx.instantiate_bound_regions_with_erased(args)
}

pub fn pretty_print_mir(tcx: TyCtxt<'_>, def_id: DefId) {
    if !matches!(
        tcx.def_kind(def_id),
        rustc_hir::def::DefKind::Struct | rustc_hir::def::DefKind::Variant
    ) {
        let mut stdout = std::io::stdout();
        stdout.write_fmt(format_args!("{:?}", def_id)).unwrap();
        rustc_middle::mir::write_mir_pretty(tcx, &mut stdout).unwrap();
        let _ = stdout.flush();
    }
}
