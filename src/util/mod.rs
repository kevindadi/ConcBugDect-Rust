pub mod mem_watcher;
pub mod mir_dot;

use std::io::Write;
use std::rc::Rc;

use rustc_hir::attrs::HasAttrs;
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

pub fn has_pn_attribute(tcx: TyCtxt<'_>, def_id: DefId, attr_stem: &str) -> bool {
    let name = rustc_span::symbol::Symbol::intern(attr_stem);
    def_id.get_attrs(&tcx).iter().any(|attr| attr.has_name(name))
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
