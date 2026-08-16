extern crate rustc_hir;
extern crate rustc_middle;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, List, Ty, TyCtxt, TyKind};

pub fn is_arc_or_rc_clone<'tcx>(
    def_id: DefId,
    substs: &List<GenericArg<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let fn_name = tcx.def_path_str(def_id);
    if fn_name != "std::clone::Clone::clone" {
        return false;
    }
    if let &[arg] = substs.as_ref() {
        let arg_ty_name = format!("{:?}", arg);
        if is_arc(&arg_ty_name) || is_rc(&arg_ty_name) {
            return true;
        }
    }
    false
}

#[inline]
pub fn is_arc(arg_ty_name: &str) -> bool {
    arg_ty_name.starts_with("std::sync::Arc<") || arg_ty_name.starts_with("alloc::sync::Arc<")
}

#[inline]
pub fn is_rc(arg_ty_name: &str) -> bool {
    arg_ty_name.starts_with("std::rc::Rc<") || arg_ty_name.starts_with("alloc::rc::Rc<")
}

#[inline]
pub fn is_box_ty_name(arg_ty_name: &str) -> bool {
    arg_ty_name.starts_with("std::boxed::Box<") || arg_ty_name.starts_with("alloc::boxed::Box<")
}

/// Whether `ty` is `Arc`/`Rc`/`Box` or a reference (including `&T`).
#[inline]
pub fn is_smart_pointer_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    if ty.is_ref() {
        return true;
    }
    if let TyKind::Adt(adt, _) = ty.kind() {
        let path = tcx.def_path_str(adt.did());
        return path.starts_with("std::sync::Arc")
            || path.starts_with("alloc::sync::Arc")
            || path.starts_with("std::rc::Rc")
            || path.starts_with("alloc::rc::Rc")
            || path.starts_with("std::boxed::Box")
            || path.starts_with("alloc::boxed::Box");
    }
    let name = format!("{:?}", ty);
    is_arc(&name) || is_rc(&name) || is_box_ty_name(&name)
}

/// Pure-string test: a `Box`/`Arc`/`Rc` inherent `::new`. Excludes lock
/// constructors (`Mutex::new`/`RwLock::new`) whose heap *is* the lock object
/// and is correctly produced by the conservative model.
#[inline]
pub fn is_box_arc_rc_new_path(path: &str) -> bool {
    if !path.ends_with("::new") {
        return false;
    }
    const PREFIXES: &[&str] = &[
        "std::boxed::Box::",
        "std::sync::Arc::",
        "std::rc::Rc::",
        "alloc::boxed::Box::",
        "alloc::sync::Arc::",
        "alloc::rc::Rc::",
    ];
    PREFIXES.iter().any(|p| path.starts_with(p))
}

/// `Box`/`Arc`/`Rc` constructor (`::new`). The boxed value must be stored into
/// the heap the smart pointer points to.
#[inline]
pub fn is_box_arc_rc_new(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    is_box_arc_rc_new_path(&tcx.def_path_str(def_id))
}

/// `Box::into_raw(b) -> *mut T`: leaks the box and returns a raw pointer to its
/// pointee. Modeled directly (`dest ⊇ arg`) so the raw pointer resolves to the
/// shared heap without descending into the std `into_raw_with_allocator` /
/// `deref_mut` / `as_mut_ptr` chain.
#[inline]
pub fn is_box_into_raw(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    let path = tcx.def_path_str(def_id);
    path.contains("boxed::Box") && path.ends_with("::into_raw")
}

/// Pure-string test for the deref method names.
#[inline]
pub fn is_deref_method_name(method: &str) -> bool {
    matches!(method, "deref" | "deref_mut")
}

/// `<Arc<T>/Rc<T> as Deref/DerefMut>::deref(&self) -> &T`. Modeled elsewhere as
/// `dest ⊇ *arg` so the result points at the smart pointer's pointee (the boxed
/// heap), not a fresh object. `Box` deref is built-in (a MIR `Deref`
/// projection) and intentionally excluded here.
#[inline]
pub fn is_arc_rc_deref<'tcx>(
    def_id: DefId,
    substs: &List<GenericArg<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let path = tcx.def_path_str(def_id);
    let method = path.rsplit("::").next().unwrap_or("");
    if !is_deref_method_name(method) {
        return false;
    }
    // Self type is the first generic arg of the (Deref) method instance.
    if let Some(arg0) = substs.iter().next() {
        let n = format!("{:?}", arg0);
        return is_arc(&n) || is_rc(&n);
    }
    false
}

#[inline]
pub fn is_ptr_read(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    tcx.def_path_str(def_id).starts_with("std::ptr::read::<")
}

#[inline]
pub fn is_index(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    tcx.def_path_str(def_id).ends_with("::index")
}

/// Lock-acquiring methods whose returned guard conceptually refers to the
/// receiver lock object (`Mutex::lock`/`try_lock`, `RwLock::read|write` and
/// their `try_*` forms, across std / parking_lot / spin). Async variants are
/// intentionally excluded — they belong to the async engine.
#[inline]
pub fn is_lock_acquire(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    let path = tcx.def_path_str(def_id);
    if path.contains("tokio")
        || path.contains("futures")
        || path.contains("loom")
        || path.contains("async")
    {
        return false;
    }
    let method = path.rsplit("::").next().unwrap_or("");
    let mutex_lock = path.contains("Mutex") && matches!(method, "lock" | "try_lock");
    let rwlock_lock =
        path.contains("RwLock") && matches!(method, "read" | "write" | "try_read" | "try_write");
    mutex_lock || rwlock_lock
}

/// `Result`/`Option` extractors commonly chained after `lock()`
/// (`unwrap`/`expect`/`ok`/...). Used only to trace a lock guard back to its
/// acquiring call's receiver; this is *not* a points-to model, so it does not
/// affect analysis soundness elsewhere.
#[inline]
pub fn is_wrapper_extract(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    let path = tcx.def_path_str(def_id);
    if !(path.contains("Result") || path.contains("Option")) {
        return false;
    }
    let method = path.rsplit("::").next().unwrap_or("");
    matches!(
        method,
        "unwrap"
            | "expect"
            | "ok"
            | "unwrap_or"
            | "unwrap_or_else"
            | "unwrap_or_default"
            | "unwrap_unchecked"
    )
}

/// `Condvar::wait`-family methods (`wait`/`wait_while`/`wait_timeout`/...).
/// The guard passed in is released and then re-acquired, so the returned guard
/// protects the *same* mutex as the argument guard.
#[inline]
pub fn is_condvar_wait(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    let path = tcx.def_path_str(def_id);
    let method = path.rsplit("::").next().unwrap_or("");
    path.contains("Condvar") && method.starts_with("wait")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_path_matches_box_arc_rc_only() {
        assert!(is_box_arc_rc_new_path("std::sync::Arc::<T>::new"));
        assert!(is_box_arc_rc_new_path("std::rc::Rc::<T>::new"));
        assert!(is_box_arc_rc_new_path("std::boxed::Box::<T>::new"));
        assert!(is_box_arc_rc_new_path("alloc::sync::Arc::<T>::new"));
        // Must NOT match lock constructors (their heap == the lock object, handled by UnknownModel).
        assert!(!is_box_arc_rc_new_path("std::sync::Mutex::<T>::new"));
        assert!(!is_box_arc_rc_new_path("std::sync::RwLock::<T>::new"));
        assert!(!is_box_arc_rc_new_path("my_crate::Foo::new"));
    }

    #[test]
    fn deref_method_name_detection() {
        assert!(is_deref_method_name("deref"));
        assert!(is_deref_method_name("deref_mut"));
        assert!(!is_deref_method_name("clone"));
        assert!(!is_deref_method_name("lock"));
    }
}
