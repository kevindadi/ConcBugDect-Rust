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

/// `<Vec<T> as Deref>::deref(&self) -> &[T]` / `DerefMut::deref_mut`. The
/// callee at the call site is the *trait* method (`std::ops::Deref::deref`),
/// so the `Vec` receiver is identified through the instance's `Self` generic
/// argument, exactly like [`is_arc_rc_deref`]. Modeled structurally (see
/// `pta::model::collections`).
#[inline]
pub fn is_vec_deref<'tcx>(
    def_id: DefId,
    substs: &List<GenericArg<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let path = tcx.def_path_str(def_id);
    let method = path.rsplit("::").next().unwrap_or("");
    if !is_deref_method_name(method) {
        return false;
    }
    if let Some(arg0) = substs.iter().next() {
        let n = format!("{:?}", arg0);
        return n.starts_with("std::vec::Vec<") || n.starts_with("alloc::vec::Vec<");
    }
    false
}

/// `<[T]>::iter(&self) -> slice::Iter<'_, T>` (the inherent slice method, not
/// `IntoIterator::into_iter`). Modeled so the iterator's data pointer refers
/// to an element of the slice buffer.
#[inline]
pub fn is_slice_iter(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    let path = tcx.def_path_str(def_id);
    path.starts_with("core::slice::") && path.ends_with("::iter")
}

/// `<slice::Iter<'_, T> as Iterator>::find(&mut self, predicate)`.
///
/// The callee at the call site is the *trait* method
/// (`<std::slice::Iter<'_, T> as std::iter::Iterator>::find`), so the
/// iterator type is read from the instance's `Self` generic argument, like
/// [`is_vec_deref`].
#[inline]
pub fn is_slice_iter_find<'tcx>(
    def_id: DefId,
    substs: &List<GenericArg<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    if !tcx.def_path_str(def_id).ends_with("Iterator::find") {
        return false;
    }
    match substs.iter().next() {
        Some(arg) => {
            let n = format!("{:?}", arg);
            // `Debug` for the iterator type prints the short module path
            // (`std::slice::Iter<...>`), not `slice::iter::Iter`.
            n.starts_with("core::slice::Iter<") || n.starts_with("std::slice::Iter<")
        }
        None => false,
    }
}

/// `<[T]>::get(&self, index) -> Option<&T>` / `get_mut`.
#[inline]
pub fn is_slice_get(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    let path = tcx.def_path_str(def_id);
    path.starts_with("core::slice::") && (path.ends_with("::get") || path.ends_with("::get_mut"))
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

/// Weight/kind class of a guard-less custom lock operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CustomLockMode {
    /// Mutually exclusive: acquire/release weight 1, capacity 1.
    Mutex,
    /// Shared read side of a reader-writer lock: weight 1.
    RwLockRead,
    /// Exclusive write side: weight `RWLOCK_CAPACITY`.
    RwLockWrite,
}

/// Direction of a guard-less custom lock operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CustomLockOp {
    Acquire,
    Release,
}

/// A guard-less custom lock method (`RawMutex::lock`, `RawRwLock::unlock_shared`,
/// `WordLock::lock`, …) recognized by [`custom_lock_method`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CustomLockMethod {
    pub mode: CustomLockMode,
    pub op: CustomLockOp,
}

/// Recognize a *function definition* as a guard-less custom lock operation.
///
/// This is the counterpart of [`is_lock_acquire`]: lock APIs that
/// return no guard (parking_lot's `RawMutex`/`RawRwLock` traits, the
/// `parking_lot_core::WordLock`), or user types listed in
/// `custom_lock_types`, carry the resource operation *inside* the method
/// body instead of at the call site. Recognition matches the configured
/// substrings against three descriptors so all MIR shapes are covered:
///
/// 1. the method's def path (`parking_lot_core::word_lock::WordLock::lock`),
/// 2. its trait path (`<.. as lock_api::RawMutex>::lock` — the trait impl
///    item's own def path contains only `{impl#N}`, so the trait name has to
///    come from `trait_of_item`), and
/// 3. its signature (`fn(&parking_lot::raw_mutex::RawMutex)`), which names
///    the inherent impl's self type.
///
/// The method name then selects acquire/release and the mutex / read / write
/// weight class. `bump_*`, `upgrade` and `downgrade` are intentionally not
/// modelled: they convert a held lock instead of taking or returning one.
#[inline]
pub fn custom_lock_method(
    def_id: DefId,
    tcx: TyCtxt<'_>,
    patterns: &[String],
) -> Option<CustomLockMethod> {
    if patterns.is_empty() {
        return None;
    }
    let path = tcx.def_path_str(def_id);
    if path.contains("tokio")
        || path.contains("futures")
        || path.contains("loom")
        || path.contains("async")
    {
        return None;
    }
    // A trait impl item's own def path is `crate::module::{impl#N}::method`,
    // which does not name the implemented trait; the trait name is the part
    // that identifies `<T as lock_api::RawMutex>::lock`. Resolve it through
    // the impl's trait reference (trait items themselves keep their path).
    let container = tcx.parent(def_id);
    let trait_path = match tcx.def_kind(container) {
        rustc_hir::def::DefKind::Trait | rustc_hir::def::DefKind::TraitAlias => {
            tcx.def_path_str(container)
        }
        rustc_hir::def::DefKind::Impl { .. } => tcx
            .impl_opt_trait_id(container)
            .map(|trait_id| tcx.def_path_str(trait_id))
            .unwrap_or_default(),
        _ => String::new(),
    };
    let signature = format!("{:?}", tcx.type_of(def_id).skip_binder());
    if !custom_lock_descriptors_match(&path, &trait_path, &signature, patterns) {
        return None;
    }
    let method = path.rsplit("::").next().unwrap_or("");
    let descriptors = format!("{path} {trait_path} {signature}");
    classify_custom_lock_method(method, descriptors.contains("RwLock"))
}

/// Whether any configured pattern names the function through its def path,
/// its implemented-trait path, or its signature.
#[inline]
fn custom_lock_descriptors_match(
    path: &str,
    trait_path: &str,
    signature: &str,
    patterns: &[String],
) -> bool {
    patterns.iter().any(|pattern| {
        path.contains(pattern.as_str())
            || trait_path.contains(pattern.as_str())
            || signature.contains(pattern.as_str())
    })
}

/// Method-name table for guard-less custom locks: `(name, rwlock) -> (mode, op)`.
///
/// Names that merely delegate to another recognized method
/// (`lock_shared_fair`, `unlock_shared_fair`, `unlock_fair`, recursive and
/// timed wrappers that forward to a plain acquire) stay in the table because
/// the *caller* of a wrapper still needs the operation to be modelled; the
/// translation layer drops the wrapper itself when its body delegates, so the
/// operation is counted once, at the innermost call.
#[inline]
fn classify_custom_lock_method(method: &str, rwlock: bool) -> Option<CustomLockMethod> {
    use CustomLockMode::{Mutex, RwLockRead, RwLockWrite};
    use CustomLockOp::{Acquire, Release};
    let (mode, op) = match method {
        // Mutex names.
        "lock" | "try_lock" | "try_lock_for" | "try_lock_until" => {
            if rwlock {
                (RwLockWrite, Acquire)
            } else {
                (Mutex, Acquire)
            }
        }
        "unlock" | "unlock_fair" => {
            if rwlock {
                (RwLockWrite, Release)
            } else {
                (Mutex, Release)
            }
        }
        // Reader-writer names.
        "read"
        | "try_read"
        | "lock_shared"
        | "try_lock_shared"
        | "lock_shared_recursive"
        | "try_lock_shared_recursive"
        | "try_lock_shared_recursive_for"
        | "try_lock_shared_recursive_until"
        | "try_lock_shared_for"
        | "try_lock_shared_until" => (RwLockRead, Acquire),
        "unlock_shared" | "unlock_shared_fair" => (RwLockRead, Release),
        "write"
        | "try_write"
        | "lock_exclusive"
        | "try_lock_exclusive"
        | "try_lock_exclusive_for"
        | "try_lock_exclusive_until" => (RwLockWrite, Acquire),
        "unlock_exclusive" | "unlock_exclusive_fair" => (RwLockWrite, Release),
        // Upgradable is an independent mode in parking_lot (at most one
        // holder, coexists with readers). The net has no upgradable place, so
        // it is modelled on the read side: that over-approximates the
        // interleavings (never falsely excludes a reader) and never claims an
        // exclusion the primitive does not have.
        "lock_upgradable"
        | "try_lock_upgradable"
        | "try_lock_upgradable_for"
        | "try_lock_upgradable_until" => (RwLockRead, Acquire),
        "unlock_upgradable" | "unlock_upgradable_fair" => (RwLockRead, Release),
        // `bump_*`, `upgrade` and `downgrade` convert a held lock instead of
        // taking or returning one; `is_locked*` observes it.
        _ => return None,
    };
    Some(CustomLockMethod { mode, op })
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

    #[test]
    fn custom_lock_method_names_select_weight_class() {
        use CustomLockMode::{Mutex, RwLockRead, RwLockWrite};
        use CustomLockOp::{Acquire, Release};
        let m = |mode, op| Some(CustomLockMethod { mode, op });
        // Mutex: lock/try_lock/unlock, including the timed family.
        assert_eq!(
            classify_custom_lock_method("lock", false),
            m(Mutex, Acquire)
        );
        assert_eq!(
            classify_custom_lock_method("try_lock", false),
            m(Mutex, Acquire)
        );
        assert_eq!(
            classify_custom_lock_method("try_lock_for", false),
            m(Mutex, Acquire)
        );
        assert_eq!(
            classify_custom_lock_method("unlock", false),
            m(Mutex, Release)
        );
        assert_eq!(
            classify_custom_lock_method("unlock_fair", false),
            m(Mutex, Release)
        );
        // RwLock read side consumes one token, write side the whole capacity.
        assert_eq!(
            classify_custom_lock_method("lock_shared", true),
            m(RwLockRead, Acquire)
        );
        assert_eq!(
            classify_custom_lock_method("unlock_shared_fair", true),
            m(RwLockRead, Release)
        );
        assert_eq!(
            classify_custom_lock_method("lock_exclusive", true),
            m(RwLockWrite, Acquire)
        );
        assert_eq!(
            classify_custom_lock_method("unlock_exclusive_fair", true),
            m(RwLockWrite, Release)
        );
        assert_eq!(
            classify_custom_lock_method("read", true),
            m(RwLockRead, Acquire)
        );
        assert_eq!(
            classify_custom_lock_method("write", true),
            m(RwLockWrite, Acquire)
        );
        // Upgradable shares the read place (no upgradable place in the net).
        assert_eq!(
            classify_custom_lock_method("lock_upgradable", true),
            m(RwLockRead, Acquire)
        );
        assert_eq!(
            classify_custom_lock_method("unlock_upgradable_fair", true),
            m(RwLockRead, Release)
        );
        // Conversion / observation methods are not acquisitions or releases.
        for name in [
            "bump_slow",
            "bump_shared",
            "bump_exclusive",
            "bump_upgradable",
            "upgrade",
            "try_upgrade",
            "downgrade",
            "is_locked",
            "is_locked_exclusive",
            "lock_slow",
            "unlock_shared_slow",
            "lock_common",
            "lock_shared_slow",
            "new",
        ] {
            assert_eq!(classify_custom_lock_method(name, true), None, "{name}");
        }
    }

    #[test]
    fn custom_lock_patterns_match_paths_traits_and_signatures() {
        let patterns = vec!["RawMutex".to_string(), "WordLock".to_string()];
        // Def path hit (WordLock's inherent method).
        assert!(custom_lock_descriptors_match(
            "parking_lot_core::word_lock::WordLock::lock",
            "",
            "",
            &patterns
        ));
        // Trait path hit: the impl item's path only carries `{impl#0}`; the
        // trait is `<T as lock_api::RawMutex>` (`lock_api::raw_mutex::RawMutex`).
        assert!(custom_lock_descriptors_match(
            "parking_lot::raw_mutex::{impl#0}::lock",
            "lock_api::raw_mutex::RawMutex",
            "fn(&parking_lot::raw_mutex::RawMutex)",
            &patterns
        ));
        // Signature hit: an inherent helper whose path and trait do not name
        // the lock type still mentions `&RawMutex` in its self type.
        assert!(custom_lock_descriptors_match(
            "some_crate::ext::{impl#2}::lock",
            "",
            "fn(&some_crate::ext::RawMutex)",
            &patterns
        ));
        assert!(!custom_lock_descriptors_match(
            "std::sync::Mutex::lock",
            "",
            "fn(&std::sync::Mutex<T>)",
            &patterns
        ));
        // An empty pattern list never matches (feature off).
        assert!(!custom_lock_descriptors_match(
            "parking_lot_core::word_lock::WordLock::lock",
            "",
            "",
            &[]
        ));
    }
}
