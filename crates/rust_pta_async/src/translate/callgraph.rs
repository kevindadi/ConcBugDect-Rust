//! Async runtime API classification (tokio / async-std / …).

use rust_petri_net_analysis::translate::structure::KeyApiRegex;
use rust_petri_net_analysis::util::has_pn_attribute;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

/// Async thread-control kinds (experiment crate only).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AsyncThreadControlKind {
    Spawn,
    Join,
}

/// Classify async spawn/join APIs. Returns `None` for sync-only APIs.
pub fn classify_async_thread_control(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    fn_path: &str,
    key_api_regex: &KeyApiRegex,
) -> Option<AsyncThreadControlKind> {
    if has_pn_attribute(tcx, def_id, "pn_async_spawn") {
        return Some(AsyncThreadControlKind::Spawn);
    }
    if has_pn_attribute(tcx, def_id, "pn_async_join") {
        return Some(AsyncThreadControlKind::Join);
    }

    if fn_path.contains("tokio::task::spawn") || fn_path.contains("tokio::runtime::Runtime::spawn") {
        return Some(AsyncThreadControlKind::Spawn);
    }
    if fn_path.contains("async_std::task::spawn") {
        return Some(AsyncThreadControlKind::Spawn);
    }
    if fn_path.contains("smol::Task::spawn") || fn_path.contains("smol::spawn") {
        return Some(AsyncThreadControlKind::Spawn);
    }

    if fn_path.contains("tokio::task::JoinHandle")
        && (fn_path.contains("await") || fn_path.contains("blocking_on"))
    {
        return Some(AsyncThreadControlKind::Join);
    }

    if key_api_regex.thread_spawn.is_match(fn_path)
        && (fn_path.contains("tokio") || fn_path.contains("async_std") || fn_path.contains("smol"))
    {
        return Some(AsyncThreadControlKind::Spawn);
    }

    if key_api_regex.thread_join.is_match(fn_path)
        && (fn_path.contains("tokio") || fn_path.contains("JoinHandle"))
    {
        return Some(AsyncThreadControlKind::Join);
    }

    None
}

/// Default async spawn/join regex entries for `PnConfig` (experiment builds).
pub fn default_async_spawn_patterns() -> Vec<String> {
    vec![
        r"tokio::task::spawn".to_string(),
        r"tokio::runtime::Runtime::spawn".to_string(),
        r"async_std::task::spawn".to_string(),
        r"smol::Task::spawn".to_string(),
        r"smol::spawn".to_string(),
    ]
}

pub fn default_async_join_patterns() -> Vec<String> {
    vec![
        r"tokio::task::JoinHandle::await".to_string(),
        r"tokio::task::JoinHandle::blocking_on".to_string(),
    ]
}
