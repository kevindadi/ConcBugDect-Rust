//! Writes `translation-coverage.json`: which instances were translated or dropped.
//! Counts come from the call graph and from `process_functions`.
//! It does not change the net or the deadlock report.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

/// Identifies the JSON shape of `translation-coverage.json`.
pub const COVERAGE_SCHEMA: &str = "pn-translation-coverage/1";

/// Maximum number of entries emitted in `dropped` and `opaque_calls`.
/// `counts` always reflects the true pre-truncation totals.
pub const MAX_COVERAGE_ITEMS: usize = 500;

/// Maximum number of library entry function names emitted in `entry_roots.entries`.
pub const MAX_ENTRY_ROOT_NAMES: usize = 50;

/// How `is_exported` was determined for functions in the analysed crate.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum PublicApiMethod {
    #[default]
    #[serde(rename = "effective_visibilities")]
    EffectiveVisibilities,
    #[serde(rename = "approx")]
    Approx,
}

impl PublicApiMethod {
    pub fn as_str(self) -> &'static str {
        match self {
            PublicApiMethod::EffectiveVisibilities => "effective_visibilities",
            PublicApiMethod::Approx => "approx",
        }
    }
}

/// Whether `def_id` is part of the local crate's exported public API.
///
/// Uses `tcx.effective_visibilities(()).is_exported(local_def_id)` for local
/// definitions; non-local items are never exported by the current crate.
pub fn is_function_exported(tcx: TyCtxt<'_>, def_id: DefId) -> (bool, PublicApiMethod) {
    (
        crate::analysis::entry_plan::is_local_exported(tcx, def_id),
        PublicApiMethod::EffectiveVisibilities,
    )
}

/// Final disposition of a function (`DefId`) in `PetriNet::process_functions`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionDisposition {
    Translated,
    NotReachable,
    CrateFiltered,
    /// Reachable and inside the crate filter, but `WithoutBody` or
    /// `is_mir_available` is false. No function frame is created.
    NoMirCallee,
    IgnoredByName(String),
}

/// Why a reachable function was not given a function place in the Petri net.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum DropReason {
    #[serde(rename = "ignored_by_name")]
    IgnoredByName,
    #[serde(rename = "crate_filtered")]
    CrateFiltered,
}

impl DropReason {
    pub fn as_str(self) -> &'static str {
        match self {
            DropReason::IgnoredByName => "ignored_by_name",
            DropReason::CrateFiltered => "crate_filtered",
        }
    }
}

/// One dropped function entry in `dropped[]`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DroppedFunction {
    pub name: String,
    pub reason: DropReason,
    pub pattern: Option<String>,
    pub span: String,
}

/// Why `handle_normal_call` had no callee frame and collapsed the call into a
/// direct transition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum OpaqueCallReason {
    #[serde(rename = "without_body")]
    WithoutBody,
    #[serde(rename = "filtered")]
    Filtered,
    #[serde(rename = "no_mir")]
    NoMir,
    /// Collapsed call whose callee is not in the sync registry.
    #[serde(rename = "unregistered")]
    Unregistered,
}

impl OpaqueCallReason {
    pub fn as_str(self) -> &'static str {
        match self {
            OpaqueCallReason::WithoutBody => "without_body",
            OpaqueCallReason::Filtered => "filtered",
            OpaqueCallReason::NoMir => "no_mir",
            OpaqueCallReason::Unregistered => "unregistered",
        }
    }
}

/// One collapsed call site in `opaque_calls[]`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpaqueCall {
    pub callee: String,
    pub caller: String,
    pub reason: OpaqueCallReason,
    pub span: String,
}

pub use crate::analysis::entry_plan::RootReason;

/// One library root that had no function place when `construct_library_entries`
/// marked initial tokens.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnplacedRoot {
    pub name: String,
    pub reason: String,
}

/// Summary counts in `counts`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoverageCounts {
    pub callgraph_instances: usize,
    pub with_body: usize,
    pub without_body: usize,
    pub translated_functions: usize,
    pub not_reachable: usize,
    pub crate_filtered: usize,
    pub ignored_by_name: usize,
    /// Reachable in-crate defs that did not receive a function frame because
    /// the call-graph node has no body or MIR is unavailable.
    pub no_mir_callee: usize,
}

/// Public API counts in `public_api`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublicApiCoverage {
    pub exported_functions: usize,
    pub translated_exported: usize,
}

/// Breakdown of concurrent roots by primitive family.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EntryRootsByReason {
    pub lockguard: usize,
    pub condvar: usize,
    pub atomic: usize,
    pub custom_lock: usize,
}

/// Concurrent root statistics in `entry_roots`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EntryRootsCoverage {
    pub count: usize,
    pub marked: usize,
    pub unplaced: usize,
    pub private_helpers: usize,
    pub public_marked: usize,
    pub private_skipped: usize,
    pub fallback_used: bool,
    pub entries: Vec<String>,
    pub by_reason: EntryRootsByReason,
}

/// Read-only translation coverage accumulator attached to `PetriNet`.
#[derive(Clone, Debug, Default)]
pub struct Coverage {
    pub entry_mode: String,
    pub public_api_method: PublicApiMethod,
    pub counts: CoverageCounts,
    pub public_api: PublicApiCoverage,
    pub entry_roots: EntryRootsCoverage,
    pub dropped: Vec<DroppedFunction>,
    pub opaque_calls: Vec<OpaqueCall>,
    pub unplaced_roots: Vec<UnplacedRoot>,
    /// Joins whose `JoinHandle` was produced in another function. Counted,
    /// warned once, and not translated as an ordinary call.
    pub unsupported_cross_fn_join: usize,
    cross_fn_join_warned: bool,
    root_reasons: BTreeMap<usize, BTreeSet<RootReason>>,
    root_private: BTreeMap<usize, bool>,
}

impl Coverage {
    pub fn new() -> Self {
        Self {
            entry_mode: "main".to_string(),
            ..Self::default()
        }
    }

    pub fn set_entry_mode(&mut self, mode: &str) {
        self.entry_mode = mode.to_string();
    }

    pub fn record_callgraph_counts(
        &mut self,
        callgraph_instances: usize,
        with_body: usize,
        without_body: usize,
    ) {
        self.counts.callgraph_instances = callgraph_instances;
        self.counts.with_body = with_body;
        self.counts.without_body = without_body;
    }

    /// Record a concurrent root instance and one of the reasons that selected
    /// it (`lockguard`, `condvar`, `atomic`, `custom_lock`), plus
    /// whether the root function is a private helper (`!is_exported`).
    ///
    /// Keyed by `instance_id.index()` so repeated calls to
    /// `concurrent_root_instance_ids` during net construction are idempotent.
    pub fn record_concurrent_root(
        &mut self,
        instance_index: usize,
        reason: RootReason,
        is_private: bool,
    ) {
        self.root_reasons
            .entry(instance_index)
            .or_default()
            .insert(reason);
        self.root_private.insert(instance_index, is_private);
        self.recompute_root_totals();
    }

    fn recompute_root_totals(&mut self) {
        self.entry_roots.count = self.root_reasons.len();
        self.entry_roots.private_helpers = self
            .root_private
            .values()
            .filter(|&&is_private| is_private)
            .count();

        let mut by_reason = EntryRootsByReason::default();
        for reasons in self.root_reasons.values() {
            for reason in reasons {
                match reason {
                    RootReason::Lockguard => by_reason.lockguard += 1,
                    RootReason::Condvar => by_reason.condvar += 1,
                    RootReason::Atomic => by_reason.atomic += 1,
                    RootReason::CustomLock => by_reason.custom_lock += 1,
                }
            }
        }
        self.entry_roots.by_reason = by_reason;
    }

    /// Record the outcome of `PetriNet::construct_library_entries`.
    pub fn record_library_entries(
        &mut self,
        marked: usize,
        unplaced: usize,
        public_marked: usize,
        private_skipped: usize,
        fallback_used: bool,
        mut entries: Vec<String>,
        unplaced_roots: Vec<UnplacedRoot>,
    ) {
        entries.sort();
        entries.dedup();
        entries.truncate(MAX_ENTRY_ROOT_NAMES);
        self.entry_roots.marked = marked;
        self.entry_roots.unplaced = unplaced;
        self.entry_roots.public_marked = public_marked;
        self.entry_roots.private_skipped = private_skipped;
        self.entry_roots.fallback_used = fallback_used;
        self.entry_roots.entries = entries;
        self.unplaced_roots = unplaced_roots;
    }

    /// Record an opaque call encountered in `BodyToPetriNet::handle_normal_call`.
    /// Returns `true` the first time, so the translator can `log::warn!` once.
    pub fn note_unsupported_cross_fn_join(&mut self, fn_path: &str) -> bool {
        self.unsupported_cross_fn_join += 1;
        let first = !self.cross_fn_join_warned;
        if first {
            log::warn!(
                "unsupported cross-function JoinHandle in {fn_path}: spawn and join are not in the same function"
            );
        }
        self.cross_fn_join_warned = true;
        first
    }

    pub fn record_opaque_call(
        &mut self,
        callee: String,
        caller: String,
        reason: OpaqueCallReason,
        span: String,
    ) {
        self.opaque_calls.push(OpaqueCall {
            callee,
            caller,
            reason,
            span,
        });
    }
}

/// Build the deterministic `translation-coverage.json` value.
pub fn build_coverage_report(crate_name: &str, coverage: &Coverage) -> Value {
    let mut dropped = coverage.dropped.clone();
    dropped.sort_by(|a, b| {
        a.name
            .cmp(&b.name)
            .then_with(|| a.reason.as_str().cmp(b.reason.as_str()))
            .then_with(|| a.pattern.cmp(&b.pattern))
            .then_with(|| a.span.cmp(&b.span))
    });

    let mut opaque_calls = coverage.opaque_calls.clone();
    opaque_calls.sort_by(|a, b| {
        a.callee
            .cmp(&b.callee)
            .then_with(|| a.caller.cmp(&b.caller))
            .then_with(|| a.reason.as_str().cmp(b.reason.as_str()))
            .then_with(|| a.span.cmp(&b.span))
    });

    let truncated = dropped.len() > MAX_COVERAGE_ITEMS || opaque_calls.len() > MAX_COVERAGE_ITEMS;
    dropped.truncate(MAX_COVERAGE_ITEMS);
    opaque_calls.truncate(MAX_COVERAGE_ITEMS);

    let dropped_json: Vec<Value> = dropped
        .iter()
        .map(|d| {
            json!({
                "name": d.name,
                "reason": d.reason.as_str(),
                "pattern": d.pattern,
                "span": d.span,
            })
        })
        .collect();

    let opaque_json: Vec<Value> = opaque_calls
        .iter()
        .map(|c| {
            json!({
                "callee": c.callee,
                "caller": c.caller,
                "reason": c.reason.as_str(),
                "span": c.span,
            })
        })
        .collect();

    let entry_mode = if coverage.entry_mode.is_empty() {
        "main"
    } else {
        coverage.entry_mode.as_str()
    };

    let mut entries = coverage.entry_roots.entries.clone();
    entries.sort();
    entries.dedup();
    entries.truncate(MAX_ENTRY_ROOT_NAMES);

    let mut entry_roots_json = json!({
        "count": coverage.entry_roots.count,
        "marked": coverage.entry_roots.marked,
        "unplaced": coverage.entry_roots.unplaced,
        "private_helpers": coverage.entry_roots.private_helpers,
        "by_reason": {
            "lockguard": coverage.entry_roots.by_reason.lockguard,
            "condvar": coverage.entry_roots.by_reason.condvar,
            "atomic": coverage.entry_roots.by_reason.atomic,
            "custom_lock": coverage.entry_roots.by_reason.custom_lock,
        },
    });
    if entry_mode != "main" {
        entry_roots_json["public_marked"] = json!(coverage.entry_roots.public_marked);
        entry_roots_json["private_skipped"] = json!(coverage.entry_roots.private_skipped);
        entry_roots_json["fallback_used"] = json!(coverage.entry_roots.fallback_used);
        entry_roots_json["entries"] = json!(entries);
    }

    let mut report = json!({
        "schema": COVERAGE_SCHEMA,
        "crate": crate_name,
        "entry_mode": entry_mode,
        "public_api_method": coverage.public_api_method.as_str(),
        "counts": {
            "callgraph_instances": coverage.counts.callgraph_instances,
            "with_body": coverage.counts.with_body,
            "without_body": coverage.counts.without_body,
            "translated_functions": coverage.counts.translated_functions,
            "not_reachable": coverage.counts.not_reachable,
            "crate_filtered": coverage.counts.crate_filtered,
            "ignored_by_name": coverage.counts.ignored_by_name,
            "ignored_by_name_deprecated": true,
            "unsupported_cross_fn_join": coverage.unsupported_cross_fn_join,
            "no_mir_callee": coverage.counts.no_mir_callee,
        },
        "public_api": {
            "exported_functions": coverage.public_api.exported_functions,
            "translated_exported": coverage.public_api.translated_exported,
        },
        "entry_roots": entry_roots_json,
        "dropped": dropped_json,
        "opaque_calls": opaque_json,
    });

    if truncated {
        report["truncated"] = json!(true);
    }

    report
}

/// Write `dir/translation-coverage.json`, creating `dir` if needed.
pub fn write_coverage_report(
    crate_name: &str,
    coverage: &Coverage,
    dir: &Path,
) -> std::io::Result<()> {
    let report = build_coverage_report(crate_name, coverage);
    let mut text = serde_json::to_string_pretty(&report).map_err(std::io::Error::other)?;
    text.push('\n');
    fs::create_dir_all(dir)?;
    fs::write(dir.join("translation-coverage.json"), text)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dyn_dispatch_no_wait_records_no_mir_callee_without_dropping_old_counts() {
        let mut cov = Coverage::new();
        cov.counts.translated_functions = 2;
        cov.counts.without_body = 1;
        cov.counts.crate_filtered = 0;
        cov.counts.not_reachable = 0;
        cov.counts.no_mir_callee = 1;
        let report = build_coverage_report("dyn_dispatch_no_wait", &cov);
        assert_eq!(report["counts"]["no_mir_callee"], 1);
        assert_eq!(report["counts"]["translated_functions"], 2);
        assert_eq!(report["counts"]["without_body"], 1);
        assert_eq!(report["counts"]["crate_filtered"], 0);
        assert_eq!(report["counts"]["not_reachable"], 0);
    }

    #[test]
    fn coverage_report_sorts_and_truncates_deterministically() {
        let mut cov = Coverage::new();
        cov.set_entry_mode("library-roots");
        cov.record_callgraph_counts(10, 6, 4);
        cov.counts.translated_functions = 2;
        cov.counts.not_reachable = 1;
        cov.counts.crate_filtered = 505;
        cov.counts.ignored_by_name = 1;
        cov.public_api.exported_functions = 3;
        cov.public_api.translated_exported = 1;

        cov.record_concurrent_root(0, RootReason::Lockguard, false);
        cov.record_concurrent_root(0, RootReason::Condvar, false);
        cov.record_concurrent_root(1, RootReason::Atomic, true);
        cov.record_library_entries(
            1,
            0,
            1,
            1,
            false,
            vec!["my_crate::pub_fn".to_string()],
            Vec::new(),
        );

        for i in (0..505).rev() {
            cov.dropped.push(DroppedFunction {
                name: format!("dep::fn_{i:04}"),
                reason: DropReason::CrateFiltered,
                pattern: None,
                span: format!("src/lib.rs:{i}:1"),
            });
        }
        cov.dropped.push(DroppedFunction {
            name: "a_crate::fmt::helper".to_string(),
            reason: DropReason::IgnoredByName,
            pattern: Some("::fmt::".to_string()),
            span: "src/lib.rs:1:1".to_string(),
        });

        cov.record_opaque_call(
            "std::io::_print".to_string(),
            "my_crate::f".to_string(),
            OpaqueCallReason::WithoutBody,
            "src/lib.rs:10:5".to_string(),
        );
        cov.record_opaque_call(
            "alloc::sync::Arc::new".to_string(),
            "my_crate::f".to_string(),
            OpaqueCallReason::WithoutBody,
            "src/lib.rs:9:5".to_string(),
        );

        let first = build_coverage_report("my_crate", &cov);
        let second = build_coverage_report("my_crate", &cov);
        assert_eq!(
            serde_json::to_string(&first).unwrap(),
            serde_json::to_string(&second).unwrap()
        );
        assert_eq!(first["schema"], COVERAGE_SCHEMA);
        assert_eq!(first["truncated"], true);
        assert_eq!(first["counts"]["crate_filtered"], 505);
        assert_eq!(first["counts"]["ignored_by_name"], 1);
        assert_eq!(first["counts"]["no_mir_callee"], 0);
        assert_eq!(
            first["dropped"].as_array().unwrap().len(),
            MAX_COVERAGE_ITEMS
        );
        assert_eq!(first["dropped"][0]["name"], "a_crate::fmt::helper");
        assert_eq!(first["dropped"][0]["pattern"], "::fmt::");
        assert_eq!(first["opaque_calls"][0]["callee"], "alloc::sync::Arc::new");
        assert_eq!(first["entry_roots"]["count"], 2);
        assert_eq!(first["entry_roots"]["marked"], 1);
        assert_eq!(first["entry_roots"]["public_marked"], 1);
        assert_eq!(first["entry_roots"]["private_skipped"], 1);
        assert_eq!(first["entry_roots"]["fallback_used"], false);
        assert_eq!(first["entry_roots"]["entries"], json!(["my_crate::pub_fn"]));
        assert_eq!(first["entry_roots"]["private_helpers"], 1);
        assert_eq!(first["entry_roots"]["by_reason"]["lockguard"], 1);
        assert_eq!(first["entry_roots"]["by_reason"]["condvar"], 1);
        assert_eq!(first["entry_roots"]["by_reason"]["atomic"], 1);
    }
}
