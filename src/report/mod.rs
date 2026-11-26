//! Deadlock report types and `write_deadlock_report`.
//! Selection, σ, and JSON projection live in `deadlock` and `json`.
//! This file does not decide which states are deadlocks.

use std::fs;
use std::path::Path;

use unipn::analysis::pt::reachability::StateGraph;
use unipn::analysis::pt::reduce::ReductionTrace;
use unipn::net::TransitionId;
use unipn::pt::{PtNet, TransitionType};

pub mod concir_net;
pub mod coverage;
pub mod events;
pub mod expected_trace;
pub mod predicates;
pub mod refinements;

mod json;

mod deadlock;
pub use deadlock::{
    build_deadlock_report, frontier_state_count, reported_deadlocks, reported_state_indices,
};

/// Identifies the JSON shape; bumped when a field changes meaning.
pub const SCHEMA: &str = "pn-deadlock-report/2";

/// At most this many deadlocks are spelled out; the rest only count. A
/// counterexample is for a human to read, and twenty blocked-state dumps is
/// already more than a report can carry.
pub const MAX_REPORTED_DEADLOCKS: usize = 20;

/// σ is truncated to this many steps. The state limit already caps the graph,
/// so this only fires when the state limit is disabled.
pub const MAX_SIGMA_STEPS: usize = 200_000;

/// One original-net transition a σ step lifts to.
#[derive(Clone, Debug)]
pub struct RawTrans {
    pub transition_id: TransitionId,
    pub name: String,
}

/// One σ step, structured: exactly what the JSON report carries per step,
/// without the JSON in between.
#[derive(Clone, Debug)]
pub struct SigmaStep {
    pub step: usize,
    pub from_state: usize,
    pub to_state: usize,
    pub transition_id: TransitionId,
    pub name: String,
    pub transition_type: TransitionType,
    /// The original transitions this (possibly reduced) transition stands for,
    /// in the order the lift produces them; `[self]` without a reduction.
    pub raw: Vec<RawTrans>,
}

/// The structured counterpart of one reported deadlock: what the JSON writer
/// and the path-predicate extractor need, with no JSON in between.
#[derive(Clone, Debug)]
pub struct DeadlockData {
    pub state_index: usize,
    pub sigma: Vec<SigmaStep>,
    pub sigma_truncated: bool,
    /// The concurrent roots of the slice this candidate came from (
    /// per-entry slicing). Empty when the graph was explored jointly — main
    /// mode and the non-sliced fallback.
    pub entry_roots: Vec<String>,
}

/// Everything the report is built from.
///
/// `raw_net` is the pre-reduction snapshot (`== net` when no reduction ran)
/// and `net` is the net the state graph was built on; `reduce_trace` is
/// `Some` exactly when the reduction actually rewrote the net.
///
/// `excluded` holds candidate state indices whose σ dynamic evidence refuted
/// (`--exclude-candidates`,). It is report-side only: the net, the
/// state graph and `deadlock_count` stay untouched, and an empty set restores
/// the byte-identical previous report.
///
/// `entry_mode` is `"main"` for a binary crate and `"library-roots"` when the
/// crate had no `entry_fn` and the library-entry semantics marked every
/// concurrent root. The field is written into the `net` block only for
/// `"library-roots"`: main-mode reports must stay byte-identical to the
/// pre-library-entry output (hard gate), so their absence of the field means
/// `"main"`.
///
/// `slice_layout` is `Some` exactly when the state graph was built by
/// [`crate::pipeline::slices::slice_state_graphs`] (library mode,). It is
/// provenance only: it selects each candidate's σ start (one initial state
/// per slice) and adds the `entry_root`/`slicing` fields. `None` leaves every
/// report byte-identical to the pre-slicing output. The slicing stage owns
/// the layout; the report only consumes it.
pub struct ReportInputs<'a> {
    pub crate_name: &'a str,
    pub raw_net: &'a PtNet,
    pub net: &'a PtNet,
    pub state_graph: &'a StateGraph,
    pub reduce_trace: Option<&'a ReductionTrace>,
    pub excluded: &'a std::collections::BTreeSet<usize>,
    pub entry_mode: &'a str,
    pub slice_layout: Option<&'a crate::pipeline::slices::SliceLayout>,
}

/// The `excluded` set of a run without refinements, for callers that build a
/// [`ReportInputs`] directly (tests, tools).
pub static NO_EXCLUSIONS: std::sync::LazyLock<std::collections::BTreeSet<usize>> =
    std::sync::LazyLock::new(std::collections::BTreeSet::new);

/// Write `dir/deadlocks.json`, creating `dir` if needed.
pub fn write_deadlock_report(inputs: &ReportInputs, dir: &Path) -> std::io::Result<()> {
    let report = build_deadlock_report(inputs);
    let mut text = serde_json::to_string_pretty(&report).map_err(std::io::Error::other)?;
    text.push('\n');
    fs::create_dir_all(dir)?;
    fs::write(dir.join("deadlocks.json"), text)
}

#[cfg(test)]
mod fixture {
    use super::{NO_EXCLUSIONS, ReportInputs, build_deadlock_report};
    use serde_json::Value;
    use unipn::analysis::pt::reachability::{StateGraph, StateGraphConfig};
    use unipn::net::{ControlSub, Marking, PlaceId, TransitionId};
    use unipn::pt::{PtBuilder, PtNet, PtPlaceKind, PtTransitionKind, TransitionType};

    pub(super) fn bb() -> PtPlaceKind {
        PtPlaceKind::control(ControlSub::BasicBlock)
    }

    pub(super) fn end() -> PtPlaceKind {
        PtPlaceKind::control(ControlSub::FunctionEnd)
    }

    pub(super) fn res() -> PtPlaceKind {
        PtPlaceKind::resource()
    }

    pub(super) fn add_t(
        b: &mut PtBuilder,
        name: &str,
        ty: TransitionType,
        pre: &[PlaceId],
        post: &[PlaceId],
    ) -> TransitionId {
        let t = b.add_transition(name, PtTransitionKind::new(ty));
        for &p in pre {
            b.add_input_arc(p, t, 1);
        }
        for &p in post {
            b.add_output_arc(p, t, 1);
        }
        t
    }

    pub(super) fn state_graph(net: &PtNet, m0: &Marking) -> StateGraph {
        StateGraph::with_config(
            net,
            m0.clone(),
            StateGraphConfig {
                state_limit: Some(20_000),
                include_zero_tokens: false,
                use_por: false,
            },
        )
    }

    pub(super) fn report_of<'a>(crate_name: &'a str, net: &'a PtNet, sg: &'a StateGraph) -> Value {
        build_deadlock_report(&ReportInputs {
            crate_name,
            raw_net: net,
            net,
            state_graph: sg,
            reduce_trace: None,
            excluded: &NO_EXCLUSIONS,
            entry_mode: "main",
            slice_layout: None,
        })
    }
}
