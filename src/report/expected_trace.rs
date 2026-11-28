//! Writes `expected-trace.json`: the event order a replay of each deadlock should see.
//! σ is expanded to original transitions and projected onto event sites.
//! Non-events are dropped; the net is not modified.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use serde_json::{Value, json};
use unipn::pt::PtNet;

use crate::report::events::{EventKind, event_sites, resource_name};
use crate::report::{ReportInputs, reported_deadlocks};
use crate::translate::lower::facts::TranslationProvenance;

/// Identifies the JSON shape; bumped when a field changes meaning.
pub const EXPECTED_TRACE_SCHEMA: &str = "pn-expected-trace/1";

/// What one `expected-trace.json` run contains, for the driver's summary line.
#[derive(Clone, Debug, Default)]
pub struct TraceStats {
    pub candidates: usize,
    pub events: usize,
    pub null_hints: usize,
}

/// Which thread the model's σ ran an event on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ThreadHint {
    /// The crate's `main` lineage.
    Main,
    /// A spawned closure, by first-appearance ordinal among spawned closures.
    Spawn(usize),
}

impl ThreadHint {
    fn json(self) -> Value {
        match self {
            ThreadHint::Main => Value::from("main"),
            ThreadHint::Spawn(ordinal) => Value::from(ordinal),
        }
    }
}

/// Build the `expected-trace.json` value.
///
/// The deadlock list and σ come from `inputs` exactly as the other reports
/// build them; the *raw* transitions of σ index the original net, so event
/// classification, `site_id`s and resource names all read `inputs.raw_net`.
pub fn build_expected_traces(
    inputs: &ReportInputs,
    provenance: &TranslationProvenance,
) -> (Value, TraceStats) {
    let site_of: BTreeMap<usize, usize> = event_sites(inputs.raw_net)
        .iter()
        .map(|site| (site.transition_id.index(), site.site_id))
        .collect();
    let mut stats = TraceStats::default();
    let deadlocks = reported_deadlocks(inputs);
    stats.candidates = deadlocks.len();

    let candidates: Vec<Value> = deadlocks
        .iter()
        .map(|data| {
            let (events, notes) = trace_of(data, inputs.raw_net, provenance, &site_of);
            stats.events += events.len();
            stats.null_hints += events
                .iter()
                .filter(|event| event["thread_hint"].is_null())
                .count();
            json!({
                "state_index": data.state_index,
                "reported": true,
                "sigma_len": data.sigma.len(),
                "events": events,
                "notes": notes,
            })
        })
        .collect();

    (
        json!({
            "schema": EXPECTED_TRACE_SCHEMA,
            "crate": inputs.crate_name,
            "candidates": candidates,
        }),
        stats,
    )
}

/// Write `dir/expected-trace.json`, creating `dir` if needed.
pub fn write_expected_traces(
    inputs: &ReportInputs,
    provenance: &TranslationProvenance,
    dir: &Path,
) -> std::io::Result<TraceStats> {
    let (report, stats) = build_expected_traces(inputs, provenance);
    let mut text = serde_json::to_string_pretty(&report).map_err(std::io::Error::other)?;
    text.push('\n');
    fs::create_dir_all(dir)?;
    fs::write(dir.join("expected-trace.json"), text)?;
    Ok(stats)
}

/// One raw transition of σ, with the frame bookkeeping the hint walk needs.
struct RawStep {
    transition_id: unipn::TransitionId,
    site_id: Option<usize>,
    kind: Option<EventKind>,
    function: String,
    resource: String,
}

fn trace_of(
    data: &crate::report::DeadlockData,
    net: &PtNet,
    provenance: &TranslationProvenance,
    site_of: &BTreeMap<usize, usize>,
) -> (Vec<Value>, Vec<String>) {
    let mut notes: Vec<String> = Vec::new();
    let mut steps: Vec<RawStep> = Vec::new();
    for step in &data.sigma {
        for raw in &step.raw {
            let origin = provenance.origin(raw.transition_id);
            if origin.is_none() {
                notes.push(format!(
                    "transition {} has no provenance record; its events (if any) are dropped",
                    raw.transition_id.index()
                ));
            }
            let kind = net
                .transition(raw.transition_id)
                .and_then(|t| EventKind::classify(&t.kind.transition_type));
            let resource = if kind.is_some() {
                resource_name(net, raw.transition_id)
            } else {
                String::new()
            };
            steps.push(RawStep {
                transition_id: raw.transition_id,
                site_id: site_of.get(&raw.transition_id.index()).copied(),
                kind,
                function: origin.map(|o| o.fn_def_path.clone()).unwrap_or_default(),
                resource,
            });
        }
    }

    // Frames: maximal runs of raw steps of the same function. The σ interleaves
    // frames of different threads, so a function can open, close and reopen.
    let mut frames: Vec<(String, Vec<usize>)> = Vec::new();
    for (index, step) in steps.iter().enumerate() {
        match frames.last_mut() {
            Some((function, members)) if *function == step.function => members.push(index),
            _ => frames.push((step.function.clone(), vec![index])),
        }
    }

    // Spawn sites: the parent functions whose frames contain a Spawn step.
    let mut spawned_parents: BTreeSet<String> = BTreeSet::new();
    for step in &steps {
        if step.kind == Some(EventKind::Spawn) {
            if step.function.is_empty() {
                notes.push(format!(
                    "spawn transition {} has no provenance; its thread cannot be named",
                    step.transition_id.index()
                ));
            } else {
                spawned_parents.insert(step.function.clone());
            }
        }
    }

    let mut hints: BTreeMap<usize, Option<ThreadHint>> = BTreeMap::new();
    let mut tracker = ThreadTracker::new(spawned_parents);
    for (function, members) in &frames {
        let hint = tracker.enter(function, &mut notes);
        for &index in members {
            hints.insert(index, hint);
        }
    }

    // Project onto events, in σ order; each entry names the site the conductor
    // will match against a `__trace::gate` request.
    let mut events: Vec<Value> = Vec::new();
    for (index, step) in steps.iter().enumerate() {
        let (Some(kind), Some(site_id)) = (step.kind, step.site_id) else {
            continue;
        };
        let hint = hints.get(&index).copied().flatten();
        events.push(json!({
            "seq": events.len(),
            "transition_id": step.transition_id.index(),
            "site_id": site_id,
            "kind": kind.name(),
            "function": step.function,
            "resource": step.resource,
            "thread_hint": hint.map(ThreadHint::json).unwrap_or(Value::Null),
        }));
    }
    (events, notes)
}

/// Frame-stack walk that assigns each frame a thread hint (see the module
/// docs). Deterministic: frames are entered in σ order and the stack is a
/// `Vec`, so only the nearest enclosing frame can win.
struct ThreadTracker {
    spawned_parents: BTreeSet<String>,
    closure_ordinals: BTreeMap<String, usize>,
    /// Open frames, innermost last, with the thread hint they run on.
    stack: Vec<(String, Option<ThreadHint>)>,
}

impl ThreadTracker {
    fn new(spawned_parents: BTreeSet<String>) -> Self {
        ThreadTracker {
            spawned_parents,
            closure_ordinals: BTreeMap::new(),
            stack: Vec::new(),
        }
    }

    /// The parent function of `name` when it is a closure
    /// (`crate::f::{closure#0}` -> `crate::f`); nested closures strip one level.
    fn closure_parent(name: &str) -> Option<&str> {
        let start = name.rfind("::{closure#")?;
        let rest = &name[start + "::{closure#".len()..];
        let digits = rest.strip_suffix('}')?;
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        Some(&name[..start])
    }

    fn enter(&mut self, function: &str, notes: &mut Vec<String>) -> Option<ThreadHint> {
        if function.is_empty() {
            // No provenance: the frame identity is unknown, keep the enclosing
            // hint so far (which is at least as good as a guess).
            let hint = self.stack.last().and_then(|(_, hint)| *hint);
            self.stack.push((function.to_string(), hint));
            return hint;
        }

        // A spawned closure opens a thread of its own.
        if let Some(parent) = Self::closure_parent(function) {
            if self.spawned_parents.contains(parent) {
                let next = self.closure_ordinals.len();
                let ordinal = *self
                    .closure_ordinals
                    .entry(function.to_string())
                    .or_insert(next);
                let hint = ThreadHint::Spawn(ordinal);
                if let Some(position) = self.stack.iter().position(|(name, _)| name == parent) {
                    self.stack.truncate(position + 1);
                } else {
                    notes.push(format!(
                        "closure {function} runs on a spawned thread but its parent frame \
                         {parent} is not open; the hint keeps the previous thread"
                    ));
                }
                self.stack.push((function.to_string(), Some(hint)));
                return Some(hint);
            }
        }

        // A frame that is already open continues on its own thread.
        if let Some(position) = self.stack.iter().rposition(|(name, _)| name == function) {
            let hint = self.stack[position].1;
            self.stack.truncate(position + 1);
            return hint;
        }

        // A new frame: it inherits the innermost open frame's thread, or main's
        // when it is the very first frame (the crate's entry point).
        let hint = self
            .stack
            .last()
            .and_then(|(_, hint)| *hint)
            .or(Some(ThreadHint::Main));
        self.stack.push((function.to_string(), hint));
        hint
    }
}
