//! Writes `predicates.json`: path predicates for each reported deadlock's σ.
//! Steps are expanded to original-net transitions before the predicate is built.
//! It does not add or remove deadlock candidates.

use std::collections::HashSet;
use std::fs;
use std::path::Path;

use serde_json::{Value, json};

use crate::report::{DeadlockData, ReportInputs, reported_deadlocks};
use crate::translate::lower::facts::{DefRecord, FunctionFacts, GuardFacts, TranslationProvenance};
use unipn::TransitionId;

/// Identifies the JSON shape; bumped when a field changes meaning.
pub const PREDICATE_SCHEMA: &str = "pn-path-predicates/1";

/// Upper bound on the entries of one guard's Def-Use chain.
pub const MAX_DEF_USE_ENTRIES: usize = 8;

/// What one `predicates.json` run contains, for the driver's summary line.
#[derive(Clone, Debug, Default)]
pub struct PredicateStats {
    pub candidates: usize,
    pub guards: usize,
    pub switches: usize,
    pub asserts: usize,
    pub verified: usize,
    pub unverified: usize,
}

/// Build the `predicates.json` value for the reported deadlocks.
pub fn build_predicates(
    inputs: &ReportInputs,
    provenance: &TranslationProvenance,
) -> (Value, PredicateStats) {
    let deadlocks = reported_deadlocks(inputs);
    let mut stats = PredicateStats {
        candidates: deadlocks.len(),
        ..PredicateStats::default()
    };
    let candidates: Vec<Value> = deadlocks
        .iter()
        .map(|data| candidate_json(data, provenance, &mut stats))
        .collect();

    let report = json!({
        "schema": PREDICATE_SCHEMA,
        "crate": inputs.crate_name,
        "candidates": candidates,
    });
    (report, stats)
}

/// Write `dir/predicates.json`, creating `dir` if needed; returns the stats
/// the driver logs.
pub fn write_predicates(
    inputs: &ReportInputs,
    provenance: &TranslationProvenance,
    dir: &Path,
) -> std::io::Result<PredicateStats> {
    let (report, stats) = build_predicates(inputs, provenance);
    let mut text = serde_json::to_string_pretty(&report).map_err(std::io::Error::other)?;
    text.push('\n');
    fs::create_dir_all(dir)?;
    fs::write(dir.join("predicates.json"), text)?;
    Ok(stats)
}

/// One raw transition on a frame path, with where it came from.
struct PathEntry {
    transition_id: TransitionId,
    bb: usize,
    span: String,
}

/// One function frame of a σ: the consecutive raw transitions of one function.
struct FramePath {
    function: String,
    entries: Vec<PathEntry>,
}

fn candidate_json(
    data: &DeadlockData,
    provenance: &TranslationProvenance,
    stats: &mut PredicateStats,
) -> Value {
    let mut unresolved: Vec<String> = Vec::new();
    let frames = split_frames(data, provenance, &mut unresolved);
    let frames_json: Vec<Value> = frames
        .iter()
        .map(|frame| frame_json(frame, provenance, &mut unresolved, stats))
        .collect();

    json!({
        "state_index": data.state_index,
        "reported": true,
        "sigma_len": data.sigma.len(),
        "unresolved": unresolved,
        "frames": frames_json,
    })
}

/// Project σ into `(function, bb)` and cut it into frames at function changes.
/// A raw transition without provenance continues the current frame and is
/// reported in the candidate's `unresolved` list.
fn split_frames(
    data: &DeadlockData,
    provenance: &TranslationProvenance,
    unresolved: &mut Vec<String>,
) -> Vec<FramePath> {
    let mut frames: Vec<FramePath> = Vec::new();
    for step in &data.sigma {
        for raw in &step.raw {
            match provenance.origin(raw.transition_id) {
                Some(origin) => {
                    if frames
                        .last()
                        .map_or(true, |frame| frame.function != origin.fn_def_path)
                    {
                        frames.push(FramePath {
                            function: origin.fn_def_path.clone(),
                            entries: Vec::new(),
                        });
                    }
                    frames.last_mut().unwrap().entries.push(PathEntry {
                        transition_id: raw.transition_id,
                        bb: origin.bb,
                        span: origin.span.clone(),
                    });
                }
                None => unresolved.push(format!(
                    "transition {} has no provenance record",
                    raw.transition_id.index()
                )),
            }
        }
    }
    frames
}

fn frame_json(
    frame: &FramePath,
    provenance: &TranslationProvenance,
    unresolved: &mut Vec<String>,
    stats: &mut PredicateStats,
) -> Value {
    let bb_path: Vec<usize> = frame.entries.iter().map(|entry| entry.bb).collect();
    let Some(facts) = provenance.function(&frame.function) else {
        unresolved.push(format!("no MIR facts for function {}", frame.function));
        return json!({
            "function": frame.function,
            "bb_path": bb_path,
            "back_edges_cut": [],
            "guards": [],
        });
    };

    let back_edges_cut: Vec<Value> = facts
        .cut_back_edges
        .iter()
        .map(|(from, to)| json!([from, to]))
        .collect();

    let mut guards = Vec::new();
    for (pos, entry) in frame.entries.iter().enumerate() {
        // The guard belongs to the block's terminator; only the transition
        // that implements the branch fires it. Other transitions of the same
        // block (its start, statements) must not be mistaken for the guard.
        if !provenance.is_guard_transition(entry.transition_id) {
            continue;
        }
        let Some(bb_facts) = facts.bb(entry.bb) else {
            continue;
        };
        let Some(guard) = &bb_facts.guard else {
            continue;
        };
        stats.guards += 1;
        match guard {
            GuardFacts::Switch { .. } => stats.switches += 1,
            GuardFacts::Assert { .. } => stats.asserts += 1,
        }
        let next_bb = frame.entries.get(pos + 1).map(|entry| entry.bb);
        guards.push(guard_json(
            guard,
            &frame.function,
            entry.bb,
            &entry.span,
            next_bb,
            facts,
            provenance,
            &bb_path,
            pos,
            stats,
        ));
    }

    json!({
        "function": frame.function,
        "bb_path": bb_path,
        "back_edges_cut": back_edges_cut,
        "guards": guards,
    })
}

/// The entry source span of a switch target block: a source location inside
/// the block, or the empty string when the block produced no transition. This
/// is what lets the verifier check "the taken arm's code ran" for switches
/// rustc builds without a branch region (e.g. `match`).
fn target_entry_span(provenance: &TranslationProvenance, function: &str, target: usize) -> String {
    provenance
        .bb_entry_span(function, target)
        .unwrap_or("")
        .to_string()
}

/// One walked-branch guard. `taken_target`/`taken_bb` are `-1` when the taken
/// branch cannot be observed (the guard is the frame's last step); such an
/// entry is `verified: false` and `unresolved: true` and is only *marked*.
/// A path that contradicts the guard's own target list is an anomaly and is
/// additionally logged with `log::error!`.
#[allow(clippy::too_many_arguments)]
fn guard_json(
    guard: &GuardFacts,
    function: &str,
    bb: usize,
    span: &str,
    next_bb: Option<usize>,
    facts: &FunctionFacts,
    provenance: &TranslationProvenance,
    bb_path: &[usize],
    pos: usize,
    stats: &mut PredicateStats,
) -> Value {
    let span = if span.is_empty() {
        "<no-location>"
    } else {
        span
    };

    match guard {
        GuardFacts::Switch {
            operand,
            operand_local,
            targets,
        } => {
            let taken =
                next_bb.and_then(|next| targets.iter().position(|(_, target)| *target == next));
            let (taken_value, is_otherwise, taken_target, verified) = if let Some(next) = next_bb {
                match taken {
                    Some(index) => {
                        let (value, _) = targets[index];
                        (value.map(value_json), value.is_none(), next as i64, true)
                    }
                    None => {
                        // The path walked a branch the facts do not declare:
                        // worth an error line (the other unverified case — the
                        // guard being the frame's last step — is benign).
                        log::error!(
                            "path predicates: switch at {function} bb{bb} ({span}) took target \
                             {next}, which is not among its MIR targets {targets:?}"
                        );
                        (None, false, next as i64, false)
                    }
                }
            } else {
                (None, false, -1, false)
            };
            let other_targets: Vec<Value> = targets
                .iter()
                .enumerate()
                .filter(|(index, _)| Some(*index) != taken)
                .map(|(_, (value, target))| {
                    json!({
                        "value": value.map(value_json),
                        "bb": target,
                        "span": target_entry_span(provenance, function, *target),
                    })
                })
                .collect();
            let taken_target_span = if taken_target >= 0 {
                target_entry_span(provenance, function, taken_target as usize)
            } else {
                String::new()
            };

            let def_use = def_use_json(facts, bb_path, pos, *operand_local);
            stats.verified += usize::from(verified);
            stats.unverified += usize::from(!verified);

            let mut entry = json!({
                "kind": "switch",
                "bb": bb,
                "span": span,
                "operand": operand_field(operand, *operand_local),
                "operand_place": operand,
                "taken_value": taken_value,
                "is_otherwise": is_otherwise,
                "taken_target": taken_target,
                "taken_target_span": taken_target_span,
                "other_targets": other_targets,
                "taken_bb": taken_target,
                "verified": verified,
                "def_use": def_use.entries,
            });
            mark_def_use(&mut entry, verified, def_use.truncated);
            entry
        }
        GuardFacts::Assert {
            operand,
            operand_local,
            expected,
            target,
        } => {
            let verified = next_bb == Some(*target);
            if let Some(next) = next_bb
                && !verified
            {
                log::error!(
                    "path predicates: assert at {function} bb{bb} ({span}) has success target \
                     {target}, but the path continued at bb{next}"
                );
            }
            let taken_bb = next_bb.map_or(-1, |next| next as i64);

            let def_use = def_use_json(facts, bb_path, pos, *operand_local);
            stats.verified += usize::from(verified);
            stats.unverified += usize::from(!verified);

            let mut entry = json!({
                "kind": "assert",
                "bb": bb,
                "span": span,
                "operand": operand_field(operand, *operand_local),
                "operand_place": operand,
                "expected": expected,
                "taken_target": *target as i64,
                "taken_bb": taken_bb,
                "verified": verified,
                "def_use": def_use.entries,
            });
            mark_def_use(&mut entry, verified, def_use.truncated);
            entry
        }
    }
}

/// Add the optional failure markers only when they apply, keeping the common
/// shape stable.
fn mark_def_use(entry: &mut Value, verified: bool, truncated: bool) {
    if !verified {
        entry["unresolved"] = json!(true);
    }
    if truncated {
        entry["def_use_truncated"] = json!(true);
    }
}

/// The `operand` field: the root local's name when the operand reads a place
/// (`_3`), otherwise the `Debug` form of the operand (e.g. `const 1_i32`).
fn operand_field(operand: &str, local: Option<usize>) -> String {
    match local {
        Some(local) => format!("_{local}"),
        None => operand.to_string(),
    }
}

fn value_json(value: u128) -> Value {
    match u64::try_from(value) {
        Ok(value) => json!(value),
        Err(_) => {
            log::warn!("path predicates: switch value {value} does not fit u64; kept as a string");
            json!(value.to_string())
        }
    }
}

// Def-Use chains ─────────────────────────────────────────────────────────

struct DefUse {
    entries: Vec<Value>,
    truncated: bool,
}

fn def_use_json(
    facts: &FunctionFacts,
    bb_path: &[usize],
    guard_pos: usize,
    root: Option<usize>,
) -> DefUse {
    let mut walker = DefUseWalker {
        facts,
        bb_path,
        entries: Vec::new(),
        visited: HashSet::new(),
        truncated: false,
    };
    if let Some(root) = root {
        walker.push_local(root, guard_pos, usize::MAX);
    }
    DefUse {
        entries: walker.entries,
        truncated: walker.truncated,
    }
}

struct DefUseWalker<'a> {
    facts: &'a FunctionFacts,
    bb_path: &'a [usize],
    entries: Vec<Value>,
    visited: HashSet<usize>,
    truncated: bool,
}

impl DefUseWalker<'_> {
    /// Record the nearest definition of `local` strictly before
    /// `(before_path, before_def)` on the frame path, then recurse into that
    /// definition's operands. Parameters and locals with no definition on the
    /// path still get an entry (declaration span), so the chain never silently
    /// stops without a span to follow.
    fn push_local(&mut self, local: usize, before_path: usize, before_def: usize) {
        if self.entries.len() >= MAX_DEF_USE_ENTRIES {
            self.truncated = true;
            return;
        }
        if !self.visited.insert(local) {
            return;
        }

        let found = find_def(self.facts, self.bb_path, before_path, before_def, local).map(
            |(path_pos, def_index, def)| {
                (
                    path_pos,
                    def_index,
                    def.span.clone(),
                    def.rhs.clone(),
                    def.operands.clone(),
                    def.stop_recursion,
                )
            },
        );

        if let Some((path_pos, def_index, span, rhs, operands, stop)) = found {
            self.entries.push(json!({
                "place": format!("_{local}"),
                "span": span,
                "rhs": rhs,
            }));
            if stop {
                return;
            }
            for operand in operands {
                self.push_local(operand, path_pos, def_index);
            }
        } else {
            let rhs = if self.facts.is_param(local) {
                "param"
            } else {
                "no-def-on-path"
            };
            let span = self
                .facts
                .local_span(local)
                .unwrap_or("<no-location>")
                .to_string();
            self.entries.push(json!({
                "place": format!("_{local}"),
                "span": span,
                "rhs": rhs,
            }));
        }
    }
}

/// The nearest definition of `local` strictly before `(before_path,
/// before_def)` on the frame path: earlier definitions in the same block
/// first, then earlier blocks backwards.
fn find_def<'a>(
    facts: &'a FunctionFacts,
    bb_path: &[usize],
    before_path: usize,
    before_def: usize,
    local: usize,
) -> Option<(usize, usize, &'a DefRecord)> {
    let bb = *bb_path.get(before_path)?;
    if let Some(block) = facts.bb(bb) {
        let limit = before_def.min(block.defs.len());
        for index in (0..limit).rev() {
            if block.defs[index].local == local {
                return Some((before_path, index, &block.defs[index]));
            }
        }
    }
    for pos in (0..before_path).rev() {
        if let Some(block) = facts.bb(bb_path[pos]) {
            for index in (0..block.defs.len()).rev() {
                if block.defs[index].local == local {
                    return Some((pos, index, &block.defs[index]));
                }
            }
        }
    }
    None
}
