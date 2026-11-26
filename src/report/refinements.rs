//! Loads report-side candidate exclusions from dynamic evidence.
//! An exclusion drops one candidate from the spelled-out list only.
//! It does not change the net, the state graph, or `deadlock_count`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde_json::Value;

/// Identifies the JSON shape; bumped when a field changes meaning.
pub const REFINEMENT_SCHEMA: &str = "pn-refinements/1";

/// The only reasons an exclusion may carry. `confirmed` / `inconclusive` are
/// deliberately absent: they must never be excluded.
pub const ALLOWED_REASONS: [&str; 2] = ["spurious-by-replay", "divergent"];

/// The candidate-level exclusions of one crate, with the reasons read from the
/// file (for logging and for the materials' symmetry with the input).
#[derive(Clone, Debug, Default)]
pub struct Refinements {
    pub excluded: BTreeSet<usize>,
    pub reasons: BTreeMap<usize, String>,
}

impl Refinements {
    pub fn is_empty(&self) -> bool {
        self.excluded.is_empty()
    }
}

/// Load `path` for `crate_name`, fail-open (see the module docs).
pub fn load_refinements(path: &Path, crate_name: &str) -> Refinements {
    let text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(err) => {
            log::error!(
                "refinements: cannot read {}: {err}; continuing without exclusions",
                path.display()
            );
            return Refinements::default();
        }
    };
    let value: Value = match serde_json::from_str(&text) {
        Ok(value) => value,
        Err(err) => {
            log::error!(
                "refinements: {} is not valid JSON: {err}; continuing without exclusions",
                path.display()
            );
            return Refinements::default();
        }
    };
    parse_refinements(&value, crate_name, path)
}

fn parse_refinements(value: &Value, crate_name: &str, path: &Path) -> Refinements {
    let mut refinements = Refinements::default();
    match value.get("schema").and_then(Value::as_str) {
        Some(schema) if schema == REFINEMENT_SCHEMA => {}
        other => {
            log::error!(
                "refinements: {} has schema {other:?}, want {REFINEMENT_SCHEMA:?}; \
                 continuing without exclusions",
                path.display()
            );
            return refinements;
        }
    }
    match value.get("crate").and_then(Value::as_str) {
        Some(name) if name == crate_name => {}
        other => {
            log::error!(
                "refinements: {} is for crate {other:?}, not {crate_name:?}; \
                 continuing without exclusions",
                path.display()
            );
            return refinements;
        }
    }

    let Some(entries) = value.get("excluded").and_then(Value::as_array) else {
        log::error!(
            "refinements: {} has no `excluded` array; continuing without exclusions",
            path.display()
        );
        return refinements;
    };
    for entry in entries {
        let state = entry.get("state_index").and_then(Value::as_u64);
        let reason = entry.get("reason").and_then(Value::as_str);
        let evidence = entry.get("evidence").and_then(Value::as_str);
        let (Some(state), Some(reason), Some(evidence)) = (state, reason, evidence) else {
            log::error!(
                "refinements: {} entry {entry} lacks state_index/reason/evidence; skipping it",
                path.display()
            );
            continue;
        };
        if !ALLOWED_REASONS.contains(&reason) {
            log::error!(
                "refinements: {} entry state {state} has reason {reason:?}, which is not \
                 an allowed exclusion reason {ALLOWED_REASONS:?}; skipping it",
                path.display()
            );
            continue;
        }
        if evidence.trim().is_empty() {
            log::error!(
                "refinements: {} entry state {state} has an empty evidence path; skipping it",
                path.display()
            );
            continue;
        }
        refinements.excluded.insert(state as usize);
        refinements
            .reasons
            .insert(state as usize, reason.to_string());
    }
    refinements
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn parse(value: Value) -> Refinements {
        parse_refinements(&value, "demo", Path::new("refinements.json"))
    }

    fn file_value(excluded: Value) -> Value {
        json!({
            "schema": REFINEMENT_SCHEMA,
            "crate": "demo",
            "excluded": excluded,
        })
    }

    #[test]
    fn accepted_reasons_are_excluded_and_recorded() {
        let refinements = parse(file_value(json!([
            {"state_index": 36, "reason": "spurious-by-replay", "evidence": "a.json"},
            {"state_index": 12, "reason": "divergent", "evidence": "b.json"},
        ])));
        assert_eq!(
            refinements.excluded.iter().copied().collect::<Vec<_>>(),
            vec![12, 36]
        );
        assert_eq!(refinements.reasons.get(&36).unwrap(), "spurious-by-replay");
    }

    #[test]
    fn disallowed_reasons_and_bad_entries_are_skipped() {
        let refinements = parse(file_value(json!([
            {"state_index": 1, "reason": "confirmed", "evidence": "a.json"},
            {"state_index": 2, "reason": "inconclusive", "evidence": "a.json"},
            {"state_index": 3, "reason": "spurious-by-replay", "evidence": ""},
            {"state_index": 4, "reason": "spurious-by-replay"},
            {"state_index": 5, "reason": "divergent", "evidence": "c.json"},
        ])));
        assert_eq!(
            refinements.excluded.iter().copied().collect::<Vec<_>>(),
            vec![5]
        );
    }

    #[test]
    fn wrong_schema_or_crate_is_fail_open() {
        assert!(parse(json!({"schema": "other/1", "crate": "demo", "excluded": []})).is_empty());
        assert!(
            parse(json!({
                "schema": REFINEMENT_SCHEMA,
                "crate": "another",
                "excluded": [{"state_index": 1, "reason": "divergent", "evidence": "x"}],
            }))
            .is_empty()
        );
    }

    #[test]
    fn missing_file_is_fail_open() {
        let refinements = load_refinements(Path::new("/nonexistent/pn-refinements.json"), "demo");
        assert!(refinements.is_empty());
    }
}
