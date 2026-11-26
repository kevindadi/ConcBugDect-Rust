//! Deadlock selection, σ reconstruction, and the `deadlocks.json` object.

use std::collections::VecDeque;

use serde_json::{Value, json};
use unipn::analysis::pt::reachability::StateGraph;
use unipn::net::TransitionId;

use super::json::{blocked_place_json, sigma_step_json};
use super::{
    DeadlockData, MAX_REPORTED_DEADLOCKS, MAX_SIGMA_STEPS, RawTrans, ReportInputs, SCHEMA,
    SigmaStep,
};

/// Build the `deadlocks.json` value. Deterministic for a given input: states
/// are visited in the sorted order `deadlock_states` returns and every lookup
/// walks a `Vec` in index order.
pub fn build_deadlock_report(inputs: &ReportInputs) -> Value {
    let deadlock_states = inputs.state_graph.deadlock_states(inputs.net);
    let reported = reported_state_indices(inputs).len();
    let deadlocks: Vec<Value> = reported_deadlocks(inputs)
        .iter()
        .map(|data| deadlock_json(inputs, data))
        .collect();

    let mut state_graph_json = json!({
        "states": inputs.state_graph.states.len(),
        "edges": inputs.state_graph.edges.len(),
        "blocked": inputs.state_graph.blocked.len(),
        "deadlock_count": deadlock_states.len(),
        "reported": reported,
        "truncated": inputs.state_graph.truncated,
        "frontier_states": frontier_state_count(inputs.state_graph),
    });
    // Fields are only added when refinements actually excluded something, so
    // a run without `--exclude-candidates` stays byte-identical.
    if !inputs.excluded.is_empty() {
        state_graph_json["excluded_count"] = json!(inputs.excluded.len());
        state_graph_json["excluded"] = json!(inputs.excluded.iter().collect::<Vec<_>>());
    }

    let mut report = json!({
        "schema": SCHEMA,
        "crate": inputs.crate_name,
        "net": net_json(inputs),
        "state_graph": state_graph_json,
        "deadlocks": deadlocks,
    });
    // Library-mode per-entry slicing : additive, and only present
    // when the graph really was sliced, so the main-mode report stays
    // byte-identical.
    if let Some(layout) = inputs.slice_layout {
        let slices: Vec<Value> = layout
            .slices
            .iter()
            .map(|slice| {
                json!({
                    "entry_roots": slice.entry_roots,
                    "initial_state": slice.initial_state,
                    "states": slice.states,
                    "edges": slice.edges,
                    "blocked": slice.blocked,
                    "deadlocks": slice.deadlocks,
                    "truncated": slice.truncated,
                    "frontier_states": slice.frontier_states,
                })
            })
            .collect();
        let mut slicing = json!({
            "schema": "pn-library-slicing/1",
            "slice_count": layout.slices.len(),
            "slices": slices,
        });
        // Present only when a global slice state budget stopped the sweep,
        // so unbudgeted reports stay byte-identical.
        if layout.unexplored_slices > 0 {
            slicing["unexplored_slices"] = json!(layout.unexplored_slices);
            slicing["state_budget_stopped"] = json!(true);
        }
        report["slicing"] = slicing;
    }
    report
}

/// The deadlock states the report spells out, in state-index order: the
/// states `deadlock_states` returns, minus the excluded candidates, capped at
/// [`MAX_REPORTED_DEADLOCKS`]. Every report (`deadlocks.json`,
/// `predicates.json`, `expected-trace.json`) goes through this function, so
/// the candidate set can never drift between them.
pub fn reported_state_indices(inputs: &ReportInputs) -> Vec<usize> {
    inputs
        .state_graph
        .deadlock_states(inputs.net)
        .into_iter()
        .filter(|state| !inputs.excluded.contains(state))
        .take(MAX_REPORTED_DEADLOCKS)
        .collect()
}

/// The deadlocks the report spells out, in report order (sorted by
/// `state_index`, capped at [`MAX_REPORTED_DEADLOCKS`]) and with their σ
/// already reconstructed — the structured form of the `deadlocks` array.
pub fn reported_deadlocks(inputs: &ReportInputs) -> Vec<DeadlockData> {
    let reported = reported_state_indices(inputs);
    let predecessor = predecessor_table(inputs.state_graph);
    reported
        .iter()
        .map(|&state_index| {
            let (sigma, sigma_truncated) = sigma_steps(inputs, &predecessor, state_index);
            DeadlockData {
                state_index,
                sigma,
                sigma_truncated,
                entry_roots: inputs
                    .slice_layout
                    .and_then(|layout| layout.slice_of(state_index))
                    .map(|slice| slice.entry_roots.clone())
                    .unwrap_or_default(),
            }
        })
        .collect()
}

fn net_json(inputs: &ReportInputs) -> Value {
    let mut net = json!({
        "places": inputs.net.num_places(),
        "transitions": inputs.net.num_transitions(),
        "arcs": inputs.net.arcs().len(),
        "reduced": inputs.reduce_trace.is_some(),
        "raw_places": inputs.raw_net.num_places(),
        "raw_transitions": inputs.raw_net.num_transitions(),
        "raw_arcs": inputs.raw_net.arcs().len(),
    });
    // Additive field, library mode only: a main-mode report must stay
    // byte-identical (hard gate), so `"main"` is represented by absence.
    if inputs.entry_mode != "main" {
        net["entry_mode"] = json!(inputs.entry_mode);
    }
    net
}

/// Count the truncation-frontier states of `graph`: states with no recorded
/// outgoing edge that are not in `blocked`.
///
/// In a complete exploration a state without successors has no enabled
/// transition, so it is in `blocked`. A non-blocked sink therefore exists only
/// because the state limit stopped the expansion there. The count is 0 for
/// every non-truncated graph.
pub fn frontier_state_count(graph: &StateGraph) -> usize {
    let mut has_successor = vec![false; graph.states.len()];
    for (from, _, _) in &graph.edges {
        if let Some(slot) = has_successor.get_mut(*from) {
            *slot = true;
        }
    }
    graph
        .states
        .iter()
        .enumerate()
        .filter(|(index, _)| !has_successor[*index] && !graph.blocked.contains(index))
        .count()
}

fn deadlock_json(inputs: &ReportInputs, data: &DeadlockData) -> Value {
    let state_index = data.state_index;
    let blocked_places: Vec<Value> = match inputs.state_graph.states.get(state_index) {
        Some(state) => inputs
            .net
            .blocked_places(&state.marking)
            .into_iter()
            .map(|place| blocked_place_json(inputs.net, &state.marking, place))
            .collect(),
        None => {
            log::error!("deadlock report: state index {state_index} is out of range");
            Vec::new()
        }
    };
    let sigma: Vec<Value> = data.sigma.iter().map(sigma_step_json).collect();

    let mut deadlock = json!({
        "state_index": state_index,
        "blocked_places": blocked_places,
        "sigma": sigma,
        "sigma_truncated": data.sigma_truncated,
    });
    // Additive, sliced library runs only. `entry_roots` is the authoritative
    // set (an equivalence class may hold several roots); `entry_root` is the
    // single function name for a singleton slice and the `"a + b"` class label
    // otherwise, so every sliced candidate carries the tag the spec asks for.
    if !data.entry_roots.is_empty() {
        let entry_root = if data.entry_roots.len() == 1 {
            data.entry_roots[0].clone()
        } else {
            data.entry_roots.join(" + ")
        };
        deadlock["entry_root"] = json!(entry_root);
        deadlock["entry_roots"] = json!(data.entry_roots);
    }
    deadlock
}

/// For every target state, the *first* edge (in storage order) that reaches
/// it. Exploration inserts a state's discovery edges in BFS order, so the
/// first edge into a state is a shortest-path parent, and taking the first
/// keeps the choice deterministic.
fn predecessor_table(sg: &StateGraph) -> Vec<Option<usize>> {
    let mut predecessor: Vec<Option<usize>> = vec![None; sg.states.len()];
    for (edge_index, (_, to, _)) in sg.edges.iter().enumerate() {
        if predecessor.get(*to).is_some_and(|parent| parent.is_none()) {
            predecessor[*to] = Some(edge_index);
        }
    }
    predecessor
}

/// The sequence σ from the initial state to `deadlock_state`, structured.
///
/// The state graph has no predecessor table, so one is derived from the edge
/// list (see [`predecessor_table`]).
///
/// The walk back from the deadlock state collects steps in
/// deadlock→initial order; a chain longer than [`MAX_SIGMA_STEPS`] drops the
/// steps nearest the deadlock, so a truncated σ still *starts at the initial
/// state* and every reported step stays replayable — only the tail is missing.
/// Returns the steps in initial→deadlock order and whether truncation (or a
/// broken chain) happened.
fn sigma_steps(
    inputs: &ReportInputs,
    predecessor: &[Option<usize>],
    deadlock_state: usize,
) -> (Vec<SigmaStep>, bool) {
    let sg = inputs.state_graph;
    // A sliced library graph is a disjoint union of per-root components, so it
    // has one initial state per slice; stop at the deadlock's own slice start.
    // A joint graph keeps the single `StateGraph::initial`.
    let initial = inputs
        .slice_layout
        .and_then(|layout| layout.initial_state_of(deadlock_state))
        .unwrap_or(sg.initial);

    let mut chain: VecDeque<usize> = VecDeque::new();
    let mut truncated = false;
    let mut current = deadlock_state;
    while current != initial {
        let Some(edge_index) = predecessor.get(current).copied().flatten() else {
            log::error!(
                "deadlock report: no predecessor path from state {current} to the initial state"
            );
            truncated = true;
            break;
        };
        chain.push_back(edge_index);
        if chain.len() > MAX_SIGMA_STEPS {
            chain.pop_front();
            truncated = true;
        }
        current = sg.edges[edge_index].0;
    }

    let steps: Vec<SigmaStep> = chain
        .iter()
        .rev()
        .enumerate()
        .map(|(step, &edge_index)| {
            let (from, to, edge) = &sg.edges[edge_index];
            SigmaStep {
                step,
                from_state: *from,
                to_state: *to,
                transition_id: edge.transition.id,
                name: edge.transition.name.clone(),
                transition_type: edge.transition.transition_type.clone(),
                raw: raw_transitions(inputs, edge.transition.id),
            }
        })
        .collect();

    (steps, truncated)
}

/// Lift one state-graph transition to the original transitions it stands for.
///
/// `transition_mapping` is indexed by the *reduced* net's transition id and
/// holds the original ids in merge order — for a sequence merge, head first
/// (verified by `trace_lifting_round_trips`). Without a reduction (or with an
/// id the trace does not cover) the step lifts to itself.
fn raw_transitions(inputs: &ReportInputs, transition: TransitionId) -> Vec<RawTrans> {
    let originals: Vec<TransitionId> = match inputs.reduce_trace {
        Some(trace) => match trace.transition_mapping.get(transition.index()) {
            Some(list) if !list.is_empty() => list.clone(),
            _ => {
                log::error!(
                    "deadlock report: no reduction mapping for transition {}",
                    transition.index()
                );
                vec![transition]
            }
        },
        None => vec![transition],
    };

    originals
        .iter()
        .map(|&id| {
            let name = match inputs.raw_net.transition(id) {
                Some(t) => t.name.clone(),
                None => {
                    log::error!(
                        "deadlock report: original transition {} is out of range",
                        id.index()
                    );
                    String::new()
                }
            };
            RawTrans {
                transition_id: id,
                name,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::super::fixture::{add_t, bb, end, report_of, res, state_graph};
    use super::super::{
        NO_EXCLUSIONS, ReportInputs, build_deadlock_report, reported_state_indices,
    };
    use serde_json::json;
    use unipn::net::{Marking, PlaceId};
    use unipn::pt::{PtBuilder, PtNet, TransitionType};

    /// Two threads, two mutexes, crossed acquisition order. The blocked
    /// control places are parked before `Lock(n)` acquires, so under UniPN's
    /// `TransitionRole::is_blocking_wait` (only `Wait`/`Join`) they are *not*
    /// wait points — the wait they describe is an acquire, which the
    /// `outgoing` list shows; `wait_point_is_diagnosed` covers the positive
    /// `is_wait_point` side.
    /// Candidate exclusions are report-side only. The excluded
    /// state disappears from `deadlocks[]`, `reported` drops, the new
    /// `state_graph.excluded*` fields appear, and `deadlock_count` still
    /// counts every deadlock. Without exclusions the report has neither field
    /// (the byte gate for runs without `--exclude-candidates`).
    #[test]
    fn candidate_exclusions_filter_the_reported_list_only() {
        let (net, m0) = crossed_locks_net();
        let sg = state_graph(&net, &m0);
        let deadlocks = sg.deadlock_states(&net);
        assert!(!deadlocks.is_empty(), "the lock-order net has deadlocks");
        let total = deadlocks.len();

        let plain = build_deadlock_report(&ReportInputs {
            crate_name: "exclusions",
            raw_net: &net,
            net: &net,
            state_graph: &sg,
            reduce_trace: None,
            excluded: &NO_EXCLUSIONS,
            entry_mode: "main",
            slice_layout: None,
        });
        assert_eq!(plain["state_graph"]["deadlock_count"], total);
        assert_eq!(plain["state_graph"]["reported"], total);
        assert_eq!(plain["deadlocks"].as_array().unwrap().len(), total);
        assert!(plain["state_graph"].get("excluded").is_none());
        assert!(plain["state_graph"].get("excluded_count").is_none());

        let mut excluded = std::collections::BTreeSet::new();
        excluded.insert(deadlocks[0]);
        let filtered = build_deadlock_report(&ReportInputs {
            crate_name: "exclusions",
            raw_net: &net,
            net: &net,
            state_graph: &sg,
            reduce_trace: None,
            excluded: &excluded,
            entry_mode: "main",
            slice_layout: None,
        });
        assert_eq!(filtered["state_graph"]["deadlock_count"], total);
        assert_eq!(filtered["state_graph"]["reported"], total - 1);
        assert_eq!(filtered["state_graph"]["excluded_count"], 1);
        assert_eq!(filtered["state_graph"]["excluded"][0], deadlocks[0]);
        let reported: Vec<u64> = filtered["deadlocks"]
            .as_array()
            .unwrap()
            .iter()
            .map(|deadlock| deadlock["state_index"].as_u64().unwrap())
            .collect();
        assert_eq!(reported.len(), total - 1);
        assert!(!reported.contains(&(deadlocks[0] as u64)));
        let indices = reported_state_indices(&ReportInputs {
            crate_name: "exclusions",
            raw_net: &net,
            net: &net,
            state_graph: &sg,
            reduce_trace: None,
            excluded: &excluded,
            entry_mode: "main",
            slice_layout: None,
        });
        assert_eq!(indices.len(), total - 1);
        assert!(!indices.contains(&deadlocks[0]));
    }

    /// Two threads, two locks, crossed order — one deadlock state whose
    /// candidate can be excluded in the test above.
    fn crossed_locks_net() -> (PtNet, Marking) {
        let mut b = PtBuilder::new();
        let l1 = b.add_marked_place("L1", res(), 1);
        let l2 = b.add_marked_place("L2", res(), 1);
        let a: Vec<PlaceId> = (0..3)
            .map(|i| {
                b.add_marked_place(
                    format!("a{i}"),
                    if i == 2 { end() } else { bb() },
                    usize::from(i == 0),
                )
            })
            .collect();
        let c: Vec<PlaceId> = (0..3)
            .map(|i| {
                b.add_marked_place(
                    format!("c{i}"),
                    if i == 2 { end() } else { bb() },
                    usize::from(i == 0),
                )
            })
            .collect();
        add_t(
            &mut b,
            "A lock L1",
            TransitionType::Lock(l1.index()),
            &[a[0], l1],
            &[a[1]],
        );
        add_t(
            &mut b,
            "A lock L2",
            TransitionType::Lock(l2.index()),
            &[a[1], l2],
            &[a[2]],
        );
        add_t(
            &mut b,
            "B lock L2",
            TransitionType::Lock(l2.index()),
            &[c[0], l2],
            &[c[1]],
        );
        add_t(
            &mut b,
            "B lock L1",
            TransitionType::Lock(l1.index()),
            &[c[1], l1],
            &[c[2]],
        );
        let (net, m0) = b.build();
        (net, m0)
    }

    /// A run in which both threads end normally is blocked, but not a deadlock.
    #[test]
    fn blocked_terminal_is_not_a_deadlock() {
        let mut b = PtBuilder::new();
        let a0 = b.add_marked_place("a0", bb(), 1);
        let a1 = b.add_place("a1", end());
        let c0 = b.add_marked_place("b0", bb(), 1);
        let c1 = b.add_place("b1", end());
        add_t(&mut b, "a end", TransitionType::Normal, &[a0], &[a1]);
        add_t(&mut b, "b end", TransitionType::Normal, &[c0], &[c1]);
        let (net, m0) = b.build();

        let sg = state_graph(&net, &m0);
        assert!(sg.stats().blocked_count >= 1, "the finished run is blocked");

        let report = report_of("blocked_terminal", &net, &sg);
        assert_eq!(report["state_graph"]["blocked"], 1);
        assert_eq!(report["state_graph"]["deadlock_count"], 0);
        assert_eq!(report["state_graph"]["reported"], 0);
        assert_eq!(report["deadlocks"], json!([]));
    }

    #[test]
    fn report_is_deterministic() {
        let mut b = PtBuilder::new();
        let l1 = b.add_marked_place("L1", res(), 1);
        let l2 = b.add_marked_place("L2", res(), 1);
        let a0 = b.add_marked_place("a0", bb(), 1);
        let a1 = b.add_place("a1", bb());
        let a2 = b.add_place("a2", end());
        let c0 = b.add_marked_place("b0", bb(), 1);
        let c1 = b.add_place("b1", bb());
        let c2 = b.add_place("b2", end());
        add_t(
            &mut b,
            "A lock L1",
            TransitionType::Lock(l1.index()),
            &[a0, l1],
            &[a1],
        );
        add_t(
            &mut b,
            "A lock L2",
            TransitionType::Lock(l2.index()),
            &[a1, l2],
            &[a2],
        );
        add_t(
            &mut b,
            "B lock L2",
            TransitionType::Lock(l2.index()),
            &[c0, l2],
            &[c1],
        );
        add_t(
            &mut b,
            "B lock L1",
            TransitionType::Lock(l1.index()),
            &[c1, l1],
            &[c2],
        );
        let (net, m0) = b.build();

        let sg = state_graph(&net, &m0);
        let first = build_deadlock_report(&ReportInputs {
            crate_name: "determinism",
            raw_net: &net,
            net: &net,
            state_graph: &sg,
            reduce_trace: None,
            excluded: &NO_EXCLUSIONS,
            entry_mode: "main",
            slice_layout: None,
        });
        let second = build_deadlock_report(&ReportInputs {
            crate_name: "determinism",
            raw_net: &net,
            net: &net,
            state_graph: &sg,
            reduce_trace: None,
            excluded: &NO_EXCLUSIONS,
            entry_mode: "main",
            slice_layout: None,
        });
        assert_eq!(
            serde_json::to_string(&first).unwrap(),
            serde_json::to_string(&second).unwrap()
        );
    }

    /// A state whose expansion was cut by the state limit is a frontier
    /// state, not a blocked or deadlocked state. A complete run reports zero.
    #[test]
    fn frontier_states_separate_truncation_from_blocking() {
        use unipn::analysis::pt::reachability::{StateGraph, StateGraphConfig};

        let mut b = PtBuilder::new();
        let p0 = b.add_marked_place("p0", bb(), 1);
        let p1 = b.add_place("p1", end());
        add_t(&mut b, "step", TransitionType::Normal, &[p0], &[p1]);
        let (net, m0) = b.build();

        let truncated = StateGraph::with_config(
            &net,
            m0.clone(),
            StateGraphConfig {
                state_limit: Some(1),
                include_zero_tokens: false,
                use_por: false,
            },
        );
        assert!(truncated.truncated);
        assert!(truncated.blocked.is_empty(), "nothing is blocked, just cut");
        assert_eq!(truncated.deadlock_states(&net).len(), 0);
        assert_eq!(super::frontier_state_count(&truncated), 1);
        let report = report_of("frontier", &net, &truncated);
        assert_eq!(report["state_graph"]["frontier_states"], 1);
        assert_eq!(report["state_graph"]["blocked"], 0);
        assert_eq!(report["state_graph"]["deadlock_count"], 0);

        let complete = state_graph(&net, &m0);
        assert!(!complete.truncated);
        assert_eq!(super::frontier_state_count(&complete), 0);
        let report = report_of("frontier", &net, &complete);
        assert_eq!(report["state_graph"]["frontier_states"], 0);
    }

    /// A thread that unlocks before it reaches `FunctionEnd` is not a deadlock,
    /// even though the finished run is blocked.
    #[test]
    fn release_before_terminal_has_no_deadlock() {
        let mut b = PtBuilder::new();
        let l = b.add_marked_place("L", res(), 1);
        let a0 = b.add_marked_place("a0", bb(), 1);
        let a1 = b.add_place("a1", bb());
        let a2 = b.add_place("a2", end());
        let c0 = b.add_marked_place("b0", bb(), 1);
        let c1 = b.add_place("b1", bb());
        let c2 = b.add_place("b2", end());
        add_t(
            &mut b,
            "A lock",
            TransitionType::Lock(l.index()),
            &[a0, l],
            &[a1],
        );
        add_t(
            &mut b,
            "A unlock",
            TransitionType::Unlock(l.index()),
            &[a1],
            &[a2, l],
        );
        add_t(
            &mut b,
            "B lock",
            TransitionType::Lock(l.index()),
            &[c0, l],
            &[c1],
        );
        add_t(
            &mut b,
            "B unlock",
            TransitionType::Unlock(l.index()),
            &[c1],
            &[c2, l],
        );
        let (net, m0) = b.build();

        let sg = state_graph(&net, &m0);
        assert!(sg.stats().blocked_count >= 1, "the finished run is blocked");
        assert!(sg.deadlock_states(&net).is_empty());

        let report = report_of("release_before_terminal", &net, &sg);
        assert_eq!(report["state_graph"]["deadlock_count"], 0);
        assert_eq!(report["deadlocks"], json!([]));
    }
}
