//! Unified atomicity-violation detector.
//!
//! Runs the classic AV1/AV2/AV3 witness search over the *shared* state graph
//! instead of re-exploring the Petri net, so all detectors consume a single
//! reachability graph. Memory-ordering constraints are enforced structurally by
//! the ordering-segment places in the net, so the witness search itself only
//! matches load/store kinds and thread/alias identity.

use unipn::analysis::pt::reachability::StateGraph;
use crate::concurrency::atomic::AtomicOrdering;
use crate::memory::pointsto::AliasId;
use unipn::TransitionId;
use unipn::pt::TransitionType;
use crate::report::{AtomicOperation, AtomicReport, ViolationPattern};
use petgraph::Direction;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rustc_data_structures::fx::FxHashSet;
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

const DEFAULT_MAX_STATES: usize = 200_000;
const DEFAULT_MAX_DEPTH: usize = 10_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvKind {
    Load,
    Store,
}

#[derive(Debug, Clone)]
struct Ev {
    tid: usize,
    alias: AliasId,
    kind: EvKind,
    ord: AtomicOrdering,
    span: String,
}

fn parse_event(transition_type: &TransitionType) -> Option<Ev> {
    match transition_type {
        TransitionType::AtomicLoad(alias, order, span, tid) => Some(Ev {
            tid: *tid,
            alias: *alias,
            kind: EvKind::Load,
            ord: *order,
            span: span.clone(),
        }),
        TransitionType::AtomicStore(alias, order, span, tid) => Some(Ev {
            tid: *tid,
            alias: *alias,
            kind: EvKind::Store,
            ord: *order,
            span: span.clone(),
        }),
        TransitionType::AtomicCmpXchg(alias, success, _failure, span, tid) => Some(Ev {
            tid: *tid,
            alias: *alias,
            kind: EvKind::Store,
            ord: *success,
            span: span.clone(),
        }),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy)]
struct Rule {
    id: usize,
    start: EvKind,
    mid: EvKind,
    end: EvKind,
}

const RULES: [Rule; 3] = [
    // AV1: read, then an intruding write between read and the writer's write.
    Rule {
        id: 0,
        start: EvKind::Load,
        mid: EvKind::Store,
        end: EvKind::Store,
    },
    // AV2: write, an intruding write, then the original thread's read.
    Rule {
        id: 1,
        start: EvKind::Store,
        mid: EvKind::Store,
        end: EvKind::Load,
    },
    // AV3: read, an intruding write, then the original thread's read.
    Rule {
        id: 2,
        start: EvKind::Load,
        mid: EvKind::Store,
        end: EvKind::Load,
    },
];

#[derive(Debug, Clone)]
enum WitnessKind {
    Av1,
    Av2,
    Av3,
}

#[derive(Debug, Clone)]
struct Witness {
    kind: WitnessKind,
    start: Ev,
    mid: Ev,
    end: Ev,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct AliasKey {
    instance: usize,
    local: usize,
}

impl AliasKey {
    fn new(alias: AliasId) -> Self {
        Self {
            instance: alias.instance_id.index(),
            local: alias.local.index(),
        }
    }
}

#[derive(Clone, Default)]
struct PatternState {
    last_start: BTreeMap<(AliasKey, usize), usize>,
    saw_mid_after_start: BTreeMap<(AliasKey, usize), BTreeMap<usize, usize>>,
}

#[derive(Clone)]
struct Frame {
    node: NodeIndex,
    trace: Vec<TransitionId>,
    events: Vec<Option<Ev>>,
    pattern_states: [PatternState; RULES.len()],
}

impl Frame {
    fn new(node: NodeIndex) -> Self {
        Self {
            node,
            trace: Vec::new(),
            events: Vec::new(),
            pattern_states: std::array::from_fn(|_| PatternState::default()),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct StateFingerprint {
    node: NodeIndex,
    last_starts: Vec<(usize, usize, usize, usize, usize)>,
    saw_entries: Vec<(usize, usize, usize, usize, usize, usize)>,
}

impl StateFingerprint {
    fn from_frame(frame: &Frame) -> Self {
        let mut last_starts = Vec::new();
        let mut saw_entries = Vec::new();

        for (rule_idx, state) in frame.pattern_states.iter().enumerate() {
            for ((alias_key, tid_i), start_idx) in state.last_start.iter() {
                last_starts.push((
                    rule_idx,
                    alias_key.instance,
                    alias_key.local,
                    *tid_i,
                    *start_idx,
                ));
            }
            for ((alias_key, tid_i), intruders) in state.saw_mid_after_start.iter() {
                for (&tid_j, &mid_idx) in intruders.iter() {
                    saw_entries.push((
                        rule_idx,
                        alias_key.instance,
                        alias_key.local,
                        *tid_i,
                        tid_j,
                        mid_idx,
                    ));
                }
            }
        }

        last_starts.sort_unstable();
        saw_entries.sort_unstable();

        Self {
            node: frame.node,
            last_starts,
            saw_entries,
        }
    }
}

fn detect_witnesses(state_graph: &StateGraph, max_states: usize, max_depth: usize) -> Vec<Witness> {
    if max_states == 0 {
        return Vec::new();
    }

    let graph = &state_graph.graph;
    let mut witnesses = Vec::new();
    let mut seen: BTreeSet<(usize, TransitionId, TransitionId, TransitionId)> = BTreeSet::new();
    let mut visited: FxHashSet<StateFingerprint> = FxHashSet::default();

    let mut stack = vec![Frame::new(state_graph.initial)];

    while let Some(frame) = stack.pop() {
        if visited.len() >= max_states || frame.trace.len() >= max_depth {
            continue;
        }

        let fingerprint = StateFingerprint::from_frame(&frame);
        if !visited.insert(fingerprint) {
            continue;
        }

        let mut edges: Vec<_> = graph
            .edges_directed(frame.node, Direction::Outgoing)
            .collect();
        edges.sort_by_key(|edge| edge.weight().transition.id.index());

        for edge in edges {
            if frame.trace.len() >= max_depth || visited.len() >= max_states {
                continue;
            }

            let transition = &edge.weight().transition;
            let mut next_frame = frame.clone();
            next_frame.node = edge.target();
            next_frame.trace.push(transition.id);

            let event = parse_event(&transition.transition_type);
            next_frame.events.push(event.clone());

            if let Some(event) = &event {
                for rule in RULES.iter() {
                    try_match(&mut next_frame, rule, event, &mut witnesses, &mut seen);
                }
            }

            stack.push(next_frame);
        }
    }

    witnesses
}

fn try_match(
    frame: &mut Frame,
    rule: &Rule,
    ev: &Ev,
    out: &mut Vec<Witness>,
    seen: &mut BTreeSet<(usize, TransitionId, TransitionId, TransitionId)>,
) {
    let current_idx = frame.trace.len().saturating_sub(1);
    let alias_key = AliasKey::new(ev.alias);
    let state = &mut frame.pattern_states[rule.id];
    let key = (alias_key, ev.tid);

    if ev.kind == rule.end {
        if let Some(&start_idx) = state.last_start.get(&key) {
            if let Some(intruders) = state.saw_mid_after_start.get_mut(&key) {
                let mut to_remove = Vec::new();
                for (&tid_j, &mid_idx) in intruders.iter() {
                    if start_idx < mid_idx && mid_idx < current_idx {
                        let start_tr = frame.trace[start_idx];
                        let mid_tr = frame.trace[mid_idx];
                        let end_tr = frame.trace[current_idx];
                        if seen.insert((rule.id, start_tr, mid_tr, end_tr)) {
                            let kind = match rule.id {
                                0 => WitnessKind::Av1,
                                1 => WitnessKind::Av2,
                                2 => WitnessKind::Av3,
                                _ => unreachable!(),
                            };
                            out.push(Witness {
                                kind,
                                start: frame.events[start_idx]
                                    .clone()
                                    .expect("trace event must be present"),
                                mid: frame.events[mid_idx]
                                    .clone()
                                    .expect("trace event must be present"),
                                end: ev.clone(),
                            });
                        }
                        to_remove.push(tid_j);
                    }
                }
                for tid_j in to_remove {
                    intruders.remove(&tid_j);
                }
                if intruders.is_empty() {
                    state.saw_mid_after_start.remove(&key);
                }
            }
        }
    }

    if ev.kind == rule.mid {
        for ((start_key, tid_i), _) in state.last_start.iter() {
            if *start_key == alias_key && *tid_i != ev.tid {
                state
                    .saw_mid_after_start
                    .entry((*start_key, *tid_i))
                    .or_default()
                    .insert(ev.tid, current_idx);
            }
        }
    }

    if ev.kind == rule.start {
        state.last_start.insert(key, current_idx);
        state.saw_mid_after_start.remove(&key);
    }
}

/// Look up the `Ev` recorded for a position in the trace. Every trace position
/// that produced an atomic event stored it alongside the transition id, so
/// start and mid events are recoverable when a witness completes.
pub struct AtomicityViolationDetector<'a> {
    state_graph: &'a StateGraph,
    max_states: usize,
    max_depth: usize,
}

impl<'a> AtomicityViolationDetector<'a> {
    pub fn new(state_graph: &'a StateGraph) -> Self {
        Self {
            state_graph,
            max_states: DEFAULT_MAX_STATES,
            max_depth: DEFAULT_MAX_DEPTH,
        }
    }

    pub fn with_limits(state_graph: &'a StateGraph, max_states: usize, max_depth: usize) -> Self {
        Self {
            state_graph,
            max_states,
            max_depth,
        }
    }

    pub fn detect(&self) -> AtomicReport {
        let start_time = Instant::now();
        let mut report = AtomicReport::new("Petri Net Atomicity Violation Detector".to_string());

        let witnesses = detect_witnesses(self.state_graph, self.max_states, self.max_depth);

        if !witnesses.is_empty() {
            report.has_violation = true;
            report.violations = dedupe_patterns(&witnesses);
            report.violation_count = report.violations.len();
        }

        report.analysis_time = start_time.elapsed();
        report
    }
}

fn atomic_op(operation_type: &str, ev: &Ev) -> AtomicOperation {
    AtomicOperation {
        operation_type: operation_type.to_string(),
        ordering: format!("{:?}", ev.ord),
        variable: format!("{:?}", ev.alias),
        location: ev.span.clone(),
    }
}

fn dedupe_patterns(witnesses: &[Witness]) -> Vec<ViolationPattern> {
    let mut patterns = Vec::new();

    for witness in witnesses {
        let (load, stores) = match witness.kind {
            WitnessKind::Av1 => (
                atomic_op(&format!("load@tid{}", witness.start.tid), &witness.start),
                vec![
                    atomic_op(&format!("store@tid{}", witness.mid.tid), &witness.mid),
                    atomic_op(&format!("store@tid{}", witness.end.tid), &witness.end),
                ],
            ),
            WitnessKind::Av2 => (
                atomic_op(&format!("load@tid{}", witness.end.tid), &witness.end),
                vec![
                    atomic_op(&format!("store@tid{}", witness.start.tid), &witness.start),
                    atomic_op(&format!("store@tid{}", witness.mid.tid), &witness.mid),
                ],
            ),
            WitnessKind::Av3 => (
                atomic_op(&format!("load@tid{}", witness.start.tid), &witness.start),
                vec![atomic_op(
                    &format!("store@tid{}", witness.mid.tid),
                    &witness.mid,
                )],
            ),
        };

        let pattern = ViolationPattern {
            load_op: load,
            store_ops: stores,
        };
        if !patterns.contains(&pattern) {
            patterns.push(pattern);
        }
    }

    patterns
}

#[cfg(test)]
mod tests {
    use super::*;
    use unipn::analysis::pt::reachability::StateGraph;
    use crate::concurrency::atomic::AtomicOrdering;
    use crate::net::Net;
    use unipn::pt::{PtPlace, PlaceType, PtTransition, TransitionType};
    use petgraph::graph::NodeIndex;
    use rustc_middle::mir::Local;

    fn build_atomic_violation_net() -> Net {
        let mut net = Net::empty();
        let shared = net.add_place(Place::new(
            "shared_atomic",
            1,
            1,
            PlaceType::BasicBlock,
            "atomic.rs:1:1".into(),
        ));

        let alias = AliasId::new(NodeIndex::new(0), Local::from_usize(0));

        let store_a = net.add_transition(Transition::new_with_transition_type(
            "store_a",
            TransitionType::AtomicStore(alias, AtomicOrdering::Release, "atomic.rs:10:5".into(), 1),
        ));
        let store_b = net.add_transition(Transition::new_with_transition_type(
            "store_b",
            TransitionType::AtomicStore(alias, AtomicOrdering::SeqCst, "atomic.rs:12:5".into(), 2),
        ));
        let load = net.add_transition(Transition::new_with_transition_type(
            "load_relaxed",
            TransitionType::AtomicLoad(alias, AtomicOrdering::Relaxed, "atomic.rs:20:5".into(), 1),
        ));

        for transition in [store_a, store_b, load] {
            net.set_input_weight(shared, transition, 1);
            net.set_output_weight(shared, transition, 1);
        }

        net
    }

    #[test]
    fn detect_atomicity_violation() {
        let net = build_atomic_violation_net();
        let state_graph = StateGraph::from_net(&net);
        // The test net is a single marking with self-loops; small limits keep
        // the pathological reachable space bounded while still finding the
        // witness (which completes at depth 3).
        let detector = AtomicityViolationDetector::with_limits(&state_graph, 1_000, 8);
        let report = detector.detect();

        assert!(report.has_violation, "Expected atomicity violation");
        assert!(!report.violations.is_empty());
    }
}
