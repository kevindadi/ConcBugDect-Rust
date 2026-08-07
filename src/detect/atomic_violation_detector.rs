use std::array;
use std::collections::{BTreeMap, BTreeSet};

use rustc_data_structures::fx::FxHashSet;

use crate::concurrency::atomic::AtomicOrdering;
use crate::memory::pointsto::AliasId;
use crate::net::core::Net;
use crate::net::ids::{PlaceId, TransitionId};
use crate::net::index_vec::{Idx, IndexVec};
use crate::net::structure::{Marking, Transition, TransitionType};

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
    #[allow(unused)]
    ord: AtomicOrdering,
    #[allow(unused)]
    span: String,
    #[allow(unused)]
    transition: TransitionId,
}

fn parse_event(tr: &Transition, transition_id: TransitionId) -> Option<Ev> {
    match &tr.transition_type {
        TransitionType::AtomicLoad(alias, order, span, tid) => Some(Ev {
            tid: *tid,
            alias: *alias,
            kind: EvKind::Load,
            ord: *order,
            span: span.clone(),
            transition: transition_id,
        }),
        TransitionType::AtomicStore(alias, order, span, tid) => Some(Ev {
            tid: *tid,
            alias: *alias,
            kind: EvKind::Store,
            ord: *order,
            span: span.clone(),
            transition: transition_id,
        }),
        TransitionType::AtomicCmpXchg(alias, success, _failure, span, tid) => Some(Ev {
            tid: *tid,
            alias: *alias,
            kind: EvKind::Store,
            ord: *success,
            span: span.clone(),
            transition: transition_id,
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
    Rule {
        id: 0,
        start: EvKind::Load,
        mid: EvKind::Store,
        end: EvKind::Store,
    },
    Rule {
        id: 1,
        start: EvKind::Store,
        mid: EvKind::Store,
        end: EvKind::Load,
    },
    Rule {
        id: 2,
        start: EvKind::Load,
        mid: EvKind::Store,
        end: EvKind::Load,
    },
];

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Witness {
    AV1 {
        alias: AliasId,
        tid_i: usize,
        tid_j: usize,
        trace_slice: Vec<TransitionId>,
    },
    AV2 {
        alias: AliasId,
        tid_i: usize,
        tid_j: usize,
        trace_slice: Vec<TransitionId>,
    },
    AV3 {
        alias: AliasId,
        tid_i: usize,
        tid_j: usize,
        trace_slice: Vec<TransitionId>,
    },
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
    marking: Marking,
    trace: Vec<TransitionId>,
    pattern_states: [PatternState; RULES.len()],
}

impl Frame {
    fn new(marking: Marking) -> Self {
        Self {
            marking,
            trace: Vec::new(),
            pattern_states: array::from_fn(|_| PatternState::default()),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct StateFingerprint {
    marking: Vec<u64>,
    last_starts: Vec<(usize, usize, usize, usize, usize)>,
    saw_entries: Vec<(usize, usize, usize, usize, usize, usize)>,
}

impl StateFingerprint {
    fn from_frame(net: &Net, frame: &Frame) -> Self {
        let marking = marking_key(net, &frame.marking);

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
            marking,
            last_starts,
            saw_entries,
        }
    }
}

pub fn detect_atomicity_violations(
    net: &Net,
    init: &Marking,
    max_states: usize,
    max_depth: usize,
) -> Vec<Witness> {
    if max_states == 0 {
        return Vec::new();
    }

    let mut witnesses = Vec::new();
    let mut seen: BTreeSet<(usize, TransitionId, TransitionId, TransitionId)> = BTreeSet::new();
    let mut visited: FxHashSet<StateFingerprint> = FxHashSet::default();

    let mut stack = vec![Frame::new(init.clone())];

    while let Some(frame) = stack.pop() {
        if visited.len() >= max_states || frame.trace.len() >= max_depth {
            continue;
        }

        let fingerprint = StateFingerprint::from_frame(net, &frame);
        if !visited.insert(fingerprint) {
            continue;
        }

        let mut enabled = net.enabled_transitions(&frame.marking);
        enabled.sort_by_key(|tid| tid.index());

        for transition_id in enabled {
            if frame.trace.len() >= max_depth || visited.len() >= max_states {
                continue;
            }

            let fired = match net.fire_transition(&frame.marking, transition_id) {
                Ok(next) => next,
                Err(_) => continue,
            };

            let mut next_frame = frame.clone();
            next_frame.marking = fired;
            next_frame.trace.push(transition_id);

            if let Some(event) = parse_event(&net.transitions[transition_id], transition_id) {
                for rule in RULES.iter() {
                    try_match(&mut next_frame, rule, &event, &mut witnesses, &mut seen);
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
                        let slice = frame.trace[start_idx..=current_idx].to_vec();
                        let start_tr = frame.trace[start_idx];
                        let mid_tr = frame.trace[mid_idx];
                        let end_tr = frame.trace[current_idx];
                        if seen.insert((rule.id, start_tr, mid_tr, end_tr)) {
                            let witness = match rule.id {
                                0 => Witness::AV1 {
                                    alias: ev.alias,
                                    tid_i: ev.tid,
                                    tid_j,
                                    trace_slice: slice,
                                },
                                1 => Witness::AV2 {
                                    alias: ev.alias,
                                    tid_i: ev.tid,
                                    tid_j,
                                    trace_slice: slice,
                                },
                                2 => Witness::AV3 {
                                    alias: ev.alias,
                                    tid_i: ev.tid,
                                    tid_j,
                                    trace_slice: slice,
                                },
                                _ => unreachable!(),
                            };
                            out.push(witness);
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

fn print_trace(net: &Net, trace_slice: &[TransitionId]) {
    for (pos, transition_id) in trace_slice.iter().enumerate() {
        let transition = &net.transitions[*transition_id];
        match &transition.transition_type {
            TransitionType::AtomicLoad(alias, ord, span, tid) => println!(
                "    [{:03}] LOAD  a={:?} ord={:?} tid={} @{}",
                pos, alias, ord, tid, span
            ),
            TransitionType::AtomicStore(alias, ord, span, tid) => println!(
                "    [{:03}] STORE a={:?} ord={:?} tid={} @{}",
                pos, alias, ord, tid, span
            ),
            TransitionType::AtomicCmpXchg(alias, succ, fail, span, tid) => println!(
                "    [{:03}] CAS   a={:?} succ={:?} fail={:?} tid={} @{}",
                pos, alias, succ, fail, tid, span
            ),
            other => println!("    [{:03}] {:?} ({})", pos, other, transition.name),
        }
    }
}

pub fn print_witnesses(net: &Net, witnesses: &[Witness]) {
    if witnesses.is_empty() {
        println!("[atomic-violation] No violations found.");
        return;
    }

    println!("[atomic-violation] {} violation(s) found.", witnesses.len());

    for (idx, witness) in witnesses.iter().enumerate() {
        match witness {
            Witness::AV1 {
                alias,
                tid_i,
                tid_j,
                trace_slice,
            } => {
                println!(
                    "  #{} AV1 alias={:?} load_tid={} intruder_tid={} slice_len={}",
                    idx,
                    alias,
                    tid_i,
                    tid_j,
                    trace_slice.len()
                );
                print_trace(net, trace_slice);
            }
            Witness::AV2 {
                alias,
                tid_i,
                tid_j,
                trace_slice,
            } => {
                println!(
                    "  #{} AV2 alias={:?} store_tid={} intruder_tid={} slice_len={}",
                    idx,
                    alias,
                    tid_i,
                    tid_j,
                    trace_slice.len()
                );
                print_trace(net, trace_slice);
            }
            Witness::AV3 {
                alias,
                tid_i,
                tid_j,
                trace_slice,
            } => {
                println!(
                    "  #{} AV3 alias={:?} load_tid={} intruder_tid={} slice_len={}",
                    idx,
                    alias,
                    tid_i,
                    tid_j,
                    trace_slice.len()
                );
                print_trace(net, trace_slice);
            }
        }
    }
}

pub fn marking_from_places(net: &Net) -> Marking {
    let tokens: Vec<u64> = net
        .places
        .iter_enumerated()
        .map(|(_, place)| place.tokens)
        .collect();
    Marking(IndexVec::<PlaceId, u64>::from_vec(tokens))
}

pub fn marking_key(net: &Net, marking: &Marking) -> Vec<u64> {
    net.places
        .iter_enumerated()
        .map(|(place_id, _)| marking.tokens(place_id))
        .collect()
}

pub fn run_atomic_violation_check(net: &Net) {
    let init = marking_from_places(net);
    let witnesses = detect_atomicity_violations(net, &init, 200_000, 10_000);
    print_witnesses(net, &witnesses);
}
