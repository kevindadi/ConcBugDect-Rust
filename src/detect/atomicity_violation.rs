use crate::analysis::reachability::{StateEdge, StateGraph, StateNode};
use crate::concurrency::atomic::AtomicOrdering;
use crate::memory::pointsto::AliasId;
use crate::net::ids::TransitionId;
use crate::net::index_vec::Idx;
use crate::net::structure::TransitionType;
use crate::report::{AtomicOperation, AtomicReport, AtomicViolation, ViolationPattern};
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::{Direction, stable_graph::StableGraph};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use std::time::Instant;

pub struct AtomicityViolationDetector<'a> {
    state_graph: &'a StateGraph,
}

#[derive(Clone)]
struct AtomicOp {
    var_id: AliasId,
    ordering: AtomicOrdering,
    span: String,
    thread_id: usize,
}

impl<'a> AtomicityViolationDetector<'a> {
    pub fn new(state_graph: &'a StateGraph) -> Self {
        Self { state_graph }
    }

    pub fn detect(&self) -> AtomicReport {
        let start_time = Instant::now();
        let mut report = AtomicReport::new("Petri Net Atomicity Violation Detector".to_string());

        let (loads, stores) = self.collect_atomic_operations();

        let violations = self.check_violations(loads, stores);

        if !violations.is_empty() {
            report.has_violation = true;
            report.violation_count = violations.len();
            report.violations = violations;
        }

        report.analysis_time = start_time.elapsed();
        report
    }

    fn collect_atomic_operations(
        &self,
    ) -> (
        FxHashMap<TransitionId, AtomicOp>,
        FxHashMap<TransitionId, AtomicOp>,
    ) {
        let mut loads = FxHashMap::default();
        let mut stores = FxHashMap::default();

        for edge in self.state_graph.graph.edge_weights() {
            match &edge.transition.transition_type {
                TransitionType::AtomicLoad(var_id, ordering, span, thread_id) => {
                    loads.entry(edge.transition.id).or_insert(AtomicOp {
                        var_id: var_id.clone(),
                        ordering: *ordering,
                        span: span.clone(),
                        thread_id: *thread_id,
                    });
                }
                TransitionType::AtomicStore(var_id, ordering, span, thread_id) => {
                    stores.entry(edge.transition.id).or_insert(AtomicOp {
                        var_id: var_id.clone(),
                        ordering: *ordering,
                        span: span.clone(),
                        thread_id: *thread_id,
                    });
                }
                _ => {}
            }
        }
        (loads, stores)
    }

    fn check_violations(
        &self,
        loads: FxHashMap<TransitionId, AtomicOp>,
        stores: FxHashMap<TransitionId, AtomicOp>,
    ) -> Vec<ViolationPattern> {
        let mut all_violations = Vec::new();
        let graph = &self.state_graph.graph;

        for (load_trans, load_op) in loads {
            for state in graph.node_indices() {
                for edge in graph.edges_directed(state, Direction::Outgoing) {
                    if edge.weight().transition.id == load_trans {
                        if let Some(violation) =
                            Self::check_state_for_violation(graph, state, &load_op, &stores)
                        {
                            all_violations.push(violation);
                        }
                    }
                }
            }
        }

        let mut pattern_map: FxHashMap<ViolationPattern, Vec<Vec<(usize, u8)>>> =
            FxHashMap::default();

        for violation in all_violations {
            let pattern = ViolationPattern {
                load_op: AtomicOperation {
                    operation_type: "load".to_string(),
                    ordering: violation.pattern.load_op.ordering.clone(),
                    variable: violation.pattern.load_op.variable.clone(),
                    location: violation.pattern.load_op.location.clone(),
                },
                store_ops: violation.pattern.store_ops.clone(),
            };

            let mut states = violation.states.clone();
            states.sort();
            pattern_map.entry(pattern).or_default().push(states.clone());
        }

        pattern_map
            .into_iter()
            .map(|(pattern, _)| pattern)
            .collect()
    }

    fn check_state_for_violation(
        graph: &StableGraph<StateNode, StateEdge>,
        load_state: NodeIndex,
        load_op: &AtomicOp,
        stores: &FxHashMap<TransitionId, AtomicOp>,
    ) -> Option<AtomicViolation> {
        let mut visited = FxHashSet::default();
        let mut write_operations = FxHashSet::default();
        let mut stack = vec![load_state];

        while let Some(current) = stack.pop() {
            if !visited.insert(current) {
                continue;
            }

            for edge in graph.edges_directed(current, Direction::Incoming) {
                let source = edge.source();
                let transition = edge.weight().transition.id;
                let transition_type = &edge.weight().transition.transition_type;

                if let TransitionType::Start(thread_id) = transition_type {
                    if *thread_id == load_op.thread_id {
                        break;
                    }
                }

                if let Some(store_op) = stores.get(&transition) {
                    if store_op.var_id == load_op.var_id
                        && Self::ordering_allows(store_op.ordering, load_op.ordering)
                    {
                        write_operations.insert(AtomicOperation {
                            operation_type: "store".to_string(),
                            ordering: format!("{:?}", store_op.ordering),
                            variable: format!("{:?}", store_op.var_id),
                            location: store_op.span.clone(),
                        });
                    }
                }

                stack.push(source);
            }
        }

        let mut write_operations: Vec<_> = write_operations.into_iter().collect();
        if write_operations.len() >= 2 {
            write_operations.sort_by(|a, b| a.location.cmp(&b.location));

            Some(AtomicViolation {
                pattern: ViolationPattern {
                    load_op: AtomicOperation {
                        operation_type: "load".to_string(),
                        ordering: format!("{:?}", load_op.ordering),
                        variable: format!("{:?}", load_op.var_id),
                        location: load_op.span.clone(),
                    },
                    store_ops: write_operations,
                },
                states: graph[load_state]
                    .marking
                    .iter()
                    .filter_map(|(place_id, tokens)| {
                        if *tokens == 0 {
                            return None;
                        }
                        Some((place_id.index(), (*tokens).min(u8::MAX as u64) as u8))
                    })
                    .collect(),
            })
        } else {
            None
        }
    }

    /// Ordering guard: only relate load/store when store order is >= load under the chosen partial order.
    /// Matches common Acquire/Release approximations: Relaxed pairs with any store; SeqCst only with SeqCst;
    /// AcqRel doubles as Release plus SeqCst fallback; Release alone does not satisfy standalone reads.
    fn ordering_allows(store: AtomicOrdering, load: AtomicOrdering) -> bool {
        use AtomicOrdering::*;
        match load {
            Relaxed => true,
            Acquire => matches!(store, Release | AcqRel | SeqCst),
            SeqCst => matches!(store, SeqCst),
            AcqRel => matches!(store, SeqCst | AcqRel),
            Release => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::reachability::StateGraph;
    use crate::concurrency::atomic::AtomicOrdering;
    use crate::net::Net;
    use crate::net::structure::{Place, PlaceType, Transition, TransitionType};
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
        let detector = AtomicityViolationDetector::new(&state_graph);
        let report = detector.detect();

        assert!(report.has_violation, "Expected atomicity violation");
        assert!(!report.violations.is_empty());
    }
}
