use crate::report::{
    BlockedTransition, DeadlockReport, DeadlockState, DeadlockTrace, ResourceStatus,
    ResourceTraceStep,
};
type NodeIndex = usize;
type EdgeIndex = usize;
// EdgeRef replaced by unipn StateGraph accessors
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
use std::time::Instant;
use unipn::analysis::pt::reachability::{StateEdge, StateGraph};
use unipn::pt::{PlaceType, TransitionType};
use unipn::{Marking, PlaceId, TransitionId};

pub struct DeadlockDetector<'a> {
    state_graph: &'a StateGraph,
}

impl<'a> DeadlockDetector<'a> {
    pub fn new(state_graph: &'a StateGraph) -> Self {
        Self { state_graph }
    }

    fn initial_marking(&self) -> &Marking {
        &self.state_graph.states[self.state_graph.initial].marking
    }

    pub fn detect(&self) -> DeadlockReport {
        let start_time = Instant::now();
        let mut report = DeadlockReport::new("Petri Net Deadlock Detector".to_string());

        let reachability_deadlocks = self.detect_reachability_deadlock();

        let dependency_deadlocks = FxHashSet::default();

        let all_deadlocks: FxHashSet<_> = reachability_deadlocks
            .into_iter()
            .chain(dependency_deadlocks.into_iter())
            .collect();

        if !all_deadlocks.is_empty() {
            report.has_deadlock = true;
            report.deadlock_count = all_deadlocks.len();

            for deadlock_state in &all_deadlocks {
                let state_info = self.format_deadlock_state(*deadlock_state);
                report.deadlock_states.push(state_info);

                let trace = self.create_deadlock_trace(*deadlock_state);
                report.traces.push(trace);
            }
        }

        report.state_space_info = Some(self.collect_state_space_info());

        report.analysis_time = start_time.elapsed();
        report
    }

    fn detect_reachability_deadlock(&self) -> FxHashSet<NodeIndex> {
        let mut deadlocks = FxHashSet::default();

        for node_idx in self.state_graph.node_indices() {
            let state = self.state_graph.node(node_idx);
            let is_terminal = self.state_graph.edges(node_idx).count() == 0;
            let is_normal_termination = state
                .places
                .iter()
                .any(|place| place.tokens > 0 && place.name.contains("main_end"));

            if is_terminal && !is_normal_termination {
                deadlocks.insert(node_idx);
            }
        }

        if deadlocks.is_empty() {
            log::info!("no deadlock detected by reachability");

            let cycle_deadlocks = self.detect_cycle_deadlocks();
            deadlocks.extend(cycle_deadlocks);
        }

        deadlocks
    }

    fn detect_cycle_deadlocks(&self) -> FxHashSet<NodeIndex> {
        let mut deadlocks = FxHashSet::default();
        let mut visited = FxHashSet::default();
        let mut stack = FxHashSet::default();
        let mut cycle_groups: FxHashMap<Vec<usize>, FxHashSet<NodeIndex>> = FxHashMap::default();

        for start_node in self.state_graph.node_indices() {
            if !visited.contains(&start_node) {
                self.find_deadlock_cycles(
                    start_node,
                    &mut visited,
                    &mut stack,
                    &mut cycle_groups,
                    &Vec::new(),
                );
            }
        }

        for (_blocked_transitions, states) in cycle_groups {
            if let Some(state) = states.into_iter().next() {
                deadlocks.insert(state);
            }
        }

        deadlocks
    }

    fn find_deadlock_cycles(
        &self,
        current: NodeIndex,
        visited: &mut FxHashSet<NodeIndex>,
        stack: &mut FxHashSet<NodeIndex>,
        cycle_groups: &mut FxHashMap<Vec<usize>, FxHashSet<NodeIndex>>,
        current_path: &Vec<NodeIndex>,
    ) {
        visited.insert(current);
        stack.insert(current);
        let mut path = current_path.clone();
        path.push(current);

        for edge in self.state_graph.edges(current) {
            let next = edge.target();

            if !visited.contains(&next) {
                self.find_deadlock_cycles(next, visited, stack, cycle_groups, &path);
            } else if stack.contains(&next) {
                let cycle_start_idx = path.iter().position(|&x| x == next).unwrap();
                let cycle = &path[cycle_start_idx..];

                if let Some(blocked_trans) = self.get_consistently_blocked_transitions(cycle) {
                    if !blocked_trans.is_empty() {
                        let mut key: Vec<_> = blocked_trans.into_iter().collect();
                        key.sort_unstable();
                        cycle_groups.entry(key).or_default().extend(cycle);
                    }
                }
            }
        }

        stack.remove(&current);
    }

    fn get_consistently_blocked_transitions(
        &self,
        cycle: &[NodeIndex],
    ) -> Option<FxHashSet<usize>> {
        let lock_transitions = self.collect_lock_transitions();
        let mut consistently_blocked = FxHashSet::default();
        let all_locks: FxHashSet<_> = lock_transitions.keys().cloned().collect();

        if let Some(&first_node) = cycle.first() {
            for (lock, transitions) in &lock_transitions {
                let blocked = transitions
                    .iter()
                    .all(|transition| !self.is_transition_enabled(first_node, *transition));
                if blocked {
                    consistently_blocked.insert(*lock);
                }
            }
        }

        for &node in &cycle[1..] {
            let mut current_blocked = FxHashSet::default();
            for &lock in &consistently_blocked {
                if let Some(transitions) = lock_transitions.get(&lock) {
                    let blocked = transitions
                        .iter()
                        .all(|transition| !self.is_transition_enabled(node, *transition));
                    if blocked {
                        current_blocked.insert(lock);
                    }
                }
            }
            consistently_blocked = consistently_blocked
                .intersection(&current_blocked)
                .cloned()
                .collect();

            if consistently_blocked.is_empty() {
                return None;
            }
        }

        let is_stable = cycle.iter().all(|&node| {
            self.state_graph
                .graph
                .edges(node)
                .all(|edge| cycle.contains(&edge.target()))
        });

        if all_locks.is_subset(&consistently_blocked) {
            return None;
        }

        if is_stable {
            Some(consistently_blocked)
        } else {
            None
        }
    }

    fn collect_lock_transitions(&self) -> FxHashMap<usize, Vec<TransitionId>> {
        let mut lock_transitions: FxHashMap<usize, Vec<TransitionId>> = FxHashMap::default();

        for edge in self.state_graph.edge_weights() {
            match &edge.transition.kind.transition_type {
                TransitionType::Lock(lock_id)
                | TransitionType::RwLockWrite(lock_id)
                | TransitionType::RwLockRead(lock_id) => {
                    lock_transitions
                        .entry(*lock_id)
                        .or_default()
                        .push(edge.transition.id);
                }
                _ => {}
            }
        }

        for transitions in lock_transitions.values_mut() {
            transitions.sort_unstable_by_key(|id| id.index());
            transitions.dedup_by_key(|id| id.index());
        }

        lock_transitions
    }

    fn is_transition_enabled(&self, state: NodeIndex, transition_id: TransitionId) -> bool {
        let state_node = self.state_graph.node(state);
        state_node
            .enabled
            .iter()
            .any(|summary| summary.id == transition_id)
    }

    fn operation_label(transition_type: &TransitionType) -> &'static str {
        match transition_type {
            TransitionType::Lock(_) => "Lock acquisition",
            TransitionType::RwLockRead(_) => "RwLock read lock",
            TransitionType::RwLockWrite(_) => "RwLock write lock",
            TransitionType::UnsafeRead(_, _, _, _) => "Unsafe read",
            TransitionType::UnsafeWrite(_, _, _, _) => "Unsafe write",
            TransitionType::UnsafeAccess(_) => "Unsafe access",
            TransitionType::AtomicLoad(_, _, _, _) => "Atomic load",
            TransitionType::AtomicStore(_, _, _, _) => "Atomic store",
            TransitionType::AtomicCmpXchg(_, _, _, _, _) => "Atomic compare-exchange",
            _ => "Resource operation",
        }
    }

    fn transition_location(&self, transition_id: TransitionId) -> String {
        let net = match &self.state_graph.net {
            Some(net) => net,
            None => return String::new(),
        };

        net.places
            .iter().enumerate()
            .find_map(|(place_id, place)| {
                let is_control_input = !matches!(place.kind.place_type, PlaceType::Resources)
                    && net.input_weight(place_id, transition_id) > 0;
                (is_control_input && !place.kind.span.is_empty()).then(|| place.kind.span.clone())
            })
            .unwrap_or_default()
    }

    fn path_to_state(&self, target: NodeIndex) -> Vec<(NodeIndex, NodeIndex, StateEdge)> {
        if target == self.state_graph.initial {
            return Vec::new();
        }

        let mut visited = FxHashSet::default();
        let mut previous: FxHashMap<NodeIndex, (NodeIndex, EdgeIndex)> = FxHashMap::default();
        let mut queue = VecDeque::new();
        visited.insert(self.state_graph.initial);
        queue.push_back(self.state_graph.initial);

        while let Some(node) = queue.pop_front() {
            if node == target {
                break;
            }

            for edge in self.state_graph.edges(node) {
                let next = edge.target();
                if visited.insert(next) {
                    previous.insert(next, (node, edge.id()));
                    queue.push_back(next);
                }
            }
        }

        if !visited.contains(&target) {
            return Vec::new();
        }

        let mut path = Vec::new();
        let mut current = target;
        while current != self.state_graph.initial {
            let Some((source, edge_id)) = previous.get(&current).copied() else {
                return Vec::new();
            };
            let Some(edge) = self.state_graph.edge_weight(edge_id).cloned() else {
                return Vec::new();
            };
            path.push((source, current, edge));
            current = source;
        }
        path.reverse();
        path
    }

    fn trace_resource_usage(
        &self,
        state: NodeIndex,
        resources: &[PlaceId],
    ) -> Vec<ResourceTraceStep> {
        let net = match &self.state_graph.net {
            Some(net) => net,
            None => return Vec::new(),
        };
        let state_node = self.state_graph.node(state);
        let mut remaining: FxHashMap<PlaceId, u64> = resources
            .iter()
            .filter_map(|place_id| {
                let initial = self.initial_marking().tokens(*place_id);
                let current = state_node.marking.tokens(*place_id);
                let deficit = initial.saturating_sub(current);
                (deficit > 0).then_some((*place_id, deficit))
            })
            .collect();
        if remaining.is_empty() {
            return Vec::new();
        }

        let path = self.path_to_state(state);
        let mut trace = Vec::new();
        for (source, target, edge) in path.into_iter().rev() {
            for change in &edge.changes {
                if change.delta >= 0 || !remaining.contains_key(&change.place) {
                    continue;
                }

                let resource_name = net.places[change.place.index()].name.clone();
                trace.push(ResourceTraceStep {
                    resource_name,
                    transition_name: edge.transition.name.clone(),
                    operation: Self::operation_label(&edge.transition.kind.transition_type).to_string(),
                    location: self.transition_location(edge.transition.id),
                    from_state: format!("s{}", self.state_graph.node(source).index),
                    to_state: format!("s{}", self.state_graph.node(target).index),
                    before: change.before,
                    after: change.after,
                });

                let consumed = change.before.saturating_sub(change.after);
                if let Some(remaining_tokens) = remaining.get_mut(&change.place) {
                    *remaining_tokens = remaining_tokens.saturating_sub(consumed);
                    if *remaining_tokens == 0 {
                        remaining.remove(&change.place);
                    }
                }
            }

            if remaining.is_empty() {
                break;
            }
        }

        trace
    }

    fn find_blocked_resource_transitions(&self, state: NodeIndex) -> Vec<BlockedTransition> {
        let state_node = self.state_graph.node(state);
        let net = match &self.state_graph.net {
            Some(net) => net,
            None => return Vec::new(),
        };
        let token_count = |place: PlaceId| state_node.marking.0.get(place).copied().unwrap_or(0);
        let place_names: FxHashMap<PlaceId, (String, String)> = net
            .places
            .iter().enumerate()
            .map(|(place_id, place)| (place_id, (place.name.clone(), place.kind.span.clone())))
            .collect();
        let mut blocked = Vec::new();

        for (transition_id, transition) in net.transitions.iter().enumerate() {
            if net
                .fire_transition(&state_node.marking, transition_id)
                .is_ok()
            {
                continue;
            }

            let pre_places: Vec<(PlaceId, u64, PlaceType)> = net
                .places
                .iter().enumerate()
                .filter_map(|(place_id, place)| {
                    let weight = net.input_weight(place_id, transition_id);
                    (weight > 0).then(|| (place_id, weight, place.kind.place_type.clone()))
                })
                .collect();
            if pre_places.is_empty() {
                continue;
            }

            let non_resource_places: Vec<(PlaceId, u64)> = pre_places
                .iter()
                .filter_map(|(place_id, weight, place_type)| {
                    (!matches!(place_type, PlaceType::Resources)).then_some((*place_id, *weight))
                })
                .collect();
            if non_resource_places.is_empty()
                || !non_resource_places
                    .iter()
                    .all(|(place_id, weight)| token_count(*place_id) >= *weight)
            {
                continue;
            }

            let mut reported_resources = FxHashSet::default();
            let mut resource_status = Vec::new();
            let mut resource_places = Vec::new();
            for (place_id, weight, place_type) in &pre_places {
                if !matches!(place_type, PlaceType::Resources) {
                    continue;
                }
                let has = token_count(*place_id);
                let initial = self.initial_marking().tokens(*place_id);
                if has >= *weight || (has > 0 && has >= initial) {
                    continue;
                }
                let (resource_name, _) = place_names
                    .get(place_id)
                    .cloned()
                    .unwrap_or_else(|| (format!("place#{}", place_id.index()), String::new()));
                reported_resources.insert(*place_id);
                resource_places.push(*place_id);
                resource_status.push(ResourceStatus {
                    resource_name,
                    has,
                    needs: *weight,
                });
            }

            for (place_id, place) in net.places.iter().enumerate() {
                if !matches!(place.kind.place_type, PlaceType::Resources)
                    || reported_resources.contains(&place_id)
                {
                    continue;
                }
                let output = net.output_weight(place_id, transition_id);
                if output == 0 {
                    continue;
                }
                let has = token_count(place_id);
                let input = net.input_weight(place_id, transition_id);
                if has < input {
                    continue;
                }
                let capacity = place.kind.capacity.unwrap_or(usize::MAX);
                let after = has - input + output;
                let initial_tokens = self.initial_marking().tokens(place_id);
                if after <= capacity || (has > 0 && has >= initial_tokens) {
                    continue;
                }
                let (resource_name, _) = place_names
                    .get(&place_id)
                    .cloned()
                    .unwrap_or_else(|| (format!("place#{}", place_id.index()), String::new()));
                resource_places.push(place_id);
                resource_status.push(ResourceStatus {
                    resource_name,
                    has,
                    needs: capacity,
                });
            }

            if resource_status.is_empty() {
                continue;
            }

            let location = non_resource_places
                .iter()
                .find(|(place_id, _)| token_count(*place_id) > 0)
                .and_then(|(place_id, _)| place_names.get(place_id).map(|(_, span)| span.clone()))
                .unwrap_or_default();
            let operation = Self::operation_label(&transition.kind.transition_type).to_string();
            let needed_resources = resource_status
                .iter()
                .map(|status| status.resource_name.clone())
                .collect();
            let resource_trace = self.trace_resource_usage(state, &resource_places);

            blocked.push(BlockedTransition {
                id: format!("t{}", transition_id.index()),
                name: transition.name.clone(),
                location,
                operation,
                needed_resources,
                resource_status,
                resource_trace,
            });
        }

        blocked
    }

    fn format_deadlock_state(&self, node: NodeIndex) -> DeadlockState {
        let state = self.state_graph.node(node);
        let marking: Vec<(String, u8)> = state
            .marking
            .iter()
            .filter_map(|(place_id, tokens)| {
                if *tokens == 0 {
                    return None;
                }
                let description = state
                    .places
                    .iter()
                    .find(|p| p.place == place_id)
                    .map(|p| format!("{} ({})", p.name, p.span))
                    .unwrap_or_else(|| format!("place#{}", place_id.index()));
                Some((description, (*tokens).min(u8::MAX as u64) as u8))
            })
            .collect();

        DeadlockState {
            state_id: format!("s{}", state.index),
            marking,
            description: "Deadlock state with blocked resources".to_string(),
            blocked_transitions: self.find_blocked_resource_transitions(node),
        }
    }

    fn create_deadlock_trace(&self, node: NodeIndex) -> DeadlockTrace {
        DeadlockTrace {
            steps: vec!["Path reconstruction not implemented yet".to_string()],
            final_state: Some(self.format_deadlock_state(node)),
        }
    }

    fn collect_state_space_info(&self) -> crate::report::StateSpaceInfo {
        crate::report::StateSpaceInfo {
            total_states: self.state_graph.node_count(),
            total_transitions: self.state_graph.edge_count(),
            reachable_states: self.state_graph.node_count(),
        }
    }
}

