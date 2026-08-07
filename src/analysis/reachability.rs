use crate::net::Net;
use crate::net::ids::{PlaceId, TransitionId};
use crate::net::index_vec::Idx;
use crate::net::structure::{Marking, Place, PlaceType, Transition, TransitionType};
use petgraph::dot::{Config, Dot};
use petgraph::graph::NodeIndex;
use petgraph::stable_graph::StableGraph;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
use std::collections::hash_map::Entry;
use std::fs;
use std::path::Path;

#[derive(Debug, Clone)]
pub struct StatePlaceSnapshot {
    pub place: PlaceId,
    pub name: String,
    pub place_type: PlaceType,
    pub span: String,
    pub tokens: u64,
    pub capacity: u64,
}

impl StatePlaceSnapshot {
    fn new(place_id: PlaceId, place: &Place, tokens: u64) -> Self {
        Self {
            place: place_id,
            name: place.name.clone(),
            place_type: place.place_type.clone(),
            span: place.span.clone(),
            tokens,
            capacity: place.capacity,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TokenChange {
    pub place: PlaceId,
    pub name: String,
    pub before: u64,
    pub after: u64,
    pub delta: i64,
}

impl TokenChange {
    fn new(place_id: PlaceId, place: &Place, before: u64, after: u64) -> Option<Self> {
        if before == after {
            return None;
        }
        Some(Self {
            place: place_id,
            name: place.name.clone(),
            before,
            after,
            delta: after as i64 - before as i64,
        })
    }
}

/// Arc role: ordinary input/output vs special arcs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArcKind {
    Input,
    Output,
    #[cfg(feature = "inhibitor")]
    Inhibitor,
    #[cfg(feature = "reset")]
    Reset,
}

#[derive(Debug, Clone)]
pub struct ArcSnapshot {
    pub place: PlaceId,
    pub name: String,
    pub kind: ArcKind,
    pub weight: u64,
}

impl ArcSnapshot {
    fn new(place_id: PlaceId, place: &Place, kind: ArcKind, weight: u64) -> Self {
        Self {
            place: place_id,
            name: place.name.clone(),
            kind,
            weight,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TransitionSummary {
    pub id: TransitionId,
    pub name: String,
    pub transition_type: TransitionType,
}

impl TransitionSummary {
    fn new(id: TransitionId, transition: &Transition) -> Self {
        Self {
            id,
            name: transition.name.clone(),
            transition_type: transition.transition_type.clone(),
        }
    }
}

/// Full marking stored on the node; `places` is a visualization slice only.
#[derive(Debug, Clone)]
pub struct StateNode {
    pub index: usize,
    pub marking: Marking,
    pub places: Vec<StatePlaceSnapshot>,
    pub enabled: Vec<TransitionSummary>,
}

impl StateNode {
    fn new(index: usize, marking: Marking, net: &Net, include_zero_tokens: bool) -> Self {
        let mut places = Vec::new();
        for (place_id, place) in net.places.iter_enumerated() {
            let tokens = marking.tokens(place_id);
            if tokens > 0 || include_zero_tokens {
                places.push(StatePlaceSnapshot::new(place_id, place, tokens));
            }
        }
        Self {
            index,
            marking,
            places,
            enabled: Vec::new(),
        }
    }

    fn update_enabled(&mut self, net: &Net, transitions: &[TransitionId]) {
        self.enabled = transitions
            .iter()
            .map(|&id| TransitionSummary::new(id, &net.transitions[id]))
            .collect();
    }
}

#[derive(Debug, Clone)]
pub struct StateEdge {
    pub transition: TransitionSummary,
    pub changes: Vec<TokenChange>,
    pub arcs: Vec<ArcSnapshot>,
}

impl StateEdge {
    fn new(net: &Net, transition_id: TransitionId, before: &Marking, after: &Marking) -> Self {
        let transition = TransitionSummary::new(transition_id, &net.transitions[transition_id]);
        let mut changes = Vec::new();
        let mut arcs = Vec::new();

        for (place_id, place) in net.places.iter_enumerated() {
            let before_tokens = before.tokens(place_id);
            let after_tokens = after.tokens(place_id);
            if let Some(change) = TokenChange::new(place_id, place, before_tokens, after_tokens) {
                changes.push(change);
            }

            let input_weight = *net.pre.get(place_id, transition_id);
            if input_weight > 0 {
                arcs.push(ArcSnapshot::new(
                    place_id,
                    place,
                    ArcKind::Input,
                    input_weight,
                ));
            }

            let output_weight = *net.post.get(place_id, transition_id);
            if output_weight > 0 {
                arcs.push(ArcSnapshot::new(
                    place_id,
                    place,
                    ArcKind::Output,
                    output_weight,
                ));
            }

            #[cfg(feature = "inhibitor")]
            if let Some(matrix) = net.inhibitor.as_ref() {
                if matrix.get(place_id, transition_id) {
                    arcs.push(ArcSnapshot::new(place_id, place, ArcKind::Inhibitor, 1));
                }
            }

            #[cfg(feature = "reset")]
            if let Some(matrix) = net.reset.as_ref() {
                if matrix.get(place_id, transition_id) {
                    arcs.push(ArcSnapshot::new(place_id, place, ArcKind::Reset, 1));
                }
            }
        }

        Self {
            transition,
            changes,
            arcs,
        }
    }
}

/// Failure recorded while expanding the reachability graph.
#[derive(Debug, Clone)]
pub struct TransitionFailure {
    pub source: NodeIndex,
    pub transition: TransitionId,
    pub transition_name: String,
    pub reason: String,
}

#[derive(Debug, Clone)]
pub struct StateGraphStats {
    pub state_count: usize,
    pub edge_count: usize,
    pub deadlock_count: usize,
    pub truncated: bool,
}

#[derive(Debug, Clone)]
pub struct StateGraphConfig {
    /// Maximum number of states to explore (`None` = unbounded).
    pub state_limit: Option<usize>,
    /// Include zero-token places in per-state snapshots.
    pub include_zero_tokens: bool,
    /// Enable partial-order reduction (POR) to skip redundant interleavings.
    pub use_por: bool,
}

impl Default for StateGraphConfig {
    fn default() -> Self {
        Self {
            state_limit: Some(50_000),
            include_zero_tokens: false,
            use_por: false,
        }
    }
}

/// Return true if two transitions are independent (share no places).
/// Independent firings commute; used by POR to prune redundant interleavings.
fn transitions_are_independent(net: &Net, t1: TransitionId, t2: TransitionId) -> bool {
    if t1 == t2 {
        return false;
    }
    for (place_id, _) in net.places.iter_enumerated() {
        let w1_pre = *net.pre.get(place_id, t1);
        let w1_post = *net.post.get(place_id, t1);
        let w2_pre = *net.pre.get(place_id, t2);
        let w2_post = *net.post.get(place_id, t2);
        if (w1_pre > 0 || w1_post > 0) && (w2_pre > 0 || w2_post > 0) {
            return false;
        }
    }
    true
}

#[derive(Debug)]
pub struct StateGraph {
    pub graph: StableGraph<StateNode, StateEdge>,
    pub initial: NodeIndex,
    pub deadlocks: FxHashSet<NodeIndex>,
    pub truncated: bool,
    pub failures: Vec<TransitionFailure>,
    pub markings: FxHashMap<Marking, NodeIndex>,
    pub net: Option<Net>, // Reference to underlying net for arc inspection
}

impl StateGraph {
    pub fn dot(&self) -> String {
        fn escape(s: &str) -> String {
            s.replace('\\', "\\\\").replace('"', "\\\"")
        }

        let mut edge_attr = |_, edge: petgraph::stable_graph::EdgeReference<StateEdge>| -> String {
            let label = escape(&edge.weight().transition.name);
            format!("label=\"{}\"", label)
        };

        let mut node_attr = |_, (_idx, node): (NodeIndex, &StateNode)| -> String {
            let marking_lines: Vec<String> = node
                .places
                .iter()
                .map(|place| format!("{}:{}", place.name, place.tokens))
                .collect();
            let enabled: Vec<String> = node
                .enabled
                .iter()
                .map(|trans| escape(&trans.name))
                .collect();
            let mut label = format!(
                "s{}\\nmarking: {}",
                node.index,
                escape(&marking_lines.join(", "))
            );
            if !enabled.is_empty() {
                label.push_str(&format!("\\nenabled: {}", enabled.join(", ")));
            }
            format!("label=\"{}\"", label)
        };

        format!(
            "{:?}",
            Dot::with_attr_getters(
                &self.graph,
                &[Config::EdgeNoLabel],
                &mut edge_attr,
                &mut node_attr
            )
        )
    }

    pub fn write_dot<P: AsRef<Path>>(&self, path: P) -> std::io::Result<()> {
        let dot = self.dot();
        if let Some(parent) = path.as_ref().parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, dot)
    }

    pub fn from_net(net: &Net) -> Self {
        Self::with_config(net, StateGraphConfig::default())
    }

    pub fn with_config(net: &Net, config: StateGraphConfig) -> Self {
        if config.use_por {
            Self::with_config_por(net, config)
        } else {
            Self::with_config_standard(net, config)
        }
    }

    fn with_config_standard(net: &Net, config: StateGraphConfig) -> Self {
        let mut graph = StableGraph::new();
        let mut markings: FxHashMap<Marking, NodeIndex> = FxHashMap::default();
        let mut queue: VecDeque<NodeIndex> = VecDeque::new();
        let mut deadlocks = FxHashSet::default();
        let mut failures = Vec::new();
        let mut truncated = false;

        let initial_marking = net.initial_marking();
        let initial_index = graph.add_node(StateNode::new(
            0,
            initial_marking.clone(),
            net,
            config.include_zero_tokens,
        ));
        markings.insert(initial_marking, initial_index);
        queue.push_back(initial_index);

        while let Some(state_index) = queue.pop_front() {
            let current_marking = graph[state_index].marking.clone();
            let enabled = net.enabled_transitions(&current_marking);
            graph[state_index].update_enabled(net, &enabled);

            if enabled.is_empty() {
                deadlocks.insert(state_index);
                continue;
            }

            for transition_id in enabled {
                match net.fire_transition(&current_marking, transition_id) {
                    Ok(next_marking) => {
                        let target_index = match markings.entry(next_marking) {
                            Entry::Occupied(entry) => *entry.get(),
                            Entry::Vacant(entry) => {
                                if let Some(limit) = config.state_limit {
                                    if graph.node_count() >= limit {
                                        truncated = true;
                                        continue;
                                    }
                                }
                                let index = graph.add_node(StateNode::new(
                                    graph.node_count(),
                                    entry.key().clone(),
                                    net,
                                    config.include_zero_tokens,
                                ));
                                entry.insert(index);
                                queue.push_back(index);
                                index
                            }
                        };

                        let edge = StateEdge::new(
                            net,
                            transition_id,
                            &current_marking,
                            &graph[target_index].marking,
                        );
                        graph.add_edge(state_index, target_index, edge);
                    }
                    Err(err) => {
                        failures.push(TransitionFailure {
                            source: state_index,
                            transition: transition_id,
                            transition_name: net.transitions[transition_id].name.clone(),
                            reason: err.to_string(),
                        });
                    }
                }
            }
        }

        Self {
            graph,
            initial: initial_index,
            deadlocks,
            truncated,
            failures,
            markings,
            net: Some(net.clone()),
        }
    }

    /// Build the state graph using sleep-set partial-order reduction.
    fn with_config_por(net: &Net, config: StateGraphConfig) -> Self {
        let mut graph = StableGraph::new();
        let mut markings: FxHashMap<Marking, NodeIndex> = FxHashMap::default();
        let mut sleep_sets: FxHashMap<NodeIndex, FxHashSet<TransitionId>> = FxHashMap::default();
        let mut queue: VecDeque<(NodeIndex, FxHashSet<TransitionId>)> = VecDeque::new();
        let mut deadlocks = FxHashSet::default();
        let mut failures = Vec::new();
        let mut truncated = false;

        let initial_marking = net.initial_marking();
        let initial_index = graph.add_node(StateNode::new(
            0,
            initial_marking.clone(),
            net,
            config.include_zero_tokens,
        ));
        markings.insert(initial_marking.clone(), initial_index);
        queue.push_back((initial_index, FxHashSet::default()));

        while let Some((state_index, sleep)) = queue.pop_front() {
            let current_marking = graph[state_index].marking.clone();
            let enabled: FxHashSet<TransitionId> = net
                .enabled_transitions(&current_marking)
                .into_iter()
                .collect();
            graph[state_index].update_enabled(net, &enabled.iter().copied().collect::<Vec<_>>());

            if enabled.is_empty() {
                deadlocks.insert(state_index);
                continue;
            }

            let to_fire: Vec<TransitionId> = enabled.difference(&sleep).copied().collect();

            for transition_id in to_fire {
                match net.fire_transition(&current_marking, transition_id) {
                    Ok(next_marking) => {
                        let enabled_next: FxHashSet<TransitionId> =
                            net.enabled_transitions(&next_marking).into_iter().collect();
                        let mut new_sleep = sleep.clone();
                        for &t in &enabled {
                            if t != transition_id
                                && transitions_are_independent(net, transition_id, t)
                            {
                                new_sleep.insert(t);
                            }
                        }
                        new_sleep = new_sleep.intersection(&enabled_next).copied().collect();

                        let target_index = match markings.entry(next_marking) {
                            Entry::Occupied(entry) => {
                                let old_ni = *entry.get();
                                let old_sleep =
                                    sleep_sets.get(&old_ni).cloned().unwrap_or_default();
                                let merged_sleep: FxHashSet<TransitionId> =
                                    old_sleep.intersection(&new_sleep).copied().collect();
                                if merged_sleep != old_sleep {
                                    sleep_sets.insert(old_ni, merged_sleep.clone());
                                    queue.push_back((old_ni, merged_sleep));
                                }
                                old_ni
                            }
                            Entry::Vacant(entry) => {
                                if let Some(limit) = config.state_limit {
                                    if graph.node_count() >= limit {
                                        truncated = true;
                                        continue;
                                    }
                                }
                                let index = graph.add_node(StateNode::new(
                                    graph.node_count(),
                                    entry.key().clone(),
                                    net,
                                    config.include_zero_tokens,
                                ));
                                entry.insert(index);
                                sleep_sets.insert(index, new_sleep.clone());
                                queue.push_back((index, new_sleep));
                                index
                            }
                        };

                        let edge = StateEdge::new(
                            net,
                            transition_id,
                            &current_marking,
                            &graph[target_index].marking,
                        );
                        graph.add_edge(state_index, target_index, edge);
                    }
                    Err(err) => {
                        failures.push(TransitionFailure {
                            source: state_index,
                            transition: transition_id,
                            transition_name: net.transitions[transition_id].name.clone(),
                            reason: err.to_string(),
                        });
                    }
                }
            }
        }

        Self {
            graph,
            initial: initial_index,
            deadlocks,
            truncated,
            failures,
            markings,
            net: Some(net.clone()),
        }
    }

    pub fn stats(&self) -> StateGraphStats {
        StateGraphStats {
            state_count: self.graph.node_count(),
            edge_count: self.graph.edge_count(),
            deadlock_count: self.deadlocks.len(),
            truncated: self.truncated,
        }
    }

    pub fn node(&self, index: NodeIndex) -> &StateNode {
        &self.graph[index]
    }

    pub fn contains_marking(&self, marking: &Marking) -> bool {
        self.markings.contains_key(marking)
    }

    /// Get the resources (places + required tokens) that a transition needs.
    /// Returns Vec of (place_id, required_tokens).
    pub fn get_transition_resources(&self, transition_id: TransitionId) -> Vec<(PlaceId, u64)> {
        let mut resources = Vec::new();
        if let Some(net) = &self.net {
            for (place_id, row) in net.pre.rows().iter_enumerated() {
                let weight = row[transition_id.index()];
                if weight > 0 {
                    resources.push((place_id, weight));
                }
            }
        }
        resources
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net::structure::PlaceType;

    fn build_simple_net() -> Net {
        let mut net = Net::empty();
        let p0 = net.add_place(Place::new("p0", 1, 1, PlaceType::BasicBlock, String::new()));
        let p1 = net.add_place(Place::new("p1", 0, 1, PlaceType::BasicBlock, String::new()));
        let t0 = net.add_transition(Transition::new("t0"));

        net.set_input_weight(p0, t0, 1);
        net.set_output_weight(p1, t0, 1);

        net
    }

    #[test]
    fn state_limit_truncates_graph() {
        let net = build_simple_net();
        let config = StateGraphConfig {
            state_limit: Some(1),
            include_zero_tokens: false,
            use_por: false,
        };
        let state_graph = StateGraph::with_config(&net, config);

        assert!(state_graph.truncated);
        assert_eq!(state_graph.graph.node_count(), 1);
    }

    #[test]
    fn por_produces_same_reachable_states() {
        // POR preserves the reachable state set; it only drops redundant edges.
        let net = build_simple_net();
        let config_std = StateGraphConfig {
            state_limit: None,
            include_zero_tokens: false,
            use_por: false,
        };
        let config_por = StateGraphConfig {
            state_limit: None,
            include_zero_tokens: false,
            use_por: true,
        };
        let sg_std = StateGraph::with_config(&net, config_std);
        let sg_por = StateGraph::with_config(&net, config_por);
        assert_eq!(sg_std.graph.node_count(), sg_por.graph.node_count());
        assert_eq!(sg_std.deadlocks.len(), sg_por.deadlocks.len());
    }
}
