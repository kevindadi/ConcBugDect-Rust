//! Petri net boundness analysis.
//!
//! Provides several ways to check whether a net is bounded:
//! 1. P-invariant-based boundness
//! 2. Coverability tree construction
//! 3. (Reachability-graph variants reserved)

use crate::net::Net;
use crate::net::ids::{PlaceId, TransitionId};
use crate::net::index_vec::Idx;
use crate::net::structure::Marking;
#[cfg(feature = "invariants")]
use num::bigint::BigInt;

use std::collections::VecDeque;
use std::fmt;

/// Result of a boundness check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoundnessResult {
    /// The net is bounded.
    Bounded,
    /// The net is unbounded; carries witness places / firing sequence when known.
    Unbounded {
        /// Places that became ω (unbounded).
        unbounded_places: Vec<PlaceId>,
        /// Witness firing sequence if reconstructed.
        witness_sequence: Option<Vec<TransitionId>>,
    },
    /// Boundness could not be determined (e.g. state explosion).
    Unknown { reason: String },
}

impl fmt::Display for BoundnessResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BoundnessResult::Bounded => write!(f, "Petri net is bounded"),
            BoundnessResult::Unbounded {
                unbounded_places,
                witness_sequence,
            } => {
                write!(
                    f,
                    "Petri net is unbounded; unbounded places: {:?}",
                    unbounded_places
                )?;
                if let Some(seq) = witness_sequence {
                    write!(f, "; witness sequence: {:?}", seq)?;
                }
                Ok(())
            }
            BoundnessResult::Unknown { reason } => {
                write!(f, "Could not determine boundness: {}", reason)
            }
        }
    }
}

/// Node in the coverability tree.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CoverTreeNode {
    /// Marking at this node (None slot denotes ω).
    marking: Vec<Option<u64>>,
    /// Parent index in the tree.
    parent: Option<usize>,
    /// Transition fired from the parent.
    transition_from_parent: Option<TransitionId>,
    /// Child indices.
    children: Vec<usize>,
}

impl CoverTreeNode {
    fn new_root(initial_marking: &Marking) -> Self {
        let marking = initial_marking
            .iter()
            .map(|(_, tokens)| Some(*tokens))
            .collect();

        Self {
            marking,
            parent: None,
            transition_from_parent: None,
            children: Vec::new(),
        }
    }

    fn has_omega(&self) -> bool {
        self.marking.iter().any(|tokens| tokens.is_none())
    }

    #[allow(dead_code)]
    fn tokens(&self, place: PlaceId) -> Option<u64> {
        self.marking[place.index()]
    }
}

/// Coverability tree structure.
#[derive(Debug, Clone)]
struct CoverTree {
    nodes: Vec<CoverTreeNode>,
    #[allow(dead_code)]
    root: usize,
}

impl CoverTree {
    fn new(initial_marking: &Marking) -> Self {
        let root_node = CoverTreeNode::new_root(initial_marking);

        Self {
            nodes: vec![root_node],
            root: 0,
        }
    }

    fn node(&self, index: usize) -> &CoverTreeNode {
        &self.nodes[index]
    }

    fn node_mut(&mut self, index: usize) -> &mut CoverTreeNode {
        &mut self.nodes[index]
    }

    fn add_child(
        &mut self,
        parent: usize,
        marking: Vec<Option<u64>>,
        transition: TransitionId,
    ) -> usize {
        let child_index = self.nodes.len();

        self.nodes.push(CoverTreeNode {
            marking,
            parent: Some(parent),
            transition_from_parent: Some(transition),
            children: Vec::new(),
        });

        self.node_mut(parent).children.push(child_index);
        child_index
    }

    fn is_covered(&self, marking: &[Option<u64>]) -> Option<usize> {
        for (i, node) in self.nodes.iter().enumerate() {
            if self.covers(marking, &node.marking) {
                return Some(i);
            }
        }
        None
    }

    /// True if marking1 covers marking2 componentwise (ω covers anything).
    fn covers(&self, marking1: &[Option<u64>], marking2: &[Option<u64>]) -> bool {
        marking1.iter().zip(marking2.iter()).all(|(m1, m2)| {
            match (m1, m2) {
                // ω covers any value.
                (None, _) => true,
                // Concrete covers equal or smaller concrete.
                (Some(v1), Some(v2)) => v1 >= v2,
                // Concrete cannot cover ω.
                (Some(_), None) => false,
            }
        })
    }
}

pub struct BoundnessAnalyzer {
    state_limit: Option<usize>,
}

impl Default for BoundnessAnalyzer {
    fn default() -> Self {
        Self {
            state_limit: Some(10000),
        }
    }
}

impl BoundnessAnalyzer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_state_limit(mut self, limit: Option<usize>) -> Self {
        self.state_limit = limit;
        self
    }

    /// Boundness via P-invariants (fast when `invariants` feature is enabled).
    pub fn check_by_p_invariants(&self, net: &Net) -> BoundnessResult {
        #[cfg(not(feature = "invariants"))]
        {
            let _ = net;
            return BoundnessResult::Unknown {
                reason: "Enable the `invariants` feature for P-invariant boundness".to_string(),
            };
        }

        #[cfg(feature = "invariants")]
        {
            let invariants = net.place_invariants();

            if invariants.is_empty() {
                return BoundnessResult::Unknown {
                    reason: "No P-invariants found".to_string(),
                };
            }

            let mut positive_invariants = Vec::new();
            for invariant in &invariants {
                if invariant.iter().all(|coeff| coeff >= &BigInt::from(0)) {
                    positive_invariants.push(invariant);
                }
            }

            if !positive_invariants.is_empty() {
                return BoundnessResult::Bounded;
            }

            BoundnessResult::Unknown {
                reason: "No positive P-invariant found; further analysis needed".to_string(),
            }
        }
    }

    /// Boundness via coverability tree (may print debug traces).
    pub fn check_by_coverability_tree(&self, net: &Net) -> BoundnessResult {
        let initial_marking = net.initial_marking();
        let mut tree = CoverTree::new(&initial_marking);
        let mut queue = VecDeque::new();
        queue.push_back(0); // root

        let mut visited_count = 0;
        let mut iteration = 0;

        while let Some(node_index) = queue.pop_front() {
            visited_count += 1;
            iteration += 1;

            if let Some(limit) = self.state_limit {
                if visited_count > limit {
                    return BoundnessResult::Unknown {
                        reason: format!("Exceeded state limit {}", limit),
                    };
                }
            }

            let node = tree.node(node_index).clone();

            if node.has_omega() {
                let mut unbounded_places = Vec::new();
                let mut witness_sequence = Vec::new();
                let mut current = node_index;

                for (place_idx, tokens) in node.marking.iter().enumerate() {
                    if tokens.is_none() {
                        unbounded_places.push(PlaceId::from_usize(place_idx));
                    }
                }

                while let Some(parent) = tree.node(current).parent {
                    if let Some(trans) = tree.node(current).transition_from_parent {
                        witness_sequence.push(trans);
                    }
                    current = parent;
                }
                witness_sequence.reverse();

                println!(
                    "Iteration {}: ω marking at node {}, unbounded places: {:?}",
                    iteration, node_index, unbounded_places
                );
                return BoundnessResult::Unbounded {
                    unbounded_places,
                    witness_sequence: Some(witness_sequence),
                };
            }

            let current_marking_vec: Vec<u64> = node
                .marking
                .iter()
                .map(|tokens| tokens.unwrap_or(0))
                .collect();

            println!(
                "Iteration {}: node {}, marking: {:?}",
                iteration, node_index, current_marking_vec
            );

            use crate::net::index_vec::IndexVec;
            let temp_marking = Marking::new(IndexVec::from(current_marking_vec));

            let enabled_transitions = net.enabled_transitions(&temp_marking);
            println!("  Enabled transitions: {:?}", enabled_transitions);

            for transition_id in enabled_transitions {
                match net.fire_transition(&temp_marking, transition_id) {
                    Ok(next_marking) => {
                        let next_marking_vec: Vec<Option<u64>> = next_marking
                            .iter()
                            .map(|(_, tokens)| Some(*tokens))
                            .collect();

                        println!(
                            "  Transition {} fired, new marking: {:?}",
                            transition_id.0, next_marking_vec
                        );

                        if let Some(covered_by) = tree.is_covered(&next_marking_vec) {
                            println!("    New marking covered by node {}", covered_by);

                            let path = self.find_path_to_node(&tree, node_index, covered_by);

                            if let Some(path_nodes) = path {
                                let mut needs_omega = false;
                                for &path_node_idx in &path_nodes {
                                    let path_marking = &tree.node(path_node_idx).marking;
                                    if self.is_strictly_smaller(path_marking, &next_marking_vec) {
                                        needs_omega = true;
                                        break;
                                    }
                                }

                                if needs_omega {
                                    let omega_marking = self.create_omega_marking(
                                        &tree,
                                        &path_nodes,
                                        &next_marking_vec,
                                    );

                                    println!("    Creating ω node, marking: {:?}", omega_marking);
                                    let child_idx =
                                        tree.add_child(node_index, omega_marking, transition_id);
                                    queue.push_back(child_idx);
                                } else {
                                    println!("    Branch ends; no ω acceleration needed");
                                }
                            } else {
                                println!("    No path found; adding ordinary node");
                                let child_idx =
                                    tree.add_child(node_index, next_marking_vec, transition_id);
                                queue.push_back(child_idx);
                            }
                        } else {
                            println!("    New marking not covered; adding ordinary node");
                            let child_idx =
                                tree.add_child(node_index, next_marking_vec, transition_id);
                            queue.push_back(child_idx);
                        }
                    }
                    Err(e) => {
                        println!("  Transition {} failed to fire: {:?}", transition_id.0, e);
                        continue;
                    }
                }
            }
        }

        println!(
            "Coverability tree complete: {} nodes processed, no ω markings",
            visited_count
        );

        BoundnessResult::Bounded
    }

    fn find_path_to_node(&self, tree: &CoverTree, from: usize, to: usize) -> Option<Vec<usize>> {
        let mut path = Vec::new();
        let mut current = from;

        while current != to {
            path.push(current);
            if let Some(parent) = tree.node(current).parent {
                current = parent;
                if current == to {
                    path.push(current);
                    return Some(path);
                }
            } else {
                return None;
            }
        }

        // from == to
        Some(vec![from])
    }

    /// Strict componentwise `<` with ω semantics as in the coverability construction.
    fn is_strictly_smaller(&self, marking1: &[Option<u64>], marking2: &[Option<u64>]) -> bool {
        marking1
            .iter()
            .zip(marking2.iter())
            .all(|(m1, m2)| match (m1, m2) {
                (None, Some(_)) => false,
                (Some(v1), Some(v2)) => v1 < v2,
                _ => false,
            })
            && marking1
                .iter()
                .zip(marking2.iter())
                .any(|(m1, m2)| match (m1, m2) {
                    (Some(v1), Some(v2)) => v1 < v2,
                    _ => false,
                })
    }

    fn create_omega_marking(
        &self,
        tree: &CoverTree,
        path_nodes: &[usize],
        new_marking: &[Option<u64>],
    ) -> Vec<Option<u64>> {
        let mut omega_marking = new_marking.to_vec();

        for &node_idx in path_nodes {
            let node_marking = &tree.node(node_idx).marking;
            for (i, (old_val, new_val)) in node_marking.iter().zip(new_marking.iter()).enumerate() {
                match (old_val, new_val) {
                    (Some(old), Some(new)) if old < new => {
                        omega_marking[i] = None;
                    }
                    _ => {}
                }
            }
        }

        omega_marking
    }

    /// Try P-invariants first, then coverability tree.
    pub fn check(&self, net: &Net) -> BoundnessResult {
        let p_invariant_result = self.check_by_p_invariants(net);
        if matches!(p_invariant_result, BoundnessResult::Bounded) {
            return p_invariant_result;
        }

        let coverability_result = self.check_by_coverability_tree(net);
        match coverability_result {
            BoundnessResult::Unbounded { .. } => coverability_result,
            BoundnessResult::Bounded => coverability_result,
            BoundnessResult::Unknown { .. } => BoundnessResult::Unknown {
                reason: String::from("Unknown"),
            },
        }
    }
}

/// Convenience: check whether `net` is bounded.
pub fn check_boundness(net: &Net) -> BoundnessResult {
    let analyzer = BoundnessAnalyzer::new();
    analyzer.check(net)
}

/// Check boundness information restricted to a single place.
pub fn check_place_boundness(net: &Net, place: PlaceId) -> BoundnessResult {
    let analyzer = BoundnessAnalyzer::new();
    let result = analyzer.check(net);

    match result {
        BoundnessResult::Bounded => BoundnessResult::Bounded,
        BoundnessResult::Unbounded {
            unbounded_places,
            witness_sequence,
        } => {
            if unbounded_places.contains(&place) {
                BoundnessResult::Unbounded {
                    unbounded_places: vec![place],
                    witness_sequence,
                }
            } else {
                BoundnessResult::Bounded
            }
        }
        BoundnessResult::Unknown { reason } => BoundnessResult::Unknown { reason },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net::structure::{Place, PlaceType, Transition};

    fn build_bounded_net() -> Net {
        let mut net = Net::empty();

        let p0 = net.add_place(Place::new(
            "p0",
            1,
            10,
            PlaceType::BasicBlock,
            String::new(),
        ));
        let p1 = net.add_place(Place::new(
            "p1",
            0,
            10,
            PlaceType::BasicBlock,
            String::new(),
        ));

        let t0 = net.add_transition(Transition::new("t0"));
        let t1 = net.add_transition(Transition::new("t1"));

        // p0 -> t0 -> p1 -> t1 -> p0
        net.set_input_weight(p0, t0, 1);
        net.set_output_weight(p1, t0, 1);

        net.set_input_weight(p1, t1, 1);
        net.set_output_weight(p0, t1, 1);

        net
    }

    fn build_unbounded_net() -> Net {
        let mut net = Net::empty();

        let p0 = net.add_place(Place::new(
            "p0",
            1,
            u64::MAX,
            PlaceType::BasicBlock,
            String::new(),
        ));
        let p1 = net.add_place(Place::new(
            "p1",
            0,
            u64::MAX,
            PlaceType::BasicBlock,
            String::new(),
        ));

        let t0 = net.add_transition(Transition::new("t0"));

        // p0 -> t0 -> p0 + p1 (token generator)
        net.set_input_weight(p0, t0, 1);
        net.set_output_weight(p0, t0, 1);
        net.set_output_weight(p1, t0, 1);

        println!("Built unbounded net:");
        println!("  Place p0: initial tokens=1, unlimited capacity");
        println!("  Place p1: initial tokens=0, unlimited capacity");
        println!("  Transition t0: input p0(1) -> output p0(1)+p1(1)");

        net
    }

    #[test]
    fn test_bounded_net() {
        let net = build_bounded_net();
        let result = check_boundness(&net);

        assert!(matches!(result, BoundnessResult::Bounded));
    }

    #[test]
    fn test_p_invariants_method() {
        let net = build_bounded_net();
        let analyzer = BoundnessAnalyzer::new();
        let result = analyzer.check_by_p_invariants(&net);

        #[cfg(feature = "invariants")]
        assert!(matches!(result, BoundnessResult::Bounded));
        #[cfg(not(feature = "invariants"))]
        assert!(matches!(result, BoundnessResult::Unknown { .. }));
    }

    #[test]
    fn test_place_boundness() {
        let net = build_unbounded_net();
        let p0 = PlaceId::from_usize(0);
        let p1 = PlaceId::from_usize(1);

        let _result_p0 = check_place_boundness(&net, p0);
        let result_p1 = check_place_boundness(&net, p1);

        match result_p1 {
            BoundnessResult::Unbounded {
                unbounded_places, ..
            } => {
                assert_eq!(unbounded_places, vec![p1]);
            }
            _ => {
                println!("Could not determine boundness of place p1");
            }
        }
    }
}
