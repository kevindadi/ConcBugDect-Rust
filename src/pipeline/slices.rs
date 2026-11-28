//! Splits a library net into per-root-group state graphs and merges them.
//! Roots that share a non-atomic synchronizer stay in one slice.
//! Main-mode binaries never reach this module.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use unipn::analysis::pt::reachability::{StateGraph, TransitionFailure};
use unipn::net::{Marking, PlaceId, PlaceRole};
use unipn::pt::PtNet;

use crate::translate::construct::LibraryRootEntry;

/// Per-slice size statistics: the evidence that the product explosion was cut
/// into small independent state spaces.
#[derive(Clone, Debug)]
pub struct SliceStats {
    /// The root names of the slice (one entry for a singleton root slice, more
    /// for an equivalence class).
    pub entry_roots: Vec<String>,
    /// Global index of this slice's initial state in the merged graph.
    pub initial_state: usize,
    pub states: usize,
    pub edges: usize,
    pub blocked: usize,
    /// Genuine deadlocks (`StateGraph::deadlock_states`) of this slice alone.
    pub deadlocks: usize,
    pub truncated: bool,
    /// Non-blocked states without successors: the slice's truncation frontier
    /// (; 0 unless this slice hit the state limit).
    pub frontier_states: usize,
}

/// The slice provenance of a merged state graph.
#[derive(Clone, Debug, Default)]
pub struct SliceLayout {
    pub slices: Vec<SliceStats>,
    /// One slice index per state of the merged graph.
    pub state_slice: Vec<usize>,
    /// Groups skipped because the global slice state budget was spent before
    /// they were reached (0 for unbudgeted runs). The merged graph is then a
    /// prefix of the partition, in partition order.
    pub unexplored_slices: usize,
}

impl SliceLayout {
    pub fn slice_of(&self, state: usize) -> Option<&SliceStats> {
        self.state_slice
            .get(state)
            .and_then(|&slice| self.slices.get(slice))
    }

    /// The state σ reconstruction must stop at for `state`: this slice's
    /// initial state (the merged graph has one initial per slice, so the
    /// single `StateGraph::initial` is not enough).
    pub fn initial_state_of(&self, state: usize) -> Option<usize> {
        self.slice_of(state).map(|slice| slice.initial_state)
    }
}

/// A merged state graph plus its slice provenance.
pub struct SlicedStateGraph {
    pub graph: StateGraph,
    pub layout: SliceLayout,
}

/// A place that makes two roots synchronize directly.
///
/// Resources only: a control place is shared by call/spawn structure inside a
/// slice, and an atomic place can never be held across a wait. See the module
/// docs for why this is the deadlock-preserving partition.
fn is_synchronizing_place(net: &PtNet, place: usize) -> bool {
    let Some(place) = net.place(PlaceId(place)) else {
        return false;
    };
    place.kind.is_resource() && !place.name.starts_with("Atomic(")
}

/// The structural closure of `start`: every place reachable through the
/// translated net's arcs, ignoring token counts and directions (an
/// over-approximation, which is the safe side for grouping).
pub fn place_closure(net: &PtNet, start: PlaceId) -> BTreeSet<usize> {
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut queue: VecDeque<PlaceId> = VecDeque::new();
    seen.insert(start.index());
    queue.push_back(start);
    while let Some(place) = queue.pop_front() {
        // A transition can be reached through any incident arc (input, output,
        // inhibitor, reset); once reached, all of its places are in the slice.
        for arc in net.arcs_at(place) {
            for incident in net.arcs_for(arc.transition) {
                if seen.insert(incident.place.index()) {
                    queue.push_back(incident.place);
                }
            }
        }
    }
    seen
}

/// The *direct* grouping pairs among the roots, given their closures:
///
/// 1. two roots whose closures share a non-atomic synchronizing place, and
/// 2. a root whose closure reaches another root's `_end` without reaching its
///    `_start` (a cross-root join the first cannot resolve itself).
///
/// [`group_roots`] takes the transitive closure of these pairs; the
/// partitioned slicing of [`partition_groups`] keeps every pair itself
/// covered.
fn required_pairs(
    net: &PtNet,
    roots: &[LibraryRootEntry],
    closures: &[BTreeSet<usize>],
) -> BTreeSet<(usize, usize)> {
    let mut pairs = BTreeSet::new();

    // Rule 1: a directly shared non-atomic synchronizer.
    let mut owners: HashMap<usize, Vec<usize>> = HashMap::new();
    for (root, places) in closures.iter().enumerate() {
        for &place in places {
            if is_synchronizing_place(net, place) {
                owners.entry(place).or_default().push(root);
            }
        }
    }
    for shared in owners.values() {
        for (i, &a) in shared.iter().enumerate() {
            for &b in &shared[i + 1..] {
                if a != b {
                    pairs.insert((a.min(b), a.max(b)));
                }
            }
        }
    }

    // Rule 2: a join on another root's `_end` that this root cannot produce
    // itself (it cannot reach that root's `_start`, so the callee never runs
    // inside this slice).
    for (root, places) in closures.iter().enumerate() {
        for (other, entry) in roots.iter().enumerate() {
            if root == other {
                continue;
            }
            if places.contains(&entry.end.index()) && !places.contains(&entry.start.index()) {
                pairs.insert((root.min(other), root.max(other)));
            }
        }
    }
    pairs
}

fn find(parent: &mut [usize], mut node: usize) -> usize {
    while parent[node] != node {
        parent[node] = parent[parent[node]];
        node = parent[node];
    }
    node
}

fn union(parent: &mut [usize], a: usize, b: usize) {
    let root_a = find(parent, a);
    let root_b = find(parent, b);
    if root_a != root_b {
        parent[root_b] = root_a;
    }
}

/// Partition the roots into deadlock-preserving equivalence classes.
///
/// Returns groups of indices into `roots`, ordered by their first root's name
/// (the roots are expected in the deterministic order
/// [`PetriNet::library_root_entries`](crate::translate::construct::PetriNet::library_root_entries)
/// produces).
pub fn group_roots(net: &PtNet, roots: &[LibraryRootEntry]) -> Vec<Vec<usize>> {
    if roots.is_empty() {
        return Vec::new();
    }
    let closures: Vec<BTreeSet<usize>> = roots
        .iter()
        .map(|root| place_closure(net, root.start))
        .collect();
    let mut parent: Vec<usize> = (0..roots.len()).collect();
    for (a, b) in required_pairs(net, roots, &closures) {
        union(&mut parent, a, b);
    }

    let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for root in 0..roots.len() {
        let representative = find(&mut parent, root);
        groups.entry(representative).or_default().push(root);
    }
    let mut groups: Vec<Vec<usize>> = groups.into_values().collect();
    // Roots are name-sorted, so the smallest index is the lexicographically
    // first member: a deterministic slice order.
    groups.sort_by_key(|group| group.iter().copied().min().unwrap_or(usize::MAX));
    groups
}

/// Split oversized groups so that at most `max_roots` roots start per slice
/// .
///
/// A shared lock resource can merge dozens of roots into one slice whose
/// joint product state space truncates long before any root reaches a wait
/// (parking_lot: 33 roots, 50k states, every sink a frontier state). The
/// transitive grouping is stronger than needed: a wait-for relation is always
/// a relation between *two* roots at a time, so it is enough that every
/// directly synchronizing pair — or cross-root join pair, see
/// [`required_pairs`] — appears together in at least one slice. The greedy
/// cover below keeps that invariant while capping the roots started at once.
///
/// `max_roots = None` (or a cap at least as large as every group) returns the
/// groups unchanged. The result is deterministic: uncovered pairs are seeded
/// in lexicographic order, and the greedy extension prefers the root index
/// with the most still-uncovered pairs to the slice (smallest index on a
/// tie). Roots of an oversized group that no seed pair reaches become
/// singleton slices, so every root appears in exactly one slice at least.
pub fn partition_groups(
    net: &PtNet,
    roots: &[LibraryRootEntry],
    groups: &[Vec<usize>],
    max_roots: Option<usize>,
) -> Vec<Vec<usize>> {
    let Some(cap) = max_roots.filter(|&cap| cap >= 1) else {
        return groups.to_vec();
    };
    if groups.iter().all(|group| group.len() <= cap) {
        return groups.to_vec();
    }

    let closures: Vec<BTreeSet<usize>> = roots
        .iter()
        .map(|root| place_closure(net, root.start))
        .collect();
    let required = required_pairs(net, roots, &closures);
    let oversized: Vec<&Vec<usize>> = groups.iter().filter(|group| group.len() > cap).collect();
    let required_in_oversized: usize = required
        .iter()
        .filter(|(a, b)| {
            oversized
                .iter()
                .any(|group| group.contains(a) && group.contains(b))
        })
        .count();
    log::info!(
        "slice partitioning: {} of {} group(s) oversized under cap {}; {} required pair(s) to cover",
        oversized.len(),
        groups.len(),
        cap,
        required_in_oversized
    );

    let mut sliced = Vec::with_capacity(groups.len());
    for group in groups {
        if group.len() <= cap {
            sliced.push(group.clone());
            continue;
        }
        let members: BTreeSet<usize> = group.iter().copied().collect();
        let pairs: BTreeSet<(usize, usize)> = required
            .iter()
            .copied()
            .filter(|(a, b)| members.contains(a) && members.contains(b))
            .collect();
        let mut covered: BTreeSet<(usize, usize)> = BTreeSet::new();
        let mut placed: BTreeSet<usize> = BTreeSet::new();

        for &seed in &pairs {
            if covered.contains(&seed) {
                continue;
            }
            let mut slice = vec![seed.0, seed.1];
            let mut in_slice: BTreeSet<usize> = slice.iter().copied().collect();
            while slice.len() < cap {
                // Add the root that covers the most not-yet-covered pairs to
                // *this* slice; a root covering none would only enlarge the
                // product state space without strengthening the slice.
                let mut best: Option<(usize, usize)> = None; // (new pairs, root)
                for &candidate in group {
                    if in_slice.contains(&candidate) {
                        continue;
                    }
                    let gain = pairs
                        .iter()
                        .filter(|&&(a, b)| {
                            !covered.contains(&(a, b))
                                && ((a == candidate && in_slice.contains(&b))
                                    || (b == candidate && in_slice.contains(&a)))
                        })
                        .count();
                    if gain == 0 {
                        continue;
                    }
                    let better = match best {
                        None => true,
                        Some((best_gain, best_root)) => {
                            gain > best_gain || (gain == best_gain && candidate < best_root)
                        }
                    };
                    if better {
                        best = Some((gain, candidate));
                    }
                }
                let Some((_, candidate)) = best else { break };
                slice.push(candidate);
                in_slice.insert(candidate);
            }
            slice.sort_unstable();
            for (i, &a) in slice.iter().enumerate() {
                for &b in &slice[i + 1..] {
                    covered.insert((a, b));
                }
                placed.insert(a);
            }
            sliced.push(slice);
        }

        // Every member of a non-singleton group is incident to a required
        // pair, so this only fires for a group built by an out-of-band rule;
        // keeping the root in its own slice still explores it exactly once.
        for &member in group {
            if !placed.contains(&member) {
                sliced.push(vec![member]);
            }
        }
    }
    sliced
}

/// Explore one slice: the same net, but only the roots of this group hold a
/// start token.
fn explore_slice(
    net: &PtNet,
    base_marking: &Marking,
    starts: &[PlaceId],
    group: &[usize],
    state_limit: Option<usize>,
    include_zero_tokens: bool,
    use_por: bool,
) -> StateGraph {
    let mut marking = base_marking.clone();
    let in_group: BTreeSet<usize> = group.iter().copied().collect();
    for (root, &start) in starts.iter().enumerate() {
        marking.set(start, usize::from(in_group.contains(&root)));
    }
    StateGraph::with_config(
        net,
        marking,
        unipn::analysis::pt::reachability::StateGraphConfig {
            state_limit,
            include_zero_tokens,
            use_por,
        },
    )
}

/// Explore every group and merge the graphs into one global-index graph.
///
/// `starts` holds the reduced-net start place of every root, aligned with
/// `roots`; every root must appear in exactly one group.
pub fn slice_state_graphs(
    net: &PtNet,
    base_marking: &Marking,
    roots: &[LibraryRootEntry],
    starts: &[PlaceId],
    groups: &[Vec<usize>],
    state_limit: Option<usize>,
    state_budget: Option<usize>,
    include_zero_tokens: bool,
    use_por: bool,
) -> SlicedStateGraph {
    let mut merged = StateGraph {
        states: Vec::new(),
        edges: Vec::new(),
        initial: 0,
        blocked: Default::default(),
        truncated: false,
        failures: Vec::new(),
        markings: HashMap::new(),
        net: None,
    };
    let mut layout = SliceLayout::default();

    for group in groups {
        // `state_budget` bounds the *merged* graph: with
        // `--state-limit N --slice-state-budget N` the run spends the same
        // total number of states as a joint exploration at N, which makes
        // the two comparable. Slices are visited in partition order; the
        // last explored slice is additionally capped to the remaining
        // budget, and every slice after it is counted as unexplored.
        let slice_limit = match state_budget {
            Some(budget) => {
                let used = merged.states.len();
                if used >= budget {
                    layout.unexplored_slices += 1;
                    continue;
                }
                let remaining = budget - used;
                Some(state_limit.map_or(remaining, |limit| limit.min(remaining)))
            }
            None => state_limit,
        };
        let mut graph = explore_slice(
            net,
            base_marking,
            starts,
            group,
            slice_limit,
            include_zero_tokens,
            use_por,
        );
        // The slice graphs never need their own net copy; keeping 37 net
        // clones alive next to the merged graph is pure peak-memory waste.
        graph.net = None;

        let offset = merged.states.len();
        let slice_index = layout.slices.len();
        let deadlocks = graph.deadlock_states(net).len();
        let frontier_states = crate::report::frontier_state_count(&graph);
        log::info!(
            "library slice [{}/{}] ({} root(s): {}) explored: {} states / {} edges / {} blocked / {} deadlocks / frontier {} / truncated={}",
            slice_index + 1,
            groups.len(),
            group.len(),
            group
                .iter()
                .map(|&root| roots[root].name.as_str())
                .collect::<Vec<_>>()
                .join(" + "),
            graph.states.len(),
            graph.edges.len(),
            graph.blocked.len(),
            deadlocks,
            frontier_states,
            graph.truncated
        );
        layout.slices.push(SliceStats {
            entry_roots: group.iter().map(|&root| roots[root].name.clone()).collect(),
            initial_state: offset,
            states: graph.states.len(),
            edges: graph.edges.len(),
            blocked: graph.blocked.len(),
            deadlocks,
            truncated: graph.truncated,
            frontier_states,
        });
        layout
            .state_slice
            .extend(std::iter::repeat_n(slice_index, graph.states.len()));

        merged.truncated |= graph.truncated;
        for mut state in graph.states {
            state.index += offset;
            merged.states.push(state);
        }
        for (from, to, edge) in graph.edges {
            merged.edges.push((from + offset, to + offset, edge));
        }
        for blocked in graph.blocked {
            merged.blocked.insert(blocked + offset);
        }
        for failure in graph.failures {
            merged.failures.push(TransitionFailure {
                source: failure.source + offset,
                ..failure
            });
        }
        for (marking, state) in graph.markings {
            merged.markings.entry(marking).or_insert(state + offset);
        }
    }

    if layout.unexplored_slices > 0 {
        merged.truncated = true;
        log::warn!(
            "library slice state budget {:?} spent after {}/{} slice(s); {} slice(s) unexplored",
            state_budget,
            groups.len() - layout.unexplored_slices,
            groups.len(),
            layout.unexplored_slices
        );
    }

    SlicedStateGraph {
        graph: merged,
        layout,
    }
}

/// Map every raw-net place id to the reduced-net place id that survived (or
/// covers) it. `place_mapping` is indexed by reduced id and holds the original
/// ids, so this is its inverse.
pub fn reduced_place_of(
    net: &PtNet,
    reduce_trace: Option<&unipn::analysis::pt::reduce::ReductionTrace>,
) -> HashMap<usize, PlaceId> {
    match reduce_trace {
        Some(trace) => {
            let mut mapping = HashMap::new();
            for (reduced, originals) in trace.place_mapping.iter().enumerate() {
                for original in originals {
                    mapping.insert(original.index(), PlaceId(reduced));
                }
            }
            mapping
        }
        // No reduction: the explored net *is* the raw snapshot, place ids are
        // identical.
        None => (0..net.num_places())
            .map(|index| (index, PlaceId(index)))
            .collect(),
    }
}

/// The roots that could not be located on the explored net. Any non-empty
/// result means slicing must fall back to the joint marking: a root whose
/// start token cannot be switched off would leak its executions into every
/// slice.
pub fn untranslatable_roots(
    roots: &[LibraryRootEntry],
    mapping: &HashMap<usize, PlaceId>,
) -> Vec<String> {
    roots
        .iter()
        .filter(|root| !mapping.contains_key(&root.start.index()))
        .map(|root| root.name.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use unipn::pt::{PtBuilder, PtPlaceKind, PtTransitionKind, TransitionType};

    fn bb() -> PtPlaceKind {
        PtPlaceKind::control(unipn::net::ControlSub::BasicBlock)
    }

    fn function_end() -> PtPlaceKind {
        PtPlaceKind::control(unipn::net::ControlSub::FunctionEnd)
    }

    fn root(name: &str, start: PlaceId, end: PlaceId) -> LibraryRootEntry {
        LibraryRootEntry {
            name: name.to_string(),
            start,
            end,
        }
    }

    /// `n` roots that all acquire the same `Mutex_0`.
    fn shared_mutex_roots(n: usize) -> (PtNet, Vec<LibraryRootEntry>) {
        let mut b = PtBuilder::new();
        let mutex = b.add_marked_place("Mutex_0", PtPlaceKind::resource(), 1);
        let mut roots = Vec::new();
        for i in 0..n {
            let start = b.add_marked_place(&format!("root{i}_start"), bb(), 1);
            let end = b.add_place(&format!("root{i}_end"), function_end());
            let t = b.add_transition("lock", PtTransitionKind::new(TransitionType::Normal));
            b.add_input_arc(start, t, 1);
            b.add_input_arc(mutex, t, 1);
            b.add_output_arc(end, t, 1);
            b.add_output_arc(mutex, t, 1);
            roots.push(root(&format!("root{i}"), start, end));
        }
        let (net, _) = b.build();
        (net, roots)
    }

    /// Every pair of roots that shares a synchronizing resource must co-occur
    /// in at least one slice, and no slice may start more than the cap.
    #[test]
    fn partition_covers_every_shared_resource_pair_within_the_cap() {
        let (net, roots) = shared_mutex_roots(5);
        let groups = group_roots(&net, &roots);
        assert_eq!(groups, vec![vec![0, 1, 2, 3, 4]]);

        let slices = partition_groups(&net, &roots, &groups, Some(3));
        assert!(slices.len() > 1, "an oversized group must be split");
        for slice in &slices {
            assert!(!slice.is_empty());
            assert!(slice.len() <= 3, "slice {slice:?} exceeds the cap");
        }
        // Every root still appears somewhere.
        let seen: BTreeSet<usize> = slices.iter().flatten().copied().collect();
        assert_eq!(seen, (0..5).collect::<BTreeSet<_>>());
        // Pair coverage: all ten pairs share `Mutex_0`.
        for a in 0..5 {
            for b in (a + 1)..5 {
                assert!(
                    slices.iter().any(|s| s.contains(&a) && s.contains(&b)),
                    "pair ({a}, {b}) is not covered"
                );
            }
        }
        // Deterministic output.
        assert_eq!(slices, partition_groups(&net, &roots, &groups, Some(3)));
    }

    /// A cross-root join pair is a required pair too, even though the two
    /// roots share no resource place.
    #[test]
    fn partition_keeps_cross_root_join_pairs_together() {
        let (mut b, mut roots) = {
            let mut b = PtBuilder::new();
            let mutex = b.add_marked_place("Mutex_0", PtPlaceKind::resource(), 1);
            let mut roots = Vec::new();
            // Roots 0 and 1 share the mutex.
            for i in 0..2 {
                let start = b.add_marked_place(&format!("root{i}_start"), bb(), 1);
                let end = b.add_place(&format!("root{i}_end"), function_end());
                let t = b.add_transition("lock", PtTransitionKind::new(TransitionType::Normal));
                b.add_input_arc(start, t, 1);
                b.add_input_arc(mutex, t, 1);
                b.add_output_arc(end, t, 1);
                b.add_output_arc(mutex, t, 1);
                roots.push(root(&format!("root{i}"), start, end));
            }
            (b, roots)
        };
        // Root 2 joins root 1's `_end` without reaching its `_start`.
        let join = b.add_place("root2_join", bb());
        let start2 = b.add_marked_place("root2_start", bb(), 1);
        let end2 = b.add_place("root2_end", function_end());
        let t = b.add_transition("join", PtTransitionKind::new(TransitionType::Normal));
        b.add_input_arc(start2, t, 1);
        b.add_input_arc(join, t, 1);
        b.add_output_arc(end2, t, 1);
        // `join` is a separate place fed from root 1's end, which keeps the
        // closure relation structural without consuming root 1's end token.
        let t = b.add_transition("feed", PtTransitionKind::new(TransitionType::Normal));
        b.add_input_arc(roots[1].end, t, 1);
        b.add_output_arc(join, t, 1);
        roots.push(root("root2", start2, end2));
        let (net, _) = b.build();

        let groups = group_roots(&net, &roots);
        assert_eq!(groups, vec![vec![0, 1, 2]]);
        let slices = partition_groups(&net, &roots, &groups, Some(2));
        for slice in &slices {
            assert!(slice.len() <= 2, "slice {slice:?} exceeds the cap");
        }
        assert!(
            slices.iter().any(|s| s.contains(&0) && s.contains(&1)),
            "the resource pair must stay together: {slices:?}"
        );
        assert!(
            slices.iter().any(|s| s.contains(&1) && s.contains(&2)),
            "the join pair must stay together: {slices:?}"
        );
    }

    /// `None`, `0`, or a cap that already covers every group leaves the
    /// grouping untouched (previous behaviour).
    #[test]
    fn partition_is_a_noop_without_a_cap_or_for_small_groups() {
        let (net, roots) = shared_mutex_roots(3);
        let groups = group_roots(&net, &roots);
        assert_eq!(groups, vec![vec![0, 1, 2]]);
        assert_eq!(partition_groups(&net, &roots, &groups, None), groups);
        assert_eq!(partition_groups(&net, &roots, &groups, Some(0)), groups);
        assert_eq!(partition_groups(&net, &roots, &groups, Some(3)), groups);
        assert_eq!(partition_groups(&net, &roots, &groups, Some(9)), groups);
    }

    /// A global state budget caps the merged graph: the last explored slice
    /// is cut to the remaining budget and later slices are counted as
    /// unexplored rather than silently explored past the budget.
    #[test]
    fn state_budget_bounds_the_merged_graph_and_reports_skipped_slices() {
        let mut b = PtBuilder::new();
        let mut roots = Vec::new();
        for i in 0..2 {
            let start = b.add_marked_place(&format!("root{i}_start"), bb(), 1);
            let end = b.add_place(&format!("root{i}_end"), function_end());
            let t = b.add_transition("step", PtTransitionKind::new(TransitionType::Normal));
            b.add_input_arc(start, t, 1);
            b.add_output_arc(end, t, 1);
            roots.push(root(&format!("root{i}"), start, end));
        }
        let (net, m0) = b.build();
        assert_eq!(
            group_roots(&net, &roots),
            vec![vec![0], vec![1]],
            "independent roots must slice separately"
        );
        let starts: Vec<PlaceId> = roots.iter().map(|r| r.start).collect();

        let unbudgeted = slice_state_graphs(
            &net,
            &m0,
            &roots,
            &starts,
            &[vec![0], vec![1]],
            Some(100),
            None,
            false,
            false,
        );
        assert_eq!(unbudgeted.layout.slices.len(), 2);
        assert_eq!(unbudgeted.layout.unexplored_slices, 0);
        assert_eq!(unbudgeted.graph.states.len(), 4);

        let budgeted = slice_state_graphs(
            &net,
            &m0,
            &roots,
            &starts,
            &[vec![0], vec![1]],
            Some(100),
            Some(2),
            false,
            false,
        );
        assert_eq!(
            budgeted.graph.states.len(),
            2,
            "the merged graph must stop at the budget"
        );
        assert_eq!(
            budgeted.layout.slices.len(),
            1,
            "the second slice is skipped whole"
        );
        assert_eq!(budgeted.layout.unexplored_slices, 1);
        assert_eq!(
            budgeted.layout.slices[0].entry_roots,
            vec!["root0".to_string()]
        );
        assert!(budgeted.graph.truncated);
    }

    use super as slices;
    use crate::report::{NO_EXCLUSIONS, ReportInputs, build_deadlock_report};
    use unipn::net::TransitionId;

    fn end() -> PtPlaceKind {
        PtPlaceKind::control(unipn::net::ControlSub::FunctionEnd)
    }

    fn res() -> PtPlaceKind {
        PtPlaceKind::resource()
    }

    fn add_t(
        b: &mut PtBuilder,
        name: &str,
        ty: TransitionType,
        pre: &[PlaceId],
        post: &[PlaceId],
    ) -> TransitionId {
        let t = b.add_transition(name, PtTransitionKind::new(ty));
        for &p in pre {
            b.add_input_arc(p, t, 1);
        }
        for &p in post {
            b.add_output_arc(p, t, 1);
        }
        t
    }

    /// The partition: roots that can reach the same non-atomic synchronizer
    /// share a slice; a root reachable only through an `Atomic(..)` place is a
    /// singleton (an atomic token is held for one transition, never across a
    /// wait, so it cannot make two roots deadlock against each other).
    #[test]
    fn slicing_groups_roots_by_shared_non_atomic_resources() {
        let mut b = PtBuilder::new();
        let mutex = b.add_marked_place("Mutex_0", res(), 1);
        let atomic = b.add_marked_place("Atomic(0,0)", res(), 1);
        let a0 = b.add_marked_place("a_start", bb(), 1);
        let a1 = b.add_marked_place("a_end", end(), 0);
        add_t(
            &mut b,
            "a locks",
            TransitionType::Lock(mutex.index()),
            &[a0, mutex],
            &[a1, mutex],
        );
        let c0 = b.add_marked_place("c_start", bb(), 1);
        let c1 = b.add_marked_place("c_end", end(), 0);
        add_t(
            &mut b,
            "c locks",
            TransitionType::Lock(mutex.index()),
            &[c0, mutex],
            &[c1, mutex],
        );
        let d0 = b.add_marked_place("d_start", bb(), 1);
        let d1 = b.add_marked_place("d_end", end(), 0);
        add_t(
            &mut b,
            "d atomics",
            TransitionType::AtomicLoad(
                unipn::AliasId {
                    instance_id: 0,
                    local: 0,
                    array_index: None,
                    field: None,
                },
                unipn::pt::AtomicOrdering::Relaxed,
                String::new(),
                0,
            ),
            &[d0, atomic],
            &[d1, atomic],
        );
        let (net, _) = b.build();

        let roots = vec![root("a", a0, a1), root("c", c0, c1), root("d", d0, d1)];
        let groups = slices::group_roots(&net, &roots);
        assert_eq!(groups, vec![vec![0, 1], vec![2]]);
    }

    /// A join on another root's `_end` that this root cannot produce itself
    /// (it cannot reach that root's `_start`) keeps the two roots together.
    #[test]
    fn slicing_keeps_cross_root_join_dependencies_together() {
        let mut b = PtBuilder::new();
        let a0 = b.add_marked_place("a_start", bb(), 1);
        let a1 = b.add_marked_place("a_end", end(), 0);
        let c0 = b.add_marked_place("c_start", bb(), 1);
        let c1 = b.add_marked_place("c_end", end(), 0);
        // `a` joins on `c_end`; nothing here produces `c_start` inside a.
        add_t(
            &mut b,
            "a joins c",
            TransitionType::Normal,
            &[a0, c1],
            &[a1],
        );
        let (net, _) = b.build();

        let roots = vec![root("a", a0, a1), root("c", c0, c1)];
        assert_eq!(slices::group_roots(&net, &roots), vec![vec![0, 1]]);
    }

    /// The merged graph keeps per-slice initials: σ for a candidate in the
    /// second slice starts at that slice's own initial state, and every
    /// candidate carries its `entry_root`.
    #[test]
    fn sliced_library_report_tags_candidates_and_restarts_sigma_per_slice() {
        let mut b = PtBuilder::new();
        let a0 = b.add_marked_place("alpha_start", bb(), 1);
        let a1 = b.add_marked_place("alpha_blocked", bb(), 0);
        let c0 = b.add_marked_place("beta_start", bb(), 1);
        let c1 = b.add_marked_place("beta_blocked", bb(), 0);
        // The never-enabled exits make the blocked place a wait (it has an
        // outgoing transition) rather than a structural sink.
        let a_gate = b.add_place("alpha_gate", bb());
        let c_gate = b.add_place("beta_gate", bb());
        add_t(&mut b, "alpha step", TransitionType::Normal, &[a0], &[a1]);
        add_t(&mut b, "beta step", TransitionType::Normal, &[c0], &[c1]);
        add_t(
            &mut b,
            "alpha exit",
            TransitionType::Normal,
            &[a1, a_gate],
            &[],
        );
        add_t(
            &mut b,
            "beta exit",
            TransitionType::Normal,
            &[c1, c_gate],
            &[],
        );
        let (net, m0) = b.build();

        let roots = vec![root("alpha", a0, a1), root("beta", c0, c1)];
        let groups = slices::group_roots(&net, &roots);
        assert_eq!(groups, vec![vec![0], vec![1]]);
        let starts = vec![a0, c0];
        let sliced = slices::slice_state_graphs(
            &net,
            &m0,
            &roots,
            &starts,
            &groups,
            Some(100),
            None,
            false,
            false,
        );
        assert_eq!(sliced.layout.slices.len(), 2);
        assert_eq!(sliced.layout.slices[0].initial_state, 0);
        assert_eq!(sliced.layout.slices[1].initial_state, 2);
        assert_eq!(sliced.graph.states.len(), 4);

        let report = build_deadlock_report(&ReportInputs {
            crate_name: "sliced",
            raw_net: &net,
            net: &net,
            state_graph: &sliced.graph,
            reduce_trace: None,
            excluded: &NO_EXCLUSIONS,
            entry_mode: "library-roots",
            slice_layout: Some(&sliced.layout),
        });
        assert_eq!(report["slicing"]["slice_count"], 2);
        assert_eq!(report["state_graph"]["deadlock_count"], 2);
        let deadlocks = report["deadlocks"].as_array().unwrap();
        assert_eq!(deadlocks[0]["entry_root"], "alpha");
        assert_eq!(deadlocks[1]["entry_root"], "beta");
        assert_eq!(deadlocks[0]["sigma"][0]["from_state"], 0);
        // The second slice's σ starts at its own initial state (offset 2),
        // not at the merged graph's state 0.
        assert_eq!(deadlocks[1]["sigma"][0]["from_state"], 2);
        assert_eq!(deadlocks[1]["sigma"][0]["to_state"], 3);
    }
}
