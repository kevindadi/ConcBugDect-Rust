use crate::report::{RaceCondition, RaceOperation, RaceReport};
use petgraph::graph::NodeIndex;
use std::time::Instant;
use unipn::analysis::pt::reachability::StateGraph;
use unipn::pt::TransitionType;

use rustc_data_structures::fx::FxHashMap;

pub struct DataRaceDetector<'a> {
    state_graph: &'a StateGraph,
}

impl<'a> DataRaceDetector<'a> {
    pub fn new(state_graph: &'a StateGraph) -> Self {
        Self { state_graph }
    }

    pub fn detect(&self) -> RaceReport {
        let start_time = Instant::now();
        let mut report = RaceReport::new("State Graph Data Race Detector".to_string());
        let mut race_infos = Vec::new();

        for state in self.state_graph.graph.node_indices() {
            let transitions = self.collect_state_accesses(state);
            if transitions.len() < 2 {
                continue;
            }

            let state_snapshot = self.state_snapshot(state);
            self.check_race_in_state(&transitions, state_snapshot, &mut race_infos);
        }

        let race_conditions = self.merge_race_conditions(race_infos);

        if !race_conditions.is_empty() {
            report.has_race = true;
            report.race_count = race_conditions.len();
            report.race_conditions = race_conditions;
        }

        report.analysis_time = start_time.elapsed();
        report
    }

    fn check_race_in_state(
        &self,
        transitions: &[StateAccess],
        state_marks: Vec<(usize, u8)>,
        race_infos: &mut Vec<RaceCondition>,
    ) {
        for (location_id, accesses) in Self::group_accesses_by_location(transitions) {
            let access_sites = Self::summarize_access_sites(accesses);
            if access_sites.len() < 2 {
                continue;
            }

            let Some((left, right)) = Self::select_best_race_pair(&access_sites) else {
                continue;
            };

            let mut operations = vec![
                Self::build_race_operation(&left),
                Self::build_race_operation(&right),
            ];
            operations.sort_by_key(Self::race_operation_signature);

            race_infos.push(RaceCondition {
                operations,
                variable_info: format!("Potential data race on variable {}", location_id),
                state: state_marks.clone(),
            });
        }
    }

    fn build_race_operation(access: &StateAccess) -> RaceOperation {
        RaceOperation {
            operation_type: access.op_type.to_string(),
            variable: access.data_type.clone(),
            location: access.span.clone(),
            basic_block: Some(access.basic_block),
        }
    }

    fn group_accesses_by_location<'b>(
        transitions: &'b [StateAccess],
    ) -> FxHashMap<usize, Vec<&'b StateAccess>> {
        let mut grouped: FxHashMap<usize, Vec<&'b StateAccess>> = FxHashMap::default();

        for access in transitions {
            grouped.entry(access.location_id).or_default().push(access);
        }

        grouped
    }

    fn summarize_access_sites(accesses: Vec<&StateAccess>) -> Vec<AccessSiteSummary> {
        let mut grouped: FxHashMap<AccessSiteKey, Vec<&StateAccess>> = FxHashMap::default();

        for access in accesses {
            grouped
                .entry(AccessSiteKey::from_access(access))
                .or_insert_with(Vec::new)
                .push(access);
        }

        let mut summaries = grouped
            .into_iter()
            .map(|(site, site_accesses)| AccessSiteSummary {
                sort_span: site_accesses
                    .iter()
                    .map(|access| access.span.clone())
                    .min()
                    .unwrap_or_default(),
                read_representative: Self::select_site_representative(&site_accesses, false)
                    .cloned(),
                write_representative: Self::select_site_representative(&site_accesses, true)
                    .cloned(),
                site,
            })
            .collect::<Vec<_>>();

        summaries.sort_by_key(|summary| {
            (
                summary.site.scope.clone(),
                summary.site.basic_block,
                summary.sort_span.clone(),
            )
        });
        summaries
    }

    fn select_site_representative<'b>(
        accesses: &[&'b StateAccess],
        prefer_write: bool,
    ) -> Option<&'b StateAccess> {
        accesses
            .iter()
            .copied()
            .filter(|access| access.is_write == prefer_write)
            .max_by_key(|access| Self::state_access_signature(access))
    }

    fn select_best_race_pair(
        access_sites: &[AccessSiteSummary],
    ) -> Option<(StateAccess, StateAccess)> {
        let mut best_pair = None;

        for (index, left_site) in access_sites.iter().enumerate() {
            for right_site in access_sites.iter().skip(index + 1) {
                for (left, right) in Self::candidate_pairs(left_site, right_site) {
                    let score = Self::pair_priority(left, right);
                    match &best_pair {
                        Some((best_score, _, _)) if *best_score >= score => {}
                        _ => best_pair = Some((score, left.clone(), right.clone())),
                    }
                }
            }
        }

        best_pair.map(|(_, left, right)| (left, right))
    }

    fn candidate_pairs<'b>(
        left_site: &'b AccessSiteSummary,
        right_site: &'b AccessSiteSummary,
    ) -> Vec<(&'b StateAccess, &'b StateAccess)> {
        let mut candidates = Vec::new();

        for left in [
            left_site.read_representative.as_ref(),
            left_site.write_representative.as_ref(),
        ]
        .into_iter()
        .flatten()
        {
            for right in [
                right_site.read_representative.as_ref(),
                right_site.write_representative.as_ref(),
            ]
            .into_iter()
            .flatten()
            {
                if left.is_write || right.is_write {
                    candidates.push((left, right));
                }
            }
        }

        candidates
    }

    fn pair_priority(left: &StateAccess, right: &StateAccess) -> PairPriority {
        let mut signatures = [
            Self::state_access_signature(left),
            Self::state_access_signature(right),
        ];
        signatures.sort();

        (
            Self::pair_quality(left, right),
            usize::from(Self::forms_mixed_access_pair(left, right)),
            Self::pair_specificity(left, right),
            signatures[1].clone(),
            signatures[0].clone(),
        )
    }

    fn pair_quality(left: &StateAccess, right: &StateAccess) -> usize {
        Self::access_quality(left) + Self::access_quality(right)
    }

    fn pair_specificity(left: &StateAccess, right: &StateAccess) -> usize {
        Self::state_access_specificity(left) + Self::state_access_specificity(right)
    }

    fn forms_mixed_access_pair(left: &StateAccess, right: &StateAccess) -> bool {
        left.is_write != right.is_write
    }

    fn access_quality(access: &StateAccess) -> usize {
        Self::data_type_priority(&access.data_type)
    }

    fn state_access_specificity(access: &StateAccess) -> usize {
        Self::access_quality(access) * 2 + usize::from(access.is_write)
    }

    fn data_type_priority(data_type: &str) -> usize {
        Self::data_type_category(data_type).priority()
    }

    fn data_type_category(data_type: &str) -> DataTypeCategory {
        let data_type = place_type_name(data_type);

        if data_type.contains("Closure(") {
            DataTypeCategory::ClosureCapture
        } else if data_type.contains("JoinHandle") {
            DataTypeCategory::ThreadHandle
        } else if data_type.starts_with("*const ") || data_type.starts_with("*mut ") {
            DataTypeCategory::RawPointer
        } else if is_scalar_like_type(data_type) {
            DataTypeCategory::Scalar
        } else {
            DataTypeCategory::Wrapper
        }
    }

    fn merge_race_conditions(&self, conditions: Vec<RaceCondition>) -> Vec<RaceCondition> {
        let mut merged: FxHashMap<String, RaceCondition> = FxHashMap::default();

        for condition in conditions {
            merged
                .entry(condition.variable_info.clone())
                .and_modify(|existing| {
                    if Self::race_condition_priority(&condition)
                        > Self::race_condition_priority(existing)
                    {
                        *existing = condition.clone();
                    }
                })
                .or_insert(condition);
        }

        let mut deduped = merged.into_values().collect::<Vec<_>>();
        deduped.sort_by_key(|condition| condition.variable_info.clone());
        deduped
    }

    fn race_condition_priority(condition: &RaceCondition) -> RaceConditionPriority {
        let mut operation_priorities = condition
            .operations
            .iter()
            .map(Self::race_operation_priority)
            .collect::<Vec<_>>();
        operation_priorities.sort();

        (
            Self::race_condition_quality(condition),
            usize::from(Self::has_mixed_access_types(condition)),
            Self::race_condition_specificity(&operation_priorities),
            operation_priorities,
            Self::race_condition_key(condition),
        )
    }

    fn race_condition_quality(condition: &RaceCondition) -> usize {
        condition
            .operations
            .iter()
            .map(Self::race_operation_quality)
            .sum()
    }

    fn race_condition_specificity(operation_priorities: &[RaceOperationPriority]) -> usize {
        operation_priorities.iter().map(|priority| priority.0).sum()
    }

    fn has_mixed_access_types(condition: &RaceCondition) -> bool {
        condition
            .operations
            .iter()
            .any(|operation| operation.operation_type == "read")
            && condition
                .operations
                .iter()
                .any(|operation| operation.operation_type == "write")
    }

    fn race_condition_key(condition: &RaceCondition) -> RaceConditionKey {
        let mut operations = condition
            .operations
            .iter()
            .map(Self::race_operation_signature)
            .collect::<Vec<_>>();
        operations.sort();

        (condition.variable_info.clone(), operations)
    }

    fn race_operation_priority(operation: &RaceOperation) -> RaceOperationPriority {
        (
            Self::race_operation_quality(operation),
            operation.operation_type.clone(),
            operation.variable.clone(),
            operation.basic_block.unwrap_or_default(),
            operation.location.clone(),
        )
    }

    fn race_operation_quality(operation: &RaceOperation) -> usize {
        Self::data_type_priority(&operation.variable)
    }

    fn race_operation_signature(operation: &RaceOperation) -> RaceOperationSignature {
        (
            operation.operation_type.clone(),
            operation.variable.clone(),
            operation.basic_block.unwrap_or_default(),
            operation.location.clone(),
        )
    }

    fn state_access_signature(access: &StateAccess) -> StateAccessSignature {
        (
            usize::from(access.is_write),
            Self::access_quality(access),
            access.op_type.to_string(),
            access.data_type.clone(),
            access.basic_block,
            access.span.clone(),
            access.transition_name.clone(),
        )
    }

    fn collect_state_accesses(&self, state: NodeIndex) -> Vec<StateAccess> {
        let mut accesses = Vec::new();

        for edge in self.state_graph.graph.edges(state) {
            match &edge.weight().transition.transition_type {
                TransitionType::UnsafeRead(alias_id, span, basic_block, place_ty) => {
                    accesses.push(StateAccess {
                        location_id: *alias_id,
                        span: span.clone(),
                        basic_block: *basic_block,
                        op_type: "read",
                        data_type: place_ty.clone(),
                        is_write: false,
                        transition_name: edge.weight().transition.name.clone(),
                    });
                }
                TransitionType::UnsafeWrite(alias_id, span, basic_block, place_ty) => {
                    accesses.push(StateAccess {
                        location_id: *alias_id,
                        span: span.clone(),
                        basic_block: *basic_block,
                        op_type: "write",
                        data_type: place_ty.clone(),
                        is_write: true,
                        transition_name: edge.weight().transition.name.clone(),
                    });
                }
                TransitionType::UnsafeAccess(ops) => {
                    // One merged transition per block may touch several
                    // variables; expand it into per-variable accesses.
                    for op in ops {
                        accesses.push(StateAccess {
                            location_id: op.alias,
                            span: op.span.clone(),
                            basic_block: op.basic_block,
                            op_type: if op.is_write { "write" } else { "read" },
                            data_type: op.ty.clone(),
                            is_write: op.is_write,
                            transition_name: edge.weight().transition.name.clone(),
                        });
                    }
                }
                _ => {}
            }
        }

        accesses
    }

    fn state_snapshot(&self, state: NodeIndex) -> Vec<(usize, u8)> {
        let node = self.state_graph.node(state);
        node.marking
            .iter()
            .filter_map(|(place_id, tokens)| {
                if *tokens == 0 {
                    return None;
                }
                Some((place_id.index(), (*tokens).min(u8::MAX as u64) as u8))
            })
            .collect()
    }
}

type RaceOperationSignature = (String, String, usize, String);
type StateAccessSignature = (usize, usize, String, String, usize, String, String);
type RaceConditionKey = (String, Vec<RaceOperationSignature>);
type RaceOperationPriority = (usize, String, String, usize, String);
type RaceConditionPriority = (
    usize,
    usize,
    usize,
    Vec<RaceOperationPriority>,
    RaceConditionKey,
);
type PairPriority = (
    usize,
    usize,
    usize,
    StateAccessSignature,
    StateAccessSignature,
);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum DataTypeCategory {
    ClosureCapture,
    ThreadHandle,
    Wrapper,
    RawPointer,
    Scalar,
}

impl DataTypeCategory {
    fn priority(self) -> usize {
        match self {
            Self::ClosureCapture => 0,
            Self::ThreadHandle => 1,
            Self::Wrapper => 2,
            Self::RawPointer => 3,
            Self::Scalar => 4,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct AccessSiteKey {
    scope: String,
    basic_block: usize,
}

impl AccessSiteKey {
    fn from_access(access: &StateAccess) -> Self {
        Self {
            scope: transition_scope_key(&access.transition_name),
            basic_block: access.basic_block,
        }
    }
}

#[derive(Debug, Clone)]
struct AccessSiteSummary {
    site: AccessSiteKey,
    sort_span: String,
    read_representative: Option<StateAccess>,
    write_representative: Option<StateAccess>,
}

#[derive(Debug, Clone)]
struct StateAccess {
    location_id: usize,
    span: String,
    basic_block: usize,
    op_type: &'static str,
    data_type: String,
    is_write: bool,
    transition_name: String,
}

fn transition_scope_key(name: &str) -> String {
    let suffix_start = [name.rfind("_read_"), name.rfind("_write_")]
        .into_iter()
        .flatten()
        .max();

    suffix_start
        .map(|index| name[..index].to_string())
        .unwrap_or_else(|| name.to_string())
}

fn place_type_name(data_type: &str) -> &str {
    data_type
        .split("ty: ")
        .nth(1)
        .and_then(|suffix| suffix.split(", variant_index").next())
        .unwrap_or(data_type)
}

fn is_scalar_like_type(data_type: &str) -> bool {
    matches!(
        data_type,
        "i8" | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "f32"
            | "f64"
            | "bool"
            | "char"
    )
}
