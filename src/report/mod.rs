use serde::{Deserialize, Serialize};
use std::fmt;
use std::time::Duration;

const REPORT_WIDTH: usize = 64;

fn write_banner(f: &mut fmt::Formatter<'_>, title: &str) -> fmt::Result {
    writeln!(
        f,
        "{:=^width$}",
        format!(" {} ", title),
        width = REPORT_WIDTH
    )
}

fn write_section(f: &mut fmt::Formatter<'_>, title: &str) -> fmt::Result {
    writeln!(
        f,
        "\n{:-^width$}",
        format!(" {} ", title),
        width = REPORT_WIDTH
    )
}

fn format_duration(duration: Duration) -> String {
    if duration.is_zero() {
        "0.000 s".to_string()
    } else {
        format!("{:.3} s", duration.as_secs_f64())
    }
}

const INCIDENT_SCHEMA_VERSION: &str = "2";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IncidentReport {
    pub schema_version: String,
    pub tool: String,
    pub mode: String,
    pub result: String,
    pub severity: String,
    pub confidence: ConfidenceInfo,
    pub summary: IncidentSummary,
    pub incidents: Vec<Incident>,
    pub analysis_time: String,
    pub artifacts: ReportArtifacts,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfidenceInfo {
    pub level: String,
    pub reasons: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IncidentSummary {
    pub bug_count: usize,
    pub state_space: Option<StateSpaceInfo>,
    pub primary_locations: Vec<SourceLocation>,
    pub explanation: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceLocation {
    pub file: Option<String>,
    pub line: Option<usize>,
    pub column: Option<usize>,
    pub message: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Incident {
    pub id: String,
    pub kind: String,
    pub state_id: Option<String>,
    pub what_happened: String,
    pub where_to_look: Vec<SourceLocation>,
    pub developer_explanation: String,
    pub diagnosis: IncidentDiagnosis,
    pub evidence: IncidentEvidence,
    pub suggested_next_steps: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IncidentDiagnosis {
    pub blocked_resources: Vec<String>,
    pub conflicting_operations: Vec<String>,
    pub why_bug: String,
    /// Resource-related transitions that are blocked in this deadlock state
    pub blocked_operations: Vec<BlockedTransition>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IncidentEvidence {
    pub state: Vec<(usize, u8)>,
    pub incoming_trace: Vec<String>,
    pub marking: Vec<MarkingEvidence>,
    pub token_changes: Vec<String>,
    pub artifacts: ReportArtifacts,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MarkingEvidence {
    pub place: String,
    pub tokens: u8,
    pub span: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReportArtifacts {
    pub stategraph: String,
    pub petrinet: String,
    pub summary: String,
}

impl fmt::Display for IncidentReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_banner(f, "RustPTA Bug Report")?;
        writeln!(f)?;
        writeln!(f, "Result        : {}", result_text(&self.result))?;
        writeln!(f, "Mode          : {}", self.mode)?;
        writeln!(f, "Bug count     : {}", self.summary.bug_count)?;
        writeln!(f, "Severity      : {}", self.severity)?;
        writeln!(f, "Confidence    : {}", self.confidence.level)?;
        if let Some(info) = &self.summary.state_space {
            writeln!(
                f,
                "State space   : states={}, edges={}, reachable={}",
                info.total_states, info.total_transitions, info.reachable_states
            )?;
        }
        writeln!(
            f,
            "Artifacts     : {}, {}, {}",
            self.artifacts.summary, self.artifacts.stategraph, self.artifacts.petrinet
        )?;
        writeln!(f, "Analysis time : {}", self.analysis_time)?;

        if !self.summary.explanation.is_empty() {
            writeln!(f)?;
            writeln!(f, "Developer explanation:")?;
            writeln!(f, "  {}", self.summary.explanation)?;
        }

        for incident in &self.incidents {
            write_section(f, &format!("Incident {}", incident.id))?;
            writeln!(f)?;
            writeln!(f, "What happened:")?;
            writeln!(f, "  {}", incident.what_happened)?;
            if !incident.diagnosis.blocked_operations.is_empty() {
                writeln!(f)?;
                writeln!(f, "  blocked ops    :")?;
                for operation in &incident.diagnosis.blocked_operations {
                    let location = if operation.location.is_empty() {
                        "unknown source"
                    } else {
                        operation.location.as_str()
                    };
                    writeln!(
                        f,
                        "    - {} [{}] at {}",
                        operation.name, operation.operation, location
                    )?;
                    if !operation.needed_resources.is_empty() {
                        writeln!(f, "      needs: {}", operation.needed_resources.join(", "))?;
                    }
                    for resource in &operation.resource_status {
                        writeln!(
                            f,
                            "      resource {}: has {}, needs {}",
                            resource.resource_name, resource.has, resource.needs
                        )?;
                    }
                    if !operation.resource_trace.is_empty() {
                        writeln!(f, "      last resource use:")?;
                        for step in &operation.resource_trace {
                            writeln!(
                                f,
                                "        {} -> {}: {} [{}] at {}",
                                step.from_state,
                                step.to_state,
                                step.transition_name,
                                step.operation,
                                step.location
                            )?;
                            writeln!(
                                f,
                                "        {}: {} -> {}",
                                step.resource_name, step.before, step.after
                            )?;
                        }
                    }
                }
            }
            if incident.kind != "deadlock"
                && incident.kind != "datarace"
                && !incident.where_to_look.is_empty()
            {
                writeln!(f)?;
                writeln!(f, "Where to look:")?;
                for (index, location) in incident.where_to_look.iter().enumerate() {
                    writeln!(
                        f,
                        "  {}. {:<32} {}",
                        index + 1,
                        render_source_location(location),
                        location.message
                    )?;
                }
            }
            if incident.kind != "deadlock"
                && incident.kind != "datarace"
                && !incident.developer_explanation.is_empty()
            {
                writeln!(f)?;
                writeln!(f, "Developer explanation:")?;
                writeln!(f, "  {}", incident.developer_explanation)?;
            }
            writeln!(f)?;
            if incident.kind == "deadlock" {
                writeln!(f, "Deadlock state:")?;
                if let Some(state_id) = &incident.state_id {
                    writeln!(f, "  state id : {}", state_id)?;
                }
                writeln!(f, "  reason   : {}", incident.diagnosis.why_bug)?;

                let active_places = incident
                    .evidence
                    .marking
                    .iter()
                    .filter(|mark| mark.span.is_some())
                    .collect::<Vec<_>>();
                let resource_places = incident
                    .evidence
                    .marking
                    .iter()
                    .filter(|mark| mark.span.is_none())
                    .collect::<Vec<_>>();

                if !active_places.is_empty() {
                    writeln!(f)?;
                    writeln!(f, "  active control places:")?;
                    for mark in active_places {
                        let span = mark.span.as_deref().unwrap_or_default();
                        writeln!(f, "    - {} tokens={} at {}", mark.place, mark.tokens, span)?;
                    }
                }

                if !resource_places.is_empty() {
                    writeln!(f)?;
                    writeln!(f, "  resource tokens:")?;
                    for mark in resource_places {
                        writeln!(f, "    - {} tokens={}", mark.place, mark.tokens)?;
                    }
                }
            } else if incident.kind == "datarace" {
                writeln!(f, "Key unsafe accesses:")?;
                if !incident.where_to_look.is_empty() {
                    for (index, location) in incident.where_to_look.iter().enumerate() {
                        let detail = incident
                            .diagnosis
                            .conflicting_operations
                            .get(index)
                            .map(String::as_str)
                            .unwrap_or(location.message.as_str());
                        writeln!(
                            f,
                            "  {}. {:<32} {}",
                            index + 1,
                            render_source_location(location),
                            detail
                        )?;
                    }
                } else {
                    for operation in &incident.diagnosis.conflicting_operations {
                        writeln!(f, "  - {}", operation)?;
                    }
                }

                if let Some(state_summary) = summarize_datarace_marking(&incident.evidence.marking) {
                    writeln!(f)?;
                    writeln!(f, "Enabled state:")?;
                    writeln!(f, "  {}", state_summary)?;
                }
            } else if incident.kind == "atomicity_violation" {
                writeln!(f, "Candidate atomic pattern:")?;
                if let Some((load, stores)) = incident.diagnosis.conflicting_operations.split_first() {
                    writeln!(f, "  load:")?;
                    writeln!(f, "    - {}", load)?;
                    if !stores.is_empty() {
                        writeln!(f, "  competing stores:")?;
                        for store in stores {
                            writeln!(f, "    - {}", store)?;
                        }
                    }
                }
                writeln!(f)?;
                writeln!(f, "Pattern note:")?;
                writeln!(
                    f,
                    "  state-graph reachability can include operations from alternative branches unless a witness trace is available."
                )?;
                writeln!(f, "  why bug: {}", incident.diagnosis.why_bug)?;
            } else {
                writeln!(f, "State evidence:")?;
                if let Some(state_id) = &incident.state_id {
                    writeln!(f, "  state id       : {}", state_id)?;
                }
                if !incident.evidence.incoming_trace.is_empty() {
                    writeln!(
                        f,
                        "  incoming trace : {}",
                        incident.evidence.incoming_trace.join(" -> ")
                    )?;
                }
                if !incident.diagnosis.conflicting_operations.is_empty() {
                    writeln!(f, "  conflicts      :")?;
                    for operation in &incident.diagnosis.conflicting_operations {
                        writeln!(f, "    - {}", operation)?;
                    }
                }
                writeln!(f, "  why bug        : {}", incident.diagnosis.why_bug)?;
                writeln!(f)?;
                writeln!(f, "Relevant marking:")?;
                if incident.evidence.marking.is_empty() {
                    writeln!(f, "  No marked places were recorded for this incident.")?;
                } else {
                    for mark in &incident.evidence.marking {
                        if let Some(span) = mark.span.as_deref() {
                            writeln!(f, "  - {} tokens={} at {}", mark.place, mark.tokens, span)?;
                        } else {
                            writeln!(f, "  - {} tokens={}", mark.place, mark.tokens)?;
                        }
                    }
                }
            }
            writeln!(f)?;
            if incident.kind != "datarace" && !incident.suggested_next_steps.is_empty() {
                writeln!(f, "Suggested next steps:")?;
                for step in &incident.suggested_next_steps {
                    writeln!(f, "  - {}", step)?;
                }
            }
        }

        if let Some(error) = &self.error {
            write_section(f, "Errors")?;
            writeln!(f, "{}", error)?;
        }

        Ok(())
    }
}

fn bug_result(has_bug: bool) -> String {
    if has_bug { "bug_found" } else { "no_bug_found" }.to_string()
}

fn result_text(result: &str) -> &'static str {
    if result == "bug_found" {
        "BUG FOUND"
    } else {
        "NO BUG FOUND"
    }
}

fn default_artifacts() -> ReportArtifacts {
    ReportArtifacts {
        stategraph: "stategraph.dot".to_string(),
        petrinet: "petrinet.dot".to_string(),
        summary: "summary.json".to_string(),
    }
}

fn remove_legacy_json_sidecar(path: &str) -> std::io::Result<()> {
    let json_path = format!("{path}.json");
    match std::fs::remove_file(json_path) {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(err) => Err(err),
    }
}

fn default_confidence(has_bug: bool) -> ConfidenceInfo {
    ConfidenceInfo {
        level: if has_bug { "medium" } else { "high" }.to_string(),
        reasons: if has_bug {
            vec![
                "bug is derived from a reachable Petri-net state".to_string(),
                "source spans are preserved when MIR lowering provides them".to_string(),
            ]
        } else {
            vec!["no matching bug state was found in the explored state graph".to_string()]
        },
    }
}

fn source_location(message: impl Into<String>, location: &str) -> SourceLocation {
    let message = message.into();
    let raw = location.trim_matches('"');
    let mut parts = raw.rsplitn(3, ':').collect::<Vec<_>>();
    parts.reverse();

    if parts.len() == 3 {
        SourceLocation {
            file: Some(parts[0].to_string()),
            line: parts[1].parse().ok(),
            column: parts[2].parse().ok(),
            message,
        }
    } else {
        SourceLocation {
            file: None,
            line: None,
            column: None,
            message: format!("{message} ({raw})"),
        }
    }
}

/// Information about a resource's current status relative to what's needed.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceStatus {
    /// Name of the resource (e.g., Mutex_0, RwLock_1)
    pub resource_name: String,
    /// Current tokens available for this resource
    pub has: usize,
    /// Tokens required by the transition
    pub needs: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceTraceStep {
    pub resource_name: String,
    pub transition_name: String,
    pub operation: String,
    pub location: String,
    pub from_state: String,
    pub to_state: String,
    pub before: usize,
    pub after: usize,
}

/// A resource-related transition that is blocked in a deadlock state.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockedTransition {
    /// The transition identifier
    pub id: String,
    /// Human-readable name like "Foo::mutex_lock_1"
    pub name: String,
    /// Source location (e.g., "src/main.rs:28:20")
    pub location: String,
    /// What kind of resource operation (Lock, RwLockRead, RwLockWrite, etc.)
    pub operation: String,
    /// Resource IDs this transition needs (e.g., Mutex_0, RwLock_1)
    pub needed_resources: Vec<String>,
    /// For each needed resource: current tokens vs required tokens
    pub resource_status: Vec<ResourceStatus>,
    pub resource_trace: Vec<ResourceTraceStep>,
}

fn render_source_location(location: &SourceLocation) -> String {
    match (&location.file, location.line, location.column) {
        (Some(file), Some(line), Some(column)) => format!("{file}:{line}:{column}"),
        (Some(file), Some(line), None) => format!("{file}:{line}"),
        (Some(file), None, _) => file.clone(),
        _ => "unknown source".to_string(),
    }
}

fn summarize_datarace_marking(marking: &[MarkingEvidence]) -> Option<String> {
    if marking.is_empty() {
        return None;
    }

    let human_readable = marking
        .iter()
        .filter(|mark| mark.span.is_some() || !mark.place.starts_with("place#"))
        .collect::<Vec<_>>();

    if human_readable.is_empty() {
        return Some(format!(
            "{} Petri-net places are marked in the witness state.",
            marking.len()
        ));
    }

    Some(
        human_readable
            .into_iter()
            .map(|mark| {
                if let Some(span) = mark.span.as_deref() {
                    format!("{} tokens={} at {}", mark.place, mark.tokens, span)
                } else {
                    format!("{} tokens={}", mark.place, mark.tokens)
                }
            })
            .collect::<Vec<_>>()
            .join("; "),
    )
}

fn marking_evidence(place: &str, tokens: u8) -> MarkingEvidence {
    if let Some((name, span)) = place.split_once(" (") {
        MarkingEvidence {
            place: name.to_string(),
            tokens,
            span: span
                .strip_suffix(')')
                .filter(|span| !span.is_empty())
                .map(str::to_string),
        }
    } else {
        MarkingEvidence {
            place: place.to_string(),
            tokens,
            span: None,
        }
    }
}

fn primary_locations(incidents: &[Incident]) -> Vec<SourceLocation> {
    incidents
        .iter()
        .flat_map(|incident| incident.where_to_look.iter().cloned())
        .take(5)
        .collect()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadlockState {
    pub state_id: String,
    pub marking: Vec<(String, u8)>,
    pub description: String,
    /// Transitions that are blocked due to missing resources
    pub blocked_transitions: Vec<BlockedTransition>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadlockTrace {
    pub steps: Vec<String>,
    pub final_state: Option<DeadlockState>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadlockReport {
    pub tool_name: String,
    pub has_deadlock: bool,
    pub deadlock_count: usize,
    pub deadlock_states: Vec<DeadlockState>,
    pub traces: Vec<DeadlockTrace>,
    pub analysis_time: Duration,
    pub state_space_info: Option<StateSpaceInfo>,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateSpaceInfo {
    pub total_states: usize,
    pub total_transitions: usize,
    pub reachable_states: usize,
}

impl fmt::Display for DeadlockReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_incident_report().fmt(f)
    }
}

impl DeadlockReport {
    pub fn new(tool_name: String) -> Self {
        Self {
            tool_name,
            has_deadlock: false,
            deadlock_count: 0,
            deadlock_states: Vec::new(),
            traces: Vec::new(),
            analysis_time: Duration::default(),
            state_space_info: None,
            error: None,
        }
    }

    pub fn to_incident_report(&self) -> IncidentReport {
        let artifacts = default_artifacts();
        let incidents = self
            .deadlock_states
            .iter()
            .enumerate()
            .map(|(index, state)| {
                let trace = self
                    .traces
                    .get(index)
                    .map(|trace| trace.steps.clone())
                    .unwrap_or_default();
                let marking = state
                    .marking
                    .iter()
                    .map(|(place, tokens)| marking_evidence(place, *tokens))
                    .collect::<Vec<_>>();
                let where_to_look = Vec::new();

                Incident {
                    id: format!("deadlock-{}", index + 1),
                    kind: "deadlock".to_string(),
                    state_id: Some(state.state_id.clone()),
                    what_happened: "A reachable global state has no progress transition before normal termination.".to_string(),
                    where_to_look,
                    developer_explanation: String::new(),
                    diagnosis: IncidentDiagnosis {
                        blocked_resources: marking
                            .iter()
                            .filter(|mark| mark.tokens == 0)
                            .map(|mark| mark.place.clone())
                            .collect(),
                        conflicting_operations: Vec::new(),
                        why_bug: state.description.clone(),
                        blocked_operations: state.blocked_transitions.clone(),
                    },
                    evidence: IncidentEvidence {
                        state: Vec::new(),
                        incoming_trace: trace,
                        marking,
                        token_changes: Vec::new(),
                        artifacts: artifacts.clone(),
                    },
                    suggested_next_steps: vec![
                        "Check whether locks are acquired in inconsistent order across threads or async roots.".to_string(),
                        "Inspect active control-flow places with tokens to identify the blocked execution roots.".to_string(),
                        "Open stategraph.dot around this state and petrinet.dot around the listed places.".to_string(),
                    ],
                }
            })
            .collect::<Vec<_>>();

        IncidentReport {
            schema_version: INCIDENT_SCHEMA_VERSION.to_string(),
            tool: "RustPTA".to_string(),
            mode: "deadlock".to_string(),
            result: bug_result(self.has_deadlock),
            severity: if self.has_deadlock { "high" } else { "none" }.to_string(),
            confidence: default_confidence(self.has_deadlock),
            summary: IncidentSummary {
                bug_count: self.deadlock_count,
                state_space: self.state_space_info.clone(),
                primary_locations: primary_locations(&incidents),
                explanation: if self.has_deadlock {
                    "The blocked operations list shows which transition cannot fire, which resource it needs, and the most recent resource-consuming step found on a witness path to the deadlock state.".to_string()
                } else {
                    "No deadlock state was found in the explored state graph.".to_string()
                },
            },
            incidents,
            analysis_time: format_duration(self.analysis_time),
            artifacts,
            error: self.error.clone(),
        }
    }

    pub fn save_to_file(&self, path: &str) -> std::io::Result<()> {
        use std::fs::File;
        use std::io::Write;

        let mut file = File::create(path)?;
        writeln!(file, "{}", self)?;
        remove_legacy_json_sidecar(path)?;

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AtomicOperation {
    pub operation_type: String,
    pub ordering: String,
    pub variable: String,
    pub location: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AtomicViolation {
    pub pattern: ViolationPattern,
    pub states: Vec<(usize, u8)>,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct ViolationPattern {
    pub load_op: AtomicOperation,
    pub store_ops: Vec<AtomicOperation>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AtomicReport {
    pub tool_name: String,
    pub has_violation: bool,
    pub violation_count: usize,
    pub violations: Vec<ViolationPattern>,
    pub analysis_time: Duration,
    pub error: Option<String>,
}

impl fmt::Display for AtomicReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_incident_report().fmt(f)
    }
}

impl AtomicReport {
    pub fn new(tool_name: String) -> Self {
        Self {
            tool_name,
            has_violation: false,
            violation_count: 0,
            violations: Vec::new(),
            analysis_time: Duration::default(),
            error: None,
        }
    }

    pub fn to_incident_report(&self) -> IncidentReport {
        let artifacts = default_artifacts();
        let incidents = self
            .violations
            .iter()
            .enumerate()
            .map(|(index, violation)| {
                let mut operations = vec![format!(
                    "{} {} at {} ({})",
                    violation.load_op.operation_type,
                    violation.load_op.variable,
                    violation.load_op.location,
                    violation.load_op.ordering
                )];
                operations.extend(violation.store_ops.iter().map(|store| {
                    format!(
                        "{} {} at {} ({})",
                        store.operation_type, store.variable, store.location, store.ordering
                    )
                }));

                let mut where_to_look = vec![source_location(
                    format!(
                        "{} {}",
                        violation.load_op.operation_type, violation.load_op.variable
                    ),
                    &violation.load_op.location,
                )];
                where_to_look.extend(violation.store_ops.iter().map(|store| {
                    source_location(
                        format!("{} {}", store.operation_type, store.variable),
                        &store.location,
                    )
                }));

                Incident {
                    id: format!("atomicity-{}", index + 1),
                    kind: "atomicity_violation".to_string(),
                    state_id: None,
                    what_happened: "A load can observe an atomic variable after multiple competing stores under the modeled ordering constraints.".to_string(),
                    where_to_look,
                    developer_explanation: "The state graph contains paths where the listed stores can reach the load without a stronger ordering edge that forces a single intended write-before-read relationship.".to_string(),
                    diagnosis: IncidentDiagnosis {
                        blocked_resources: Vec::new(),
                        conflicting_operations: operations,
                        why_bug: "Multiple stores to the same atomic location are compatible with the load under the modeled ordering relation.".to_string(),
                        blocked_operations: Vec::new(),
                    },
                    evidence: IncidentEvidence {
                        state: Vec::new(),
                        incoming_trace: Vec::new(),
                        marking: Vec::new(),
                        token_changes: Vec::new(),
                        artifacts: artifacts.clone(),
                    },
                    suggested_next_steps: vec![
                        "Check whether the stores should be mutually exclusive or ordered before the load.".to_string(),
                        "Consider stronger ordering or a separate synchronization edge if the load expects one writer.".to_string(),
                        "Inspect stategraph.dot around the reported atomic load and stores.".to_string(),
                    ],
                }
            })
            .collect::<Vec<_>>();

        IncidentReport {
            schema_version: INCIDENT_SCHEMA_VERSION.to_string(),
            tool: "RustPTA".to_string(),
            mode: "atomic".to_string(),
            result: bug_result(self.has_violation),
            severity: if self.has_violation { "medium" } else { "none" }.to_string(),
            confidence: default_confidence(self.has_violation),
            summary: IncidentSummary {
                bug_count: self.violation_count,
                state_space: None,
                primary_locations: primary_locations(&incidents),
                explanation: if self.has_violation {
                    "At least one atomic load is reachable with multiple competing stores."
                        .to_string()
                } else {
                    "No modeled atomicity violation pattern was found.".to_string()
                },
            },
            incidents,
            analysis_time: format_duration(self.analysis_time),
            artifacts,
            error: self.error.clone(),
        }
    }

    pub fn save_to_file(&self, path: &str) -> std::io::Result<()> {
        use std::fs::File;
        use std::io::Write;

        let mut file = File::create(path)?;
        writeln!(file, "{}", self)?;
        remove_legacy_json_sidecar(path)?;

        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RaceOperation {
    pub operation_type: String,
    pub variable: String,
    pub location: String,
    pub basic_block: Option<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RaceCondition {
    pub operations: Vec<RaceOperation>,
    pub variable_info: String,
    pub state: Vec<(usize, u8)>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VariableInfo {
    pub name: String,
    pub data_type: String,
    pub function_scope: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RaceReport {
    pub tool_name: String,
    pub has_race: bool,
    pub race_count: usize,
    pub race_conditions: Vec<RaceCondition>,
    pub analysis_time: Duration,
    pub error: Option<String>,
}

impl fmt::Display for RaceReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_incident_report().fmt(f)
    }
}

impl RaceReport {
    pub fn new(tool_name: String) -> Self {
        Self {
            tool_name,
            has_race: false,
            race_count: 0,
            race_conditions: Vec::new(),
            analysis_time: Duration::default(),
            error: None,
        }
    }

    pub fn to_incident_report(&self) -> IncidentReport {
        let artifacts = default_artifacts();
        let incidents = self
            .race_conditions
            .iter()
            .enumerate()
            .map(|(index, race)| {
                let conflicting_operations = race
                    .operations
                    .iter()
                    .map(|op| {
                        if let Some(basic_block) = op.basic_block {
                            format!("{} {} (bb{})", op.operation_type, op.variable, basic_block)
                        } else {
                            format!("{} {}", op.operation_type, op.variable)
                        }
                    })
                    .collect::<Vec<_>>();
                let where_to_look = race
                    .operations
                    .iter()
                    .map(|op| {
                        source_location(format!("{} {}", op.operation_type, op.variable), &op.location)
                    })
                    .collect::<Vec<_>>();
                let marking = race
                    .state
                    .iter()
                    .map(|(place, tokens)| MarkingEvidence {
                        place: format!("place#{place}"),
                        tokens: *tokens,
                        span: None,
                    })
                    .collect::<Vec<_>>();

                Incident {
                    id: format!("datarace-{}", index + 1),
                    kind: "datarace".to_string(),
                    state_id: None,
                    what_happened: format!(
                        "Two unsafe accesses to {} are simultaneously enabled without synchronization.",
                        race.variable_info
                    ),
                    where_to_look,
                    developer_explanation: String::new(),
                    diagnosis: IncidentDiagnosis {
                        blocked_resources: Vec::new(),
                        conflicting_operations,
                        why_bug: "A read/write or write/write pair is simultaneously enabled for the same alias location.".to_string(),
                        blocked_operations: Vec::new(),
                    },
                    evidence: IncidentEvidence {
                        state: race.state.clone(),
                        incoming_trace: Vec::new(),
                        marking,
                        token_changes: Vec::new(),
                        artifacts: artifacts.clone(),
                    },
                    suggested_next_steps: vec![
                        "Check whether the reported accesses should be protected by the same lock or atomic protocol.".to_string(),
                        "Use the basic-block numbers to inspect the MIR-to-Petri-net transition around each access.".to_string(),
                        "Inspect stategraph.dot to confirm both access transitions are enabled from the same state.".to_string(),
                    ],
                }
            })
            .collect::<Vec<_>>();

        IncidentReport {
            schema_version: INCIDENT_SCHEMA_VERSION.to_string(),
            tool: "RustPTA".to_string(),
            mode: "datarace".to_string(),
            result: bug_result(self.has_race),
            severity: if self.has_race { "high" } else { "none" }.to_string(),
            confidence: default_confidence(self.has_race),
            summary: IncidentSummary {
                bug_count: self.race_count,
                state_space: None,
                primary_locations: primary_locations(&incidents),
                explanation: if self.has_race {
                    "At least one reachable state enables conflicting unsafe memory operations; read/read pairs are omitted."
                        .to_string()
                } else {
                    "No simultaneously enabled conflicting unsafe memory operations were found."
                        .to_string()
                },
            },
            incidents,
            analysis_time: format_duration(self.analysis_time),
            artifacts,
            error: self.error.clone(),
        }
    }

    pub fn save_to_file(&self, path: &str) -> std::io::Result<()> {
        use std::fs::File;
        use std::io::Write;

        let mut file = File::create(path)?;
        writeln!(file, "{}", self)?;
        remove_legacy_json_sidecar(path)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    fn sample_deadlock_report() -> DeadlockReport {
        DeadlockReport {
            tool_name: "Petri Net Deadlock Detector".to_string(),
            has_deadlock: true,
            deadlock_count: 1,
            deadlock_states: vec![DeadlockState {
                state_id: "s37".to_string(),
                marking: vec![
                    (
                        "thread_a_after_lock_mutex_0 (src/main.rs:40:5)".to_string(),
                        1,
                    ),
                    ("Mutex_0 ()".to_string(), 0),
                ],
                description: "Deadlock state with blocked resources".to_string(),
                blocked_transitions: Vec::new(),
            }],
            traces: vec![DeadlockTrace {
                steps: vec!["s31 --t92--> s37".to_string()],
                final_state: None,
            }],
            analysis_time: Duration::from_millis(125),
            state_space_info: Some(StateSpaceInfo {
                total_states: 128,
                total_transitions: 231,
                reachable_states: 128,
            }),
            error: None,
        }
    }

    #[test]
    fn deadlock_display_uses_incident_template() {
        let text = sample_deadlock_report().to_string();

        assert!(text.contains("RustPTA Bug Report"));
        assert!(text.contains("Result        : BUG FOUND"));
        assert!(text.contains("Mode          : deadlock"));
        assert!(text.contains("Incident deadlock-1"));
        assert!(text.contains("What happened:"));
        assert!(!text.contains("Where to look first:"));
        assert!(text.contains("Developer explanation:"));
        let explanation = text.find("Developer explanation:").unwrap();
        let first_incident = text.find("Incident deadlock-1").unwrap();
        assert!(explanation < first_incident);
        assert!(text.contains("Deadlock state:"));
        assert!(text.contains("  state id : s37"));
        assert!(text.contains("  reason   : Deadlock state with blocked resources"));
        assert!(text.contains("  active control places:"));
        assert!(text.contains("  resource tokens:"));
        assert!(!text.contains("State evidence:"));
        assert!(!text.contains("Relevant marking:"));
        assert!(!text.contains("Path reconstruction not implemented yet"));
        assert!(text.contains("Suggested next steps:"));
        assert!(text.contains("stategraph.dot"));
        assert!(text.contains("petrinet.dot"));
    }

    #[test]
    fn deadlock_incident_json_has_schema_and_evidence() {
        let json = serde_json::to_value(sample_deadlock_report().to_incident_report()).unwrap();

        assert_eq!(json["schema_version"], "2");
        assert_eq!(json["tool"], "RustPTA");
        assert_eq!(json["mode"], "deadlock");
        assert_eq!(json["result"], "bug_found");
        assert_eq!(json["summary"]["bug_count"], 1);
        assert_eq!(json["incidents"][0]["id"], "deadlock-1");
        assert_eq!(json["incidents"][0]["state_id"], "s37");
        assert!(
            json["incidents"][0]["evidence"]["marking"]
                .as_array()
                .unwrap()
                .len()
                >= 1
        );
    }

    #[test]
    fn deadlock_save_to_file_writes_only_txt_report() {
        let path = std::env::temp_dir().join(format!(
            "rustpta_deadlock_report_{}.txt",
            std::process::id()
        ));
        let json_path = format!("{}.json", path.to_string_lossy());
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_file(&json_path);
        std::fs::write(&json_path, "stale json").unwrap();

        sample_deadlock_report()
            .save_to_file(path.to_str().unwrap())
            .unwrap();

        let text = std::fs::read_to_string(&path).unwrap();
        assert!(text.contains("RustPTA Bug Report"));
        assert!(!std::path::Path::new(&json_path).exists());

        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn deadlock_display_shows_blocked_resource_operations() {
        let mut report = sample_deadlock_report();
        report.deadlock_states[0].blocked_transitions = vec![BlockedTransition {
            id: "t5".to_string(),
            name: "main_0_lock".to_string(),
            location: "src/main.rs:10:5".to_string(),
            operation: "Lock acquisition".to_string(),
            needed_resources: vec!["Mutex_0".to_string()],
            resource_status: vec![ResourceStatus {
                resource_name: "Mutex_0".to_string(),
                has: 0,
                needs: 1,
            }],
            resource_trace: vec![ResourceTraceStep {
                resource_name: "Mutex_0".to_string(),
                transition_name: "thread_a_lock".to_string(),
                operation: "Lock acquisition".to_string(),
                location: "src/main.rs:8:5".to_string(),
                from_state: "s0".to_string(),
                to_state: "s1".to_string(),
                before: 1,
                after: 0,
            }],
        }];

        let text = report.to_string();
        assert!(text.contains("main_0_lock"));
        assert!(text.contains("src/main.rs:10:5"));
        assert!(text.contains("Lock acquisition"));
        assert!(text.contains("Mutex_0"));
        assert!(text.contains("last resource use"));
        assert!(text.contains("s0 -> s1: thread_a_lock [Lock acquisition] at src/main.rs:8:5"));
        assert!(text.contains("Mutex_0: 1 -> 0"));
    }

    #[test]
    fn deadlock_display_formats_marking_spans_with_nested_parentheses() {
        let mut report = sample_deadlock_report();
        report.deadlock_states[0].marking = vec![
            (
                "main_3_wait (src/main.rs:163:5: 163:29 (#0))".to_string(),
                1,
            ),
            ("Mutex_0 ()".to_string(), 1),
        ];

        let text = report.to_string();

        assert!(text.contains("  - main_3_wait tokens=1 at src/main.rs:163:5: 163:29 (#0)"));
        assert!(text.contains("  - Mutex_0 tokens=1"));
        assert!(!text.contains("main_3_wait (src/main.rs"));
    }

    fn sample_race_report() -> RaceReport {
        RaceReport {
            tool_name: "State Graph Data Race Detector".to_string(),
            has_race: true,
            race_count: 1,
            race_conditions: vec![RaceCondition {
                operations: vec![
                    RaceOperation {
                        operation_type: "read".to_string(),
                        variable: "i32".to_string(),
                        location: "src/main.rs:10:5".to_string(),
                        basic_block: Some(0),
                    },
                    RaceOperation {
                        operation_type: "write".to_string(),
                        variable: "i32".to_string(),
                        location: "src/main.rs:20:5".to_string(),
                        basic_block: Some(1),
                    },
                ],
                variable_info: "Potential data race on variable 0".to_string(),
                state: vec![(1, 1)],
            }],
            analysis_time: Duration::from_millis(10),
            error: None,
        }
    }

    #[test]
    fn race_display_names_conflicting_operations() {
        let text = sample_race_report().to_string();

        assert!(text.contains("Mode          : datarace"));
        assert!(text.contains("Incident datarace-1"));
        assert!(text.contains("Key unsafe accesses:"));
        assert!(text.contains("1. src/main.rs:10:5"));
        assert!(text.contains("read i32 (bb0)"));
        assert!(text.contains("2. src/main.rs:20:5"));
        assert!(text.contains("write i32 (bb1)"));
        assert!(!text.contains("Where to look:"));
    }

    #[test]
    fn race_display_focuses_on_enabled_unsafe_accesses() {
        let text = sample_race_report().to_string();

        assert!(text.contains("Enabled state:"));
        assert!(text.contains("1 Petri-net places are marked in the witness state."));
        assert!(text.contains("read/read pairs are omitted"));
        assert!(!text.contains("Conflicting unsafe accesses:"));
        assert!(!text.contains("  - place#1 tokens=1"));
        assert!(!text.contains("Relevant marking:"));
    }

    #[test]
    fn race_display_omits_suggested_next_steps() {
        let text = sample_race_report().to_string();

        assert!(!text.contains("Suggested next steps:"));
        assert!(!text.contains("Check whether the reported accesses should be protected"));
    }

    fn sample_atomic_report() -> AtomicReport {
        AtomicReport {
            tool_name: "State Graph Atomicity Detector".to_string(),
            has_violation: true,
            violation_count: 1,
            violations: vec![ViolationPattern {
                load_op: AtomicOperation {
                    operation_type: "load".to_string(),
                    ordering: "Acquire".to_string(),
                    variable: "AtomicUsize".to_string(),
                    location: "src/main.rs:10:5".to_string(),
                },
                store_ops: vec![
                    AtomicOperation {
                        operation_type: "store".to_string(),
                        ordering: "Release".to_string(),
                        variable: "AtomicUsize".to_string(),
                        location: "src/main.rs:20:5".to_string(),
                    },
                    AtomicOperation {
                        operation_type: "store".to_string(),
                        ordering: "Relaxed".to_string(),
                        variable: "AtomicUsize".to_string(),
                        location: "src/main.rs:30:5".to_string(),
                    },
                ],
            }],
            analysis_time: Duration::from_millis(10),
            error: None,
        }
    }

    #[test]
    fn atomic_display_labels_candidate_pattern_and_branch_limit() {
        let text = sample_atomic_report().to_string();

        assert!(text.contains("Mode          : atomic"));
        assert!(text.contains("Incident atomicity-1"));
        assert!(text.contains("Candidate atomic pattern:"));
        assert!(text.contains("  load:"));
        assert!(text.contains("    - load AtomicUsize at src/main.rs:10:5 (Acquire)"));
        assert!(text.contains("  competing stores:"));
        assert!(text.contains("    - store AtomicUsize at src/main.rs:20:5 (Release)"));
        assert!(text.contains("    - store AtomicUsize at src/main.rs:30:5 (Relaxed)"));
        assert!(text.contains("state-graph reachability can include operations from alternative branches"));
        assert!(!text.contains("Relevant marking:"));
    }
}
