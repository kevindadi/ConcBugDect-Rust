//! Exports the `concir-impl-net/1` JSON artifact for ConcIR stuttering refinement
//! and static hole-purity verification (`--export-concir-net <FILE>` + optional
//! `--codegen-map <FILE>`).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use unipn::analysis::pt::reachability::StateGraph;
use unipn::net::{ArcDir, Marking, PlaceClass, PlaceId, TransitionId};
use unipn::pt::{PtNet, ResourceKind, TransitionType};

use crate::report::events;
use crate::translate::construct::PetriNet;
use crate::translate::lower::facts::TranslationProvenance;
use crate::translate::net::subnets::SubNetContext;

/// Schema identifier for the ConcIR implementation sync Petri-net export.
pub const SCHEMA: &str = "concir-impl-net/1";

/// One resource mapping entry from ConcIR `codegen.json`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
pub struct CodegenResource {
    pub fqn: String,
    #[serde(default)]
    pub field: String,
    #[serde(default)]
    pub kind: String,
}

/// One hole entry from ConcIR `codegen.json`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
pub struct CodegenHole {
    pub id: String,
    #[serde(default)]
    pub module: Option<String>,
    #[serde(default)]
    pub function: String,
    #[serde(default)]
    pub sid: String,
    #[serde(default)]
    pub expected: String,
    #[serde(default)]
    pub file: Option<String>,
    #[serde(default)]
    pub line: Option<usize>,
    #[serde(default)]
    pub start_line: Option<usize>,
    #[serde(default)]
    pub end_line: Option<usize>,
    #[serde(default)]
    pub reads: Vec<String>,
    #[serde(default)]
    pub writes: Vec<String>,
    #[serde(default)]
    pub req: Vec<String>,
}

/// Inclusive 1-based line range for a filled hole in a source file.
#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
pub struct HoleRange {
    #[serde(default)]
    pub file: String,
    pub start_line: usize,
    pub end_line: usize,
}

/// Subset of ConcIR `codegen.json` (plus optional `hole_ranges` produced after
/// filling holes) consumed by `--codegen-map`.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct CodegenMap {
    #[serde(default)]
    pub program: String,
    #[serde(default)]
    pub resources: Vec<CodegenResource>,
    #[serde(default)]
    pub holes: Vec<CodegenHole>,
    #[serde(default)]
    pub hole_ranges: BTreeMap<String, HoleRange>,
}

impl CodegenMap {
    pub fn load_from_file(path: &Path) -> std::io::Result<Self> {
        let text = fs::read_to_string(path)?;
        serde_json::from_str(&text)
            .map_err(|err| std::io::Error::new(std::io::ErrorKind::InvalidData, err))
    }

    /// All effective hole ranges: explicit `hole_ranges` entries take priority,
    /// falling back to `start_line..=end_line` or single `line` from `holes`.
    pub fn effective_hole_ranges(&self) -> Vec<(String, HoleRange)> {
        let mut ranges: BTreeMap<String, HoleRange> = self.hole_ranges.clone();
        for hole in &self.holes {
            if ranges.contains_key(&hole.id) {
                continue;
            }
            let file = hole
                .file
                .clone()
                .filter(|f| !f.is_empty())
                .unwrap_or_else(|| "src/main.rs".to_string());
            if let (Some(start), Some(end)) = (hole.start_line, hole.end_line)
                && start > 0
                && end >= start
            {
                ranges.insert(
                    hole.id.clone(),
                    HoleRange {
                        file,
                        start_line: start,
                        end_line: end,
                    },
                );
            } else if let Some(line) = hole.line
                && line > 0
            {
                ranges.insert(
                    hole.id.clone(),
                    HoleRange {
                        file,
                        start_line: line,
                        end_line: line,
                    },
                );
            }
        }
        ranges.into_iter().collect()
    }

    /// Find the hole whose inclusive line range contains `span`, if any.
    pub fn hole_for_span(&self, span: &str) -> Option<String> {
        let (span_file, span_line) = parse_span_file_line(span)?;
        for (hole_id, range) in self.effective_hole_ranges() {
            if span_line >= range.start_line
                && span_line <= range.end_line
                && files_match(&span_file, &range.file)
            {
                return Some(hole_id);
            }
        }
        None
    }

    /// Map a raw resource name (or MIR field hint / resource kind) to a
    /// canonical ConcIR resource FQN when present in `resources`.
    pub fn resolve_resource(
        &self,
        raw: &str,
        field_hint: Option<&str>,
        kind: Option<ResourceKind>,
    ) -> Option<String> {
        if let Some(found) = self.match_resource_candidate(raw) {
            return Some(found);
        }
        if let Some(hint) = field_hint
            && let Some(found) = self.match_resource_candidate(hint)
        {
            return Some(found);
        }
        // Fallback for synthetic SPN place names (`Mutex_0`, `Condvar:...`,
        // `Atomic(...)`) when the program has a unique resource of that kind.
        if let Some(rk) = kind
            && is_synthetic_spn_resource_name(raw)
        {
            let matches: Vec<&CodegenResource> = self
                .resources
                .iter()
                .filter(|r| resource_kind_matches(rk, &r.kind))
                .collect();
            if matches.len() == 1 {
                return Some(matches[0].fqn.clone());
            }
        }
        None
    }

    fn match_resource_candidate(&self, candidate: &str) -> Option<String> {
        let trimmed = candidate.trim();
        if trimmed.is_empty() {
            return None;
        }
        let stripped = trimmed
            .strip_prefix("shared.")
            .or_else(|| trimmed.strip_prefix("self."))
            .unwrap_or(trimmed);

        // 1. Exact FQN match.
        if let Some(r) = self
            .resources
            .iter()
            .find(|r| r.fqn == trimmed || r.fqn == stripped)
        {
            return Some(r.fqn.clone());
        }
        // 2. Exact struct field name match.
        if let Some(r) = self
            .resources
            .iter()
            .find(|r| !r.field.is_empty() && (r.field == trimmed || r.field == stripped))
        {
            return Some(r.fqn.clone());
        }
        // 3. Token-bounded substring match on struct field name (e.g. `shared.r0_main_m`
        //    or `field(r0_main_m)` without falsely matching `r0_m` inside `r0_m1`).
        if let Some(r) = self
            .resources
            .iter()
            .find(|r| !r.field.is_empty() && contains_ident_token(stripped, &r.field))
        {
            return Some(r.fqn.clone());
        }
        // 4. Unambiguous short-name suffix match (`m` -> `main::m`).
        let short_matches: Vec<&CodegenResource> = self
            .resources
            .iter()
            .filter(|r| r.fqn.rsplit("::").next() == Some(stripped))
            .collect();
        if short_matches.len() == 1 {
            return Some(short_matches[0].fqn.clone());
        }
        None
    }
}

/// Inputs to [`build_concir_net`] and [`write_concir_net`].
pub struct ConcirNetInputs<'a> {
    pub crate_name: &'a str,
    pub entry_mode: &'a str,
    pub net: &'a PtNet,
    pub initial_marking: &'a Marking,
    pub state_graph: &'a StateGraph,
    pub provenance: &'a TranslationProvenance,
    pub subnets: &'a [SubNetContext],
    pub codegen_map: Option<&'a CodegenMap>,
    /// Optional `PlaceId.index() -> struct field name` hints extracted from MIR.
    pub place_field_hints: &'a BTreeMap<usize, String>,
}

/// Structured hole-purity violation recorded in `concir-impl-net/1`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PurityViolation {
    pub hole_id: String,
    pub fn_def_path: String,
    pub kind: String,
    pub op: String,
    pub span: String,
    pub message: String,
}

/// Build the `concir-impl-net/1` JSON object.
pub fn build_concir_net(inputs: &ConcirNetInputs<'_>) -> Value {
    let net = inputs.net;
    let sg = inputs.state_graph;
    let prov = inputs.provenance;
    let codegen_map = inputs.codegen_map;

    // Precompute canonical resource names for every place and identify lock places
    // (for `held_locks` per reachable state).
    let lock_places = collect_lock_places(net, inputs.initial_marking);
    let place_canonical: Vec<String> = (0..net.num_places())
        .map(|idx| {
            let pid = PlaceId::from(idx);
            let raw_name = net.place(pid).map(|p| p.name.as_str()).unwrap_or("");
            let rk = net.resource_kind(pid);
            let hint = inputs.place_field_hints.get(&idx).map(String::as_str);
            codegen_map
                .and_then(|map| map.resolve_resource(raw_name, hint, rk))
                .unwrap_or_else(|| raw_name.to_string())
        })
        .collect();

    // 1. Places.
    let places: Vec<Value> = (0..net.num_places())
        .map(|idx| {
            let pid = PlaceId::from(idx);
            let place = net.place(pid).expect("place index in range");
            let resource_kind = resource_kind_str(net, pid);
            json!({
                "id": idx,
                "name": place.name,
                "class": format!("{:?}", place.kind.place_type),
                "resource_kind": resource_kind,
                "initial_tokens": inputs.initial_marking.tokens(pid),
                "span": place.kind.span,
            })
        })
        .collect();

    // 2. Transitions + sync-in-hole purity violations.
    let mut purity_violations: Vec<PurityViolation> = Vec::new();
    let transitions: Vec<Value> = (0..net.num_transitions())
        .map(|idx| {
            let tid = TransitionId::from(idx);
            let trans = net.transition(tid).expect("transition index in range");
            let origin = prov.origin(tid);
            let (fn_def_path, bb, span) = match origin {
                Some(o) => (o.fn_def_path.clone(), Some(o.bb), o.span.clone()),
                None => (String::new(), None, String::new()),
            };

            let (observable, op, custom_hint) = classify_transition(net, tid, prov);
            let resource = if observable {
                resolve_transition_resource(
                    net,
                    tid,
                    custom_hint.as_deref(),
                    codegen_map,
                    inputs.place_field_hints,
                )
            } else {
                String::new()
            };

            let hole_id = codegen_map.and_then(|map| map.hole_for_span(&span));
            if observable && let Some(ref hid) = hole_id {
                purity_violations.push(PurityViolation {
                    hole_id: hid.clone(),
                    fn_def_path: fn_def_path.clone(),
                    kind: "sync_in_hole".to_string(),
                    op: op.to_string(),
                    span: span.clone(),
                    message: format!(
                        "observable sync operation `{op}` ({resource}) originates inside hole `{hid}` at {span}"
                    ),
                });
            }

            let inputs_arcs: Vec<Value> = net
                .arcs_of(tid, ArcDir::Input)
                .map(|arc| json!({ "place": arc.place.index(), "weight": arc.weight }))
                .collect();
            let outputs_arcs: Vec<Value> = net
                .arcs_of(tid, ArcDir::Output)
                .map(|arc| json!({ "place": arc.place.index(), "weight": arc.weight }))
                .collect();

            json!({
                "id": idx,
                "name": trans.name,
                "observable": observable,
                "op": op,
                "resource": resource,
                "fn_def_path": fn_def_path,
                "bb": bb,
                "span": span,
                "hole_id": hole_id,
                "inputs": inputs_arcs,
                "outputs": outputs_arcs,
            })
        })
        .collect();

    // 3. Cut loop back-edges inside hole ranges -> purity violations.
    if let Some(map) = codegen_map {
        collect_loop_purity_violations(prov, map, &mut purity_violations);
    }
    purity_violations.sort_by(|a, b| {
        a.hole_id
            .cmp(&b.hole_id)
            .then_with(|| a.kind.cmp(&b.kind))
            .then_with(|| a.fn_def_path.cmp(&b.fn_def_path))
            .then_with(|| a.span.cmp(&b.span))
            .then_with(|| a.op.cmp(&b.op))
    });

    // 4. States & edges from state_graph.
    let deadlock_set: BTreeSet<usize> = sg.deadlock_states(net).into_iter().collect();
    let mut has_outgoing = vec![false; sg.states.len()];
    for (from, _, _) in &sg.edges {
        if let Some(slot) = has_outgoing.get_mut(*from) {
            *slot = true;
        }
    }

    let states: Vec<Value> = sg
        .states
        .iter()
        .enumerate()
        .map(|(state_id, state)| {
            let deadlock = deadlock_set.contains(&state_id);
            let terminal = !has_outgoing[state_id] && !deadlock;
            let mut held: BTreeSet<String> = BTreeSet::new();
            for &lock_pid in &lock_places {
                let init_tokens = inputs.initial_marking.tokens(lock_pid);
                if state.marking.tokens(lock_pid) < init_tokens {
                    let label = place_canonical
                        .get(lock_pid.index())
                        .cloned()
                        .unwrap_or_default();
                    if !label.is_empty() {
                        held.insert(label);
                    }
                }
            }
            json!({
                "id": state_id,
                "initial": state_id == sg.initial,
                "terminal": terminal,
                "deadlock": deadlock,
                "held_locks": held.into_iter().collect::<Vec<_>>(),
            })
        })
        .collect();

    let edges: Vec<Value> = sg
        .edges
        .iter()
        .map(|(from, to, edge)| {
            json!({
                "from": from,
                "to": to,
                "transition": edge.transition.id.index(),
            })
        })
        .collect();

    // 5. Completed functions: any subnet whose `end` place has > 0 tokens in at
    //    least one reachable state.
    let mut completed: BTreeSet<String> = BTreeSet::new();
    for subnet in inputs.subnets {
        let reached_end = sg
            .states
            .iter()
            .any(|state| state.marking.tokens(subnet.end) > 0);
        if reached_end {
            completed.insert(subnet.fn_def_path.clone());
        }
    }
    let completed_functions: Vec<String> = completed.into_iter().collect();

    json!({
        "schema": SCHEMA,
        "crate": inputs.crate_name,
        "entry_mode": inputs.entry_mode,
        "truncated": sg.truncated,
        "places": places,
        "transitions": transitions,
        "states": states,
        "edges": edges,
        "purity_violations": purity_violations,
        "completed_functions": completed_functions,
    })
}

/// Write `concir-impl-net/1` JSON to `path`, creating parent directories as needed.
pub fn write_concir_net(inputs: &ConcirNetInputs<'_>, path: &Path) -> std::io::Result<()> {
    let report = build_concir_net(inputs);
    let mut text = serde_json::to_string_pretty(&report).map_err(std::io::Error::other)?;
    text.push('\n');
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, text)
}

/// Collect `PlaceId.index() -> struct field name` hints from MIR for resources
/// discovered during `analyze_resources` (mutexes, rwlocks, condvars, atomics).
pub fn collect_place_field_hints(petri: &PetriNet<'_, '_>) -> BTreeMap<usize, String> {
    use crate::analysis::sync::{SiteKind, SiteOrigin};

    let mut hints = BTreeMap::new();
    let tcx = petri.tcx;

    for site in &petri.plan.sites {
        let place = match site.origin {
            SiteOrigin::Guard(id) => petri.resources.locks().get(&id.get_alias_id()).copied(),
            SiteOrigin::Custom { .. } => petri
                .resources
                .custom_locks()
                .get(&site.instance)
                .map(|entry| entry.place),
            SiteOrigin::Condvar(id) => petri
                .resources
                .condvars()
                .get(&id.get_alias_id())
                .copied(),
            SiteOrigin::Alias(alias) if site.kind == SiteKind::Atomic => petri
                .resources
                .atomic_places()
                .get(&alias)
                .and_then(|places| places.first().copied()),
            _ => None,
        };
        let Some(place) = place else {
            continue;
        };
        if hints.contains_key(&place.index()) {
            continue;
        }
        // Try the underlying sync-object local first, then the site local itself.
        let candidates = [
            (site.object.instance_id, site.object.local),
            (site.instance, site.local),
        ];
        for (inst_id, local) in candidates {
            let Some(node) = petri.callgraph.index_to_instance(inst_id) else {
                continue;
            };
            let inst = node.instance();
            if !tcx.is_mir_available(inst.def_id()) {
                continue;
            }
            let body = tcx.instance_mir(inst.def);
            if let Some(field_name) = trace_local_adt_field_name(body, local) {
                hints.insert(place.index(), field_name);
                break;
            }
        }
    }

    hints
}

fn trace_local_adt_field_name<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    start: rustc_middle::mir::Local,
) -> Option<String> {
    use crate::translate::lower::BodyToPetriNet;
    use rustc_middle::mir::{Operand, Rvalue, StatementKind, TerminatorKind};

    let mut current = start;
    let mut seen = rustc_data_structures::fx::FxHashSet::default();
    while seen.insert(current) {
        let mut next_local = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(boxed) = &stmt.kind else {
                    continue;
                };
                let (dst, rvalue) = &**boxed;
                if !dst.projection.is_empty() || dst.local != current {
                    continue;
                }
                let src_place = match rvalue {
                    Rvalue::Ref(_, _, p)
                    | Rvalue::RawPtr(_, p)
                    | Rvalue::CopyForDeref(p)
                    | Rvalue::Reborrow(_, _, p) => Some(p),
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p), _) => Some(p),
                    _ => None,
                };
                if let Some(p) = src_place {
                    if let Some(name) = BodyToPetriNet::place_adt_field_name(body, p) {
                        return Some(name);
                    }
                    next_local = Some(p.local);
                }
            }
            if let Some(term) = &bb.terminator
                && let TerminatorKind::Call {
                    args, destination, ..
                } = &term.kind
                && destination.projection.is_empty()
                && destination.local == current
                && let Some(p) = args.first().and_then(|a| a.node.place())
            {
                if let Some(name) = BodyToPetriNet::place_adt_field_name(body, &p) {
                    return Some(name);
                }
                next_local = Some(p.local);
            }
        }
        current = next_local?;
    }
    None
}

/// Classify a transition into `(observable, canonical_op, optional_custom_resource_hint)`.
pub fn classify_transition(
    net: &PtNet,
    tid: TransitionId,
    provenance: &TranslationProvenance,
) -> (bool, &'static str, Option<String>) {
    let Some(trans) = net.transition(tid) else {
        return (false, "tau", None);
    };
    match &trans.kind.transition_type {
        TransitionType::Lock(_) => (true, "mutex_lock", None),
        TransitionType::Unlock(place_idx) => {
            if net.resource_kind(PlaceId::from(*place_idx)) == Some(ResourceKind::RwLock) {
                (true, "rwlock_unlock", None)
            } else {
                (true, "mutex_unlock", None)
            }
        }
        TransitionType::RwLockRead(_) => (true, "rwlock_read", None),
        TransitionType::RwLockWrite(_) => (true, "rwlock_write", None),
        TransitionType::DropRead(_) | TransitionType::DropWrite(_) => (true, "rwlock_unlock", None),
        TransitionType::Wait => (true, "condvar_wait", None),
        TransitionType::Notify(_) => {
            if is_notify_all(trans.name.as_str(), tid, provenance) {
                (true, "condvar_notify_all", None)
            } else {
                (true, "condvar_notify", None)
            }
        }
        TransitionType::AtomicLoad(..) => (true, "atomic_load", None),
        TransitionType::AtomicStore(..) => (true, "atomic_store", None),
        TransitionType::AtomicCmpXchg(..) => (true, "atomic_cas", None),
        TransitionType::Spawn(_) => (true, "spawn", None),
        TransitionType::Join(_) => (true, "join", None),
        _ => classify_custom_concir_sync(&trans.name),
    }
}

fn is_notify_all(
    trans_name: &str,
    tid: TransitionId,
    provenance: &TranslationProvenance,
) -> bool {
    if trans_name.contains("notify_all") {
        return true;
    }
    if let Some(origin) = provenance.origin(tid) {
        if origin.fn_def_path.contains("notify_all") {
            return true;
        }
        if let Some(facts) = provenance.function(&origin.fn_def_path)
            && let Some(bb_facts) = facts.bb(origin.bb)
            && bb_facts
                .defs
                .iter()
                .any(|def| def.rhs.contains("notify_all"))
        {
            return true;
        }
    }
    false
}

/// Recognize ConcIR `cir_trace::Semaphore` / `cir_trace::Channel` summary transitions.
fn classify_custom_concir_sync(name: &str) -> (bool, &'static str, Option<String>) {
    if let Some(rest) = name.strip_prefix("cir_sync::") {
        let mut parts = rest.splitn(3, "::");
        let op_tag = parts.next().unwrap_or("");
        let second = parts.next();
        let third = parts.next();
        let canonical = match op_tag {
            "sem_acquire" => Some("sem_acquire"),
            "sem_release" => Some("sem_release"),
            "channel_send" => Some("channel_send"),
            "channel_recv" => Some("channel_recv"),
            _ => None,
        };
        if let Some(op) = canonical {
            // Format is `cir_sync::<op>::<field>::<callee>_summary_t0` when field hint
            // is present, else `cir_sync::<op>::<callee>_summary_t0`.
            let hint = match (second, third) {
                (Some(field), Some(_)) if !field.is_empty() => Some(field.to_string()),
                _ => None,
            };
            return (true, op, hint);
        }
    }
    if name.contains("Semaphore::acquire") || name.contains("::acquire_sid") {
        return (true, "sem_acquire", None);
    }
    if name.contains("Semaphore::release") || name.contains("::release_sid") {
        return (true, "sem_release", None);
    }
    if name.contains("Channel::send") || name.contains("::send_sid") {
        return (true, "channel_send", None);
    }
    if name.contains("Channel::recv") || name.contains("::recv_sid") {
        return (true, "channel_recv", None);
    }
    (false, "tau", None)
}

fn resolve_transition_resource(
    net: &PtNet,
    tid: TransitionId,
    custom_hint: Option<&str>,
    codegen_map: Option<&CodegenMap>,
    place_field_hints: &BTreeMap<usize, String>,
) -> String {
    if let Some(hint) = custom_hint {
        if let Some(map) = codegen_map
            && let Some(resolved) = map.resolve_resource(hint, Some(hint), None)
        {
            return resolved;
        }
        return hint.to_string();
    }

    let touched_place = transition_resource_place(net, tid);
    let place_name = touched_place
        .and_then(|pid| net.place(pid))
        .map(|p| p.name.as_str());
    let place_kind = touched_place.and_then(|pid| net.resource_kind(pid));
    let field_hint = touched_place
        .and_then(|pid| place_field_hints.get(&pid.index()))
        .map(String::as_str);

    let fallback = events::resource_name(net, tid);
    let primary_raw = match net.transition(tid).map(|t| &t.kind.transition_type) {
        Some(TransitionType::Wait) => place_name.unwrap_or(fallback.as_str()),
        Some(
            TransitionType::AtomicLoad(..)
            | TransitionType::AtomicStore(..)
            | TransitionType::AtomicCmpXchg(..),
        ) => place_name.unwrap_or(fallback.as_str()),
        _ => {
            if !fallback.is_empty() {
                fallback.as_str()
            } else {
                place_name.unwrap_or("")
            }
        }
    };

    if let Some(map) = codegen_map {
        if let Some(resolved) = map.resolve_resource(primary_raw, field_hint, place_kind) {
            return resolved;
        }
        if let Some(pname) = place_name
            && pname != primary_raw
            && let Some(resolved) = map.resolve_resource(pname, field_hint, place_kind)
        {
            return resolved;
        }
    }

    if !fallback.is_empty() {
        fallback
    } else {
        place_name.unwrap_or("").to_string()
    }
}

fn transition_resource_place(net: &PtNet, tid: TransitionId) -> Option<PlaceId> {
    let ty = &net.transition(tid)?.kind.transition_type;
    match ty {
        TransitionType::Lock(p)
        | TransitionType::Unlock(p)
        | TransitionType::RwLockRead(p)
        | TransitionType::RwLockWrite(p)
        | TransitionType::DropRead(p)
        | TransitionType::DropWrite(p)
        | TransitionType::Notify(p) => Some(PlaceId::from(*p)),
        TransitionType::Wait => {
            // Prefer the Condvar input arc over any re-acquired Mutex input arc.
            net.arcs_of(tid, ArcDir::Input)
                .find(|arc| net.resource_kind(arc.place) == Some(ResourceKind::Condvar))
                .or_else(|| {
                    net.arcs_of(tid, ArcDir::Input)
                        .find(|arc| net.is_resource(arc.place))
                })
                .map(|arc| arc.place)
        }
        TransitionType::AtomicLoad(..)
        | TransitionType::AtomicStore(..)
        | TransitionType::AtomicCmpXchg(..) => net
            .arcs_of(tid, ArcDir::Input)
            .find(|arc| net.resource_kind(arc.place) == Some(ResourceKind::Atomic))
            .or_else(|| {
                net.arcs_of(tid, ArcDir::Input)
                    .find(|arc| net.is_resource(arc.place))
            })
            .map(|arc| arc.place),
        _ => None,
    }
}

fn collect_lock_places(net: &PtNet, initial_marking: &Marking) -> Vec<PlaceId> {
    let mut lock_ids: BTreeSet<usize> = BTreeSet::new();
    for idx in 0..net.num_places() {
        let pid = PlaceId::from(idx);
        if matches!(
            net.resource_kind(pid),
            Some(ResourceKind::Mutex | ResourceKind::RwLock)
        ) && initial_marking.tokens(pid) > 0
        {
            lock_ids.insert(idx);
        }
    }
    // Also recognize generic `PtPlaceKind::resource()` places targeted by lock transitions.
    for idx in 0..net.num_transitions() {
        let tid = TransitionId::from(idx);
        let Some(trans) = net.transition(tid) else {
            continue;
        };
        let target = match trans.kind.transition_type {
            TransitionType::Lock(p)
            | TransitionType::Unlock(p)
            | TransitionType::RwLockRead(p)
            | TransitionType::RwLockWrite(p)
            | TransitionType::DropRead(p)
            | TransitionType::DropWrite(p) => Some(PlaceId::from(p)),
            _ => None,
        };
        if let Some(pid) = target
            && net.is_resource(pid)
            && initial_marking.tokens(pid) > 0
        {
            lock_ids.insert(pid.index());
        }
    }
    lock_ids.into_iter().map(PlaceId::from).collect()
}

fn resource_kind_str(net: &PtNet, pid: PlaceId) -> Option<&'static str> {
    let place = net.place(pid)?;
    if !matches!(place.kind.place_type, PlaceClass::Resource(_)) {
        return None;
    }
    Some(match net.resource_kind(pid) {
        Some(ResourceKind::Mutex) => "mutex",
        Some(ResourceKind::RwLock) => "rwlock",
        Some(ResourceKind::Condvar) => "condvar",
        Some(ResourceKind::Atomic) => "atomic",
        Some(ResourceKind::Thread) => "thread",
        _ => "resource",
    })
}

fn collect_loop_purity_violations(
    provenance: &TranslationProvenance,
    codegen_map: &CodegenMap,
    out: &mut Vec<PurityViolation>,
) {
    let mut seen_edges: BTreeSet<(String, usize, usize)> = BTreeSet::new();

    for (fn_def_path, facts) in &provenance.functions {
        for &(from_bb, to_bb) in &facts.cut_back_edges {
            if !seen_edges.insert((fn_def_path.clone(), from_bb, to_bb)) {
                continue;
            }
            let span = cut_back_edge_span(provenance, fn_def_path, facts, from_bb, to_bb);
            if let Some(span) = span
                && let Some(hole_id) = codegen_map.hole_for_span(&span)
            {
                out.push(PurityViolation {
                    hole_id: hole_id.clone(),
                    fn_def_path: fn_def_path.clone(),
                    kind: "loop_in_hole".to_string(),
                    op: "loop_back_edge".to_string(),
                    span: span.clone(),
                    message: format!(
                        "loop back-edge bb{from_bb}->bb{to_bb} originates inside hole `{hole_id}` at {span}"
                    ),
                });
            }
        }
        // Also cover any loop_summaries not duplicated in `cut_back_edges`.
        for summary in &facts.loop_summaries {
            if !seen_edges.insert((fn_def_path.clone(), summary.from_bb, summary.to_bb)) {
                continue;
            }
            let span = provenance
                .origin(TransitionId::from(summary.transition))
                .map(|o| o.span.clone())
                .filter(|s| !s.is_empty())
                .or_else(|| {
                    cut_back_edge_span(
                        provenance,
                        fn_def_path,
                        facts,
                        summary.from_bb,
                        summary.to_bb,
                    )
                });
            if let Some(span) = span
                && let Some(hole_id) = codegen_map.hole_for_span(&span)
            {
                out.push(PurityViolation {
                    hole_id: hole_id.clone(),
                    fn_def_path: fn_def_path.clone(),
                    kind: "loop_in_hole".to_string(),
                    op: "loop_back_edge".to_string(),
                    span: span.clone(),
                    message: format!(
                        "loop back-edge bb{}->bb{} originates inside hole `{hole_id}` at {span}",
                        summary.from_bb, summary.to_bb
                    ),
                });
            }
        }
    }
}

fn cut_back_edge_span(
    provenance: &TranslationProvenance,
    fn_def_path: &str,
    facts: &crate::translate::lower::facts::FunctionFacts,
    from_bb: usize,
    to_bb: usize,
) -> Option<String> {
    if let Some(summary) = facts
        .loop_summaries
        .iter()
        .find(|s| s.from_bb == from_bb && s.to_bb == to_bb)
        && let Some(origin) = provenance.origin(TransitionId::from(summary.transition))
        && !origin.span.is_empty()
    {
        return Some(origin.span.clone());
    }
    if let Some(span) = provenance.bb_entry_span(fn_def_path, from_bb)
        && !span.is_empty()
    {
        return Some(span.to_string());
    }
    if let Some(bb_facts) = facts.bb(from_bb)
        && let Some(def) = bb_facts.defs.iter().rev().find(|d| !d.span.is_empty())
    {
        return Some(def.span.clone());
    }
    if let Some(span) = provenance.bb_entry_span(fn_def_path, to_bb)
        && !span.is_empty()
    {
        return Some(span.to_string());
    }
    None
}

/// Parse a rustc `Debug` span (e.g. `"src/main.rs:42:5: 42:30 (#0)"` or
/// `"C:\\proj\\src\\main.rs:42:5"`) into `(normalized_file, 1_based_line)`.
pub fn parse_span_file_line(span: &str) -> Option<(String, usize)> {
    let mut s = span.trim();
    if s.is_empty() {
        return None;
    }
    if let Some(pos) = s.rfind(" (#") {
        s = s[..pos].trim();
    }
    // Strip end location after `": "` (e.g. `"src/main.rs:42:5: 42:30"` -> `"src/main.rs:42:5"`).
    if let Some(pos) = s.find(": ") {
        s = &s[..pos];
    }
    // Split from the right to preserve Windows drive letters like `C:\...`.
    let (prefix, last) = s.rsplit_once(':')?;
    if let Ok(_col_or_line) = last.trim().parse::<usize>() {
        if let Some((file, line_str)) = prefix.rsplit_once(':')
            && let Ok(line) = line_str.trim().parse::<usize>()
        {
            return Some((normalize_file_path(file), line));
        }
        // Only `file:line` without column.
        let line = last.trim().parse::<usize>().ok()?;
        return Some((normalize_file_path(prefix), line));
    }
    None
}

fn normalize_file_path(path: &str) -> String {
    let mut normalized = path.trim().replace('\\', "/");
    while let Some(stripped) = normalized.strip_prefix("./") {
        normalized = stripped.to_string();
    }
    normalized
}

fn files_match(span_file: &str, range_file: &str) -> bool {
    let range_norm = normalize_file_path(range_file);
    if range_norm.is_empty() {
        return true;
    }
    let span_norm = normalize_file_path(span_file);
    if span_norm.eq_ignore_ascii_case(&range_norm) {
        return true;
    }
    let span_lower = span_norm.to_ascii_lowercase();
    let range_lower = range_norm.to_ascii_lowercase();
    span_lower.ends_with(&format!("/{range_lower}"))
        || range_lower.ends_with(&format!("/{span_lower}"))
}

fn is_synthetic_spn_resource_name(raw: &str) -> bool {
    raw.starts_with("Mutex_")
        || raw.starts_with("RwLock_")
        || raw.starts_with("Condvar:")
        || raw.starts_with("Atomic(")
        || raw.starts_with("atomic(")
}

fn resource_kind_matches(rk: ResourceKind, kind_str: &str) -> bool {
    let k = kind_str.to_ascii_lowercase();
    match rk {
        ResourceKind::Mutex => k == "mutex",
        ResourceKind::RwLock => k == "rwlock",
        ResourceKind::Condvar => k == "condvar",
        ResourceKind::Atomic => k == "atomic",
        ResourceKind::Thread => k == "thread",
        _ => false,
    }
}

fn contains_ident_token(haystack: &str, needle: &str) -> bool {
    if needle.is_empty() {
        return false;
    }
    let bytes = haystack.as_bytes();
    let mut start = 0;
    while let Some(pos) = haystack[start..].find(needle) {
        let abs_start = start + pos;
        let abs_end = abs_start + needle.len();
        let before_ok = abs_start == 0 || !is_ident_byte(bytes[abs_start - 1]);
        let after_ok = abs_end == bytes.len() || !is_ident_byte(bytes[abs_end]);
        if before_ok && after_ok {
            return true;
        }
        start = abs_start + 1;
    }
    false
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::translate::lower::facts::{BbFacts, DefRecord, FunctionFacts, TransOrigin};
    use unipn::analysis::pt::reachability::{StateGraph, StateGraphConfig};
    use unipn::net::ControlSub;
    use unipn::pt::{PtBuilder, PtPlaceKind, PtTransitionKind};

    fn control_place(sub: ControlSub) -> PtPlaceKind {
        PtPlaceKind::control(sub)
    }

    fn resource_place(kind: ResourceKind, capacity: Option<usize>) -> PtPlaceKind {
        PtPlaceKind {
            place_type: PlaceClass::Resource(kind),
            span: String::new(),
            capacity,
        }
    }

    fn build_sg(net: &PtNet, m0: &Marking) -> StateGraph {
        StateGraph::with_config(
            net,
            m0.clone(),
            StateGraphConfig {
                state_limit: Some(10_000),
                include_zero_tokens: false,
                use_por: false,
            },
        )
    }

    #[test]
    fn exports_concir_impl_net_with_resource_mapping_held_locks_and_completed_functions() {
        let mut b = PtBuilder::new();
        let m_place = b.add_marked_place(
            "shared.r0_main_m",
            resource_place(ResourceKind::Mutex, Some(1)),
            1,
        );
        let cv_place = b.add_marked_place(
            "Condvar:src/main.rs:12:5: 12:20 (#0)",
            resource_place(ResourceKind::Condvar, Some(1)),
            1,
        );
        let p_start = b.add_marked_place("main_start", control_place(ControlSub::FunctionStart), 1);
        let p_locked = b.add_place("main_bb1", control_place(ControlSub::BasicBlock));
        let p_notified = b.add_place("main_bb2", control_place(ControlSub::BasicBlock));
        let p_sem = b.add_place("main_bb3", control_place(ControlSub::BasicBlock));
        let p_end = b.add_place("main_end", control_place(ControlSub::FunctionEnd));
        let p_dead_start = b.add_place("unused_start", control_place(ControlSub::FunctionStart));
        let p_dead_end = b.add_place("unused_end", control_place(ControlSub::FunctionEnd));

        let t_lock = b.add_transition(
            "cf_main_bb0_call",
            PtTransitionKind::new(TransitionType::Lock(m_place.index())),
        );
        b.add_input_arc(p_start, t_lock, 1);
        b.add_input_arc(m_place, t_lock, 1);
        b.add_output_arc(p_locked, t_lock, 1);

        let t_notify = b.add_transition(
            "cf_main_bb1_notify_all",
            PtTransitionKind::new(TransitionType::Notify(cv_place.index())),
        );
        b.add_input_arc(p_locked, t_notify, 1);
        b.add_output_arc(p_notified, t_notify, 1);
        b.add_output_arc(cv_place, t_notify, 1);

        let t_sem = b.add_transition(
            "cir_sync::sem_acquire::r2_main_sem::cir_generated::cir_trace::Semaphore::acquire_sid_summary_t0",
            PtTransitionKind::new(TransitionType::Function),
        );
        b.add_input_arc(p_notified, t_sem, 1);
        b.add_output_arc(p_sem, t_sem, 1);

        let t_unlock = b.add_transition(
            "cf_main_bb3_drop",
            PtTransitionKind::new(TransitionType::Unlock(m_place.index())),
        );
        b.add_input_arc(p_sem, t_unlock, 1);
        b.add_output_arc(p_end, t_unlock, 1);
        b.add_output_arc(m_place, t_unlock, 1);

        let (net, m0) = b.build();
        let sg = build_sg(&net, &m0);

        let provenance = TranslationProvenance {
            origins: vec![
                TransOrigin {
                    fn_def_path: "cir_generated::main::cf_main".to_string(),
                    bb: 0,
                    span: "src/main.rs:20:5: 20:30 (#0)".to_string(),
                },
                TransOrigin {
                    fn_def_path: "cir_generated::main::cf_main".to_string(),
                    bb: 1,
                    span: "src/main.rs:22:5: 22:30 (#0)".to_string(),
                },
                TransOrigin {
                    fn_def_path: "cir_generated::main::cf_main".to_string(),
                    bb: 2,
                    span: "src/main.rs:24:5: 24:30 (#0)".to_string(),
                },
                TransOrigin {
                    fn_def_path: "cir_generated::main::cf_main".to_string(),
                    bb: 3,
                    span: "src/main.rs:26:5: 26:30 (#0)".to_string(),
                },
            ],
            ..TranslationProvenance::default()
        };

        let codegen_map = CodegenMap {
            program: "demo".to_string(),
            resources: vec![
                CodegenResource {
                    fqn: "main::m".to_string(),
                    field: "r0_main_m".to_string(),
                    kind: "Mutex".to_string(),
                },
                CodegenResource {
                    fqn: "main::cv".to_string(),
                    field: "r1_main_cv".to_string(),
                    kind: "Condvar".to_string(),
                },
                CodegenResource {
                    fqn: "main::sem".to_string(),
                    field: "r2_main_sem".to_string(),
                    kind: "Semaphore".to_string(),
                },
            ],
            holes: vec![],
            hole_ranges: BTreeMap::new(),
        };

        let subnets = vec![
            SubNetContext::new("cir_generated::main::cf_main".to_string(), p_start, p_end),
            SubNetContext::new(
                "cir_generated::main::cf_unused".to_string(),
                p_dead_start,
                p_dead_end,
            ),
        ];

        let hints = BTreeMap::new();
        let report = build_concir_net(&ConcirNetInputs {
            crate_name: "cir_generated",
            entry_mode: "main",
            net: &net,
            initial_marking: &m0,
            state_graph: &sg,
            provenance: &provenance,
            subnets: &subnets,
            codegen_map: Some(&codegen_map),
            place_field_hints: &hints,
        });

        assert_eq!(report["schema"], SCHEMA);
        assert_eq!(report["crate"], "cir_generated");
        assert_eq!(report["entry_mode"], "main");
        assert_eq!(report["truncated"], false);

        // Verify transitions & canonical ops + resource mapping.
        let transitions = report["transitions"].as_array().unwrap();
        assert_eq!(transitions.len(), 4);
        assert_eq!(transitions[0]["observable"], true);
        assert_eq!(transitions[0]["op"], "mutex_lock");
        assert_eq!(transitions[0]["resource"], "main::m");
        assert_eq!(transitions[1]["op"], "condvar_notify_all");
        assert_eq!(transitions[1]["resource"], "main::cv");
        assert_eq!(transitions[2]["observable"], true);
        assert_eq!(transitions[2]["op"], "sem_acquire");
        assert_eq!(transitions[2]["resource"], "main::sem");
        assert_eq!(transitions[3]["op"], "mutex_unlock");
        assert_eq!(transitions[3]["resource"], "main::m");

        // Verify states: initial state has no held locks; intermediate locked states
        // hold `main::m`; final state is terminal (not deadlock) with no held locks.
        let states = report["states"].as_array().unwrap();
        assert_eq!(states.len(), 5);
        assert_eq!(states[0]["initial"], true);
        assert_eq!(states[0]["held_locks"], json!([]));
        assert_eq!(states[0]["terminal"], false);
        assert_eq!(states[0]["deadlock"], false);

        let holding_states: usize = states
            .iter()
            .filter(|s| s["held_locks"] == json!(["main::m"]))
            .count();
        assert_eq!(
            holding_states, 3,
            "states after lock and before unlock must report main::m held"
        );

        let terminal_states: Vec<&Value> = states
            .iter()
            .filter(|s| s["terminal"] == json!(true))
            .collect();
        assert_eq!(terminal_states.len(), 1);
        assert_eq!(terminal_states[0]["deadlock"], false);
        assert_eq!(terminal_states[0]["held_locks"], json!([]));

        // Verify edges match state graph 1-to-1.
        assert_eq!(report["edges"].as_array().unwrap().len(), sg.edges.len());

        // Only `cf_main` reached its end place.
        assert_eq!(
            report["completed_functions"],
            json!(["cir_generated::main::cf_main"])
        );
        assert_eq!(report["purity_violations"], json!([]));
    }

    #[test]
    fn detects_sync_and_loop_purity_violations_inside_hole_ranges() {
        let mut b = PtBuilder::new();
        let m_place = b.add_marked_place(
            "Mutex_0",
            resource_place(ResourceKind::Mutex, Some(1)),
            1,
        );
        let p0 = b.add_marked_place("p0", control_place(ControlSub::FunctionStart), 1);
        let p1 = b.add_place("p1", control_place(ControlSub::BasicBlock));
        let p2 = b.add_place("p2", control_place(ControlSub::FunctionEnd));

        let t_bad_lock = b.add_transition(
            "worker_bb1_call",
            PtTransitionKind::new(TransitionType::Lock(m_place.index())),
        );
        b.add_input_arc(p0, t_bad_lock, 1);
        b.add_input_arc(m_place, t_bad_lock, 1);
        b.add_output_arc(p1, t_bad_lock, 1);

        let t_tau = b.add_transition(
            "worker_bb2_goto",
            PtTransitionKind::new(TransitionType::Goto),
        );
        b.add_input_arc(p1, t_tau, 1);
        b.add_output_arc(p2, t_tau, 1);

        let (net, m0) = b.build();
        let sg = build_sg(&net, &m0);

        let mut fn_facts = FunctionFacts::default();
        fn_facts.cut_back_edges.push((2, 1));
        fn_facts.bbs.insert(
            2,
            BbFacts {
                defs: vec![DefRecord {
                    local: 1,
                    span: "src/main.rs:44:9: 44:25 (#0)".to_string(),
                    rhs: "copy _1".to_string(),
                    operands: vec![1],
                    stop_recursion: false,
                }],
                guard: None,
            },
        );
        let mut functions = BTreeMap::new();
        functions.insert("cir_generated::main::cf_worker".to_string(), fn_facts);

        let provenance = TranslationProvenance {
            origins: vec![
                TransOrigin {
                    fn_def_path: "cir_generated::main::cf_worker".to_string(),
                    bb: 1,
                    span: "E:\\proj\\src\\main.rs:42:9: 42:32 (#0)".to_string(),
                },
                TransOrigin {
                    fn_def_path: "cir_generated::main::cf_worker".to_string(),
                    bb: 2,
                    span: "src/main.rs:44:9: 44:25 (#0)".to_string(),
                },
            ],
            functions,
            ..TranslationProvenance::default()
        };

        let mut hole_ranges = BTreeMap::new();
        hole_ranges.insert(
            "h_inc".to_string(),
            HoleRange {
                file: "src/main.rs".to_string(),
                start_line: 40,
                end_line: 46,
            },
        );
        let codegen_map = CodegenMap {
            program: "demo".to_string(),
            resources: vec![CodegenResource {
                fqn: "main::m".to_string(),
                field: "r0_main_m".to_string(),
                kind: "Mutex".to_string(),
            }],
            holes: vec![CodegenHole {
                id: "h_inc".to_string(),
                function: "main::worker".to_string(),
                sid: "s2".to_string(),
                expected: "()".to_string(),
                line: Some(40),
                ..CodegenHole::default()
            }],
            hole_ranges,
        };

        let mut hints = BTreeMap::new();
        hints.insert(m_place.index(), "r0_main_m".to_string());

        let report = build_concir_net(&ConcirNetInputs {
            crate_name: "cir_generated",
            entry_mode: "main",
            net: &net,
            initial_marking: &m0,
            state_graph: &sg,
            provenance: &provenance,
            subnets: &[],
            codegen_map: Some(&codegen_map),
            place_field_hints: &hints,
        });

        let transitions = report["transitions"].as_array().unwrap();
        assert_eq!(transitions[0]["hole_id"], json!("h_inc"));
        assert_eq!(transitions[0]["resource"], json!("main::m"));
        assert_eq!(transitions[1]["observable"], false);
        assert_eq!(transitions[1]["op"], "tau");

        let violations = report["purity_violations"].as_array().unwrap();
        assert_eq!(
            violations.len(),
            2,
            "expected both sync_in_hole and loop_in_hole violations: {violations:?}"
        );
        assert!(
            violations
                .iter()
                .any(|v| v["kind"] == "sync_in_hole" && v["op"] == "mutex_lock" && v["hole_id"] == "h_inc")
        );
        assert!(
            violations
                .iter()
                .any(|v| v["kind"] == "loop_in_hole" && v["op"] == "loop_back_edge" && v["hole_id"] == "h_inc")
        );
    }

    #[test]
    fn deadlock_state_is_flagged_deadlock_not_terminal_and_write_roundtrips() {
        let mut b = PtBuilder::new();
        let l1 = b.add_marked_place("L1", resource_place(ResourceKind::Mutex, Some(1)), 1);
        let l2 = b.add_marked_place("L2", resource_place(ResourceKind::Mutex, Some(1)), 1);
        let a0 = b.add_marked_place("a0", control_place(ControlSub::BasicBlock), 1);
        let a1 = b.add_place("a1", control_place(ControlSub::BasicBlock));
        let a2 = b.add_place("a2", control_place(ControlSub::BasicBlock));
        let a3 = b.add_place("a3", control_place(ControlSub::BasicBlock));
        let a4 = b.add_place("a4", control_place(ControlSub::FunctionEnd));
        let b0 = b.add_marked_place("b0", control_place(ControlSub::BasicBlock), 1);
        let b1 = b.add_place("b1", control_place(ControlSub::BasicBlock));
        let b2 = b.add_place("b2", control_place(ControlSub::BasicBlock));
        let b3 = b.add_place("b3", control_place(ControlSub::BasicBlock));
        let b4 = b.add_place("b4", control_place(ControlSub::FunctionEnd));

        let t0 = b.add_transition("A lock L1", PtTransitionKind::new(TransitionType::Lock(l1.index())));
        b.add_input_arc(a0, t0, 1);
        b.add_input_arc(l1, t0, 1);
        b.add_output_arc(a1, t0, 1);

        let t1 = b.add_transition("A lock L2", PtTransitionKind::new(TransitionType::Lock(l2.index())));
        b.add_input_arc(a1, t1, 1);
        b.add_input_arc(l2, t1, 1);
        b.add_output_arc(a2, t1, 1);

        let t2 = b.add_transition("A unlock L2", PtTransitionKind::new(TransitionType::Unlock(l2.index())));
        b.add_input_arc(a2, t2, 1);
        b.add_output_arc(a3, t2, 1);
        b.add_output_arc(l2, t2, 1);

        let t3 = b.add_transition("A unlock L1", PtTransitionKind::new(TransitionType::Unlock(l1.index())));
        b.add_input_arc(a3, t3, 1);
        b.add_output_arc(a4, t3, 1);
        b.add_output_arc(l1, t3, 1);

        let t4 = b.add_transition("B lock L2", PtTransitionKind::new(TransitionType::Lock(l2.index())));
        b.add_input_arc(b0, t4, 1);
        b.add_input_arc(l2, t4, 1);
        b.add_output_arc(b1, t4, 1);

        let t5 = b.add_transition("B lock L1", PtTransitionKind::new(TransitionType::Lock(l1.index())));
        b.add_input_arc(b1, t5, 1);
        b.add_input_arc(l1, t5, 1);
        b.add_output_arc(b2, t5, 1);

        let t6 = b.add_transition("B unlock L1", PtTransitionKind::new(TransitionType::Unlock(l1.index())));
        b.add_input_arc(b2, t6, 1);
        b.add_output_arc(b3, t6, 1);
        b.add_output_arc(l1, t6, 1);

        let t7 = b.add_transition("B unlock L2", PtTransitionKind::new(TransitionType::Unlock(l2.index())));
        b.add_input_arc(b3, t7, 1);
        b.add_output_arc(b4, t7, 1);
        b.add_output_arc(l2, t7, 1);

        let (net, m0) = b.build();
        let sg = build_sg(&net, &m0);
        let prov = TranslationProvenance::default();
        let hints = BTreeMap::new();

        let out_path = std::env::temp_dir()
            .join(format!("spn-concir-net-test-{}", std::process::id()))
            .join("impl_net.json");
        let _ = fs::remove_file(&out_path);

        write_concir_net(
            &ConcirNetInputs {
                crate_name: "deadlock_demo",
                entry_mode: "main",
                net: &net,
                initial_marking: &m0,
                state_graph: &sg,
                provenance: &prov,
                subnets: &[],
                codegen_map: None,
                place_field_hints: &hints,
            },
            &out_path,
        )
        .expect("write_concir_net succeeds");

        let parsed: Value =
            serde_json::from_str(&fs::read_to_string(&out_path).unwrap()).expect("valid JSON");
        let states = parsed["states"].as_array().unwrap();
        let deadlocked: Vec<&Value> = states
            .iter()
            .filter(|s| s["deadlock"] == json!(true))
            .collect();
        assert_eq!(deadlocked.len(), 1);
        assert_eq!(deadlocked[0]["terminal"], false);
        assert_eq!(deadlocked[0]["held_locks"], json!(["L1", "L2"]));

        let terminal: Vec<&Value> = states
            .iter()
            .filter(|s| s["terminal"] == json!(true))
            .collect();
        assert_eq!(terminal.len(), 1);
        assert_eq!(terminal[0]["deadlock"], false);
        assert_eq!(terminal[0]["held_locks"], json!([]));

        let _ = fs::remove_dir_all(out_path.parent().unwrap());
    }

    #[test]
    fn parses_windows_and_unix_spans_and_maps_all_canonical_ops() {
        assert_eq!(
            parse_span_file_line("src/main.rs:42:5: 42:30 (#0)"),
            Some(("src/main.rs".to_string(), 42))
        );
        assert_eq!(
            parse_span_file_line("C:\\repo\\proj\\src\\main.rs:108:9: 108:40 (#0)"),
            Some(("C:/repo/proj/src/main.rs".to_string(), 108))
        );
        assert_eq!(
            parse_span_file_line("./src/main.rs:7:1"),
            Some(("src/main.rs".to_string(), 7))
        );
        assert_eq!(parse_span_file_line("no-location (#0)"), None);

        let mut b = PtBuilder::new();
        let rw = b.add_marked_place("rw", resource_place(ResourceKind::RwLock, Some(10)), 10);
        let at = b.add_marked_place("at", resource_place(ResourceKind::Atomic, Some(1)), 1);
        let p0 = b.add_marked_place("p0", control_place(ControlSub::BasicBlock), 1);

        let t_r = b.add_transition("r", PtTransitionKind::new(TransitionType::RwLockRead(rw.index())));
        let t_w = b.add_transition("w", PtTransitionKind::new(TransitionType::RwLockWrite(rw.index())));
        let t_ru = b.add_transition("ru", PtTransitionKind::new(TransitionType::Unlock(rw.index())));
        let t_wait = b.add_transition("wait", PtTransitionKind::new(TransitionType::Wait));
        let t_al = b.add_transition(
            "al",
            PtTransitionKind::new(TransitionType::AtomicLoad(
                unipn::pt::AliasId {
                    instance_id: 0,
                    local: 1,
                    array_index: None,
                    field: None,
                },
                unipn::pt::AtomicOrdering::SeqCst,
                String::new(),
                0,
            )),
        );
        b.add_input_arc(at, t_al, 1);
        b.add_output_arc(at, t_al, 1);
        let t_as = b.add_transition(
            "as",
            PtTransitionKind::new(TransitionType::AtomicStore(
                unipn::pt::AliasId {
                    instance_id: 0,
                    local: 1,
                    array_index: None,
                    field: None,
                },
                unipn::pt::AtomicOrdering::SeqCst,
                String::new(),
                0,
            )),
        );
        let t_cas = b.add_transition(
            "cas",
            PtTransitionKind::new(TransitionType::AtomicCmpXchg(
                unipn::pt::AliasId {
                    instance_id: 0,
                    local: 1,
                    array_index: None,
                    field: None,
                },
                unipn::pt::AtomicOrdering::SeqCst,
                unipn::pt::AtomicOrdering::SeqCst,
                String::new(),
                0,
            )),
        );
        let t_sp = b.add_transition("sp", PtTransitionKind::new(TransitionType::Spawn("worker".into())));
        let t_jn = b.add_transition("jn", PtTransitionKind::new(TransitionType::Join("worker".into())));
        let t_cs = b.add_transition(
            "cir_sync::channel_send::r0_main_ch::cir_trace::Channel::send_sid_summary_t0",
            PtTransitionKind::new(TransitionType::Function),
        );
        let t_cr = b.add_transition(
            "cir_sync::channel_recv::r0_main_ch::cir_trace::Channel::recv_sid_summary_t0",
            PtTransitionKind::new(TransitionType::Function),
        );
        let t_sr = b.add_transition(
            "cir_sync::sem_release::r1_main_sem::cir_trace::Semaphore::release_sid_summary_t0",
            PtTransitionKind::new(TransitionType::Function),
        );
        let _ = p0;
        let (net, _) = b.build();
        let prov = TranslationProvenance::default();

        assert_eq!(classify_transition(&net, t_r, &prov).1, "rwlock_read");
        assert_eq!(classify_transition(&net, t_w, &prov).1, "rwlock_write");
        assert_eq!(classify_transition(&net, t_ru, &prov).1, "rwlock_unlock");
        assert_eq!(classify_transition(&net, t_wait, &prov).1, "condvar_wait");
        assert_eq!(classify_transition(&net, t_al, &prov).1, "atomic_load");
        assert_eq!(classify_transition(&net, t_as, &prov).1, "atomic_store");
        assert_eq!(classify_transition(&net, t_cas, &prov).1, "atomic_cas");
        assert_eq!(classify_transition(&net, t_sp, &prov).1, "spawn");
        assert_eq!(classify_transition(&net, t_jn, &prov).1, "join");
        assert_eq!(classify_transition(&net, t_cs, &prov), (true, "channel_send", Some("r0_main_ch".to_string())));
        assert_eq!(classify_transition(&net, t_cr, &prov), (true, "channel_recv", Some("r0_main_ch".to_string())));
        assert_eq!(classify_transition(&net, t_sr, &prov), (true, "sem_release", Some("r1_main_sem".to_string())));
    }
}
