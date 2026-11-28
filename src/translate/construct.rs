use crate::Options;
use crate::analysis::api_patterns::KeyApiRegex;
use crate::analysis::primitives::blocking::LockGuardMap;
use crate::config::LoopSemantics;
use crate::translate::net::{FunctionRegistry, NetBuilder, PlaceId, ResourceRegistry};
use crate::translate::resources::PlaceBinding;
use crate::translate::resources::lock_binder::ResourceBinder;
use crate::util::format_name;
use petgraph::graph::NodeIndex;
use petgraph::visit::IntoNodeReferences;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::cell::RefCell;
use std::sync::Arc;
use std::time::Instant;

use crate::analysis::callgraph::{CallGraph, CallGraphNode, InstanceId};
use crate::analysis::entry_plan::{EntryPlan, EntryPlanner};
use crate::analysis::memory::alias_engine::AliasEngine;
use crate::pipeline::analyze::ResourcePlan;
use crate::translate::lower::BodyToPetriNet;

/// Whether `process_functions` should build `_start`/`_end` for this node.
///
/// Both checks are required. `WithBody` is how the call graph records
/// "this def will be expanded"; `is_mir_available` is whether translation can
/// mark `_end`. Either failure leaves the call on the existing direct edge.
pub(crate) fn callee_frame_eligible(with_body: bool, mir_available: bool) -> bool {
    with_body && mir_available
}

pub use crate::analysis::entry_plan::EntryMode;

/// One concurrent entry point of a library-mode net: the function name and the
/// `_start`/`_end` control places the translation created for it.
///
/// Root *instances* that share a `DefId` share one pair of places, so the list
/// is deduplicated by place; the initial marking marks one token per pair.
#[derive(Clone, Debug)]
pub struct LibraryRootEntry {
    pub name: String,
    pub start: PlaceId,
    pub end: PlaceId,
}

pub struct PetriNet<'analysis, 'tcx> {
    pub(crate) options: Options,
    pub(crate) tcx: rustc_middle::ty::TyCtxt<'tcx>,
    pub net: NetBuilder<'tcx>,
    pub(crate) callgraph: &'analysis CallGraph<'tcx>,
    pub alias: RefCell<AliasEngine<'tcx>>,
    /// Sites, classes, and concurrent roots from `analyze_resources`.
    pub(crate) plan: ResourcePlan<'tcx>,
    pub(crate) functions: FunctionRegistry,
    pub(crate) lock_info: Arc<LockGuardMap<'tcx>>,
    pub(crate) resources: ResourceRegistry,
    /// Lock-guard grouping. Translation still looks up `resources`.
    pub(crate) resource_binder: ResourceBinder,
    /// Proposed-versus-built resource classes. Filled after places exist.
    /// Never read by lowering.
    pub(crate) resource_shadow: Vec<crate::analysis::sync::shadow::MemberDiff>,
    /// Slot of each collected site. Lowering still reads [`ResourceRegistry`];
    /// this map is the same assignment.
    pub(crate) resource_map: crate::analysis::sync::ResourceMap,
    pub(crate) place_binding: PlaceBinding,
    pub entry_exit: (PlaceId, PlaceId),
    /// Copy of [`EntryPlan::mode`]. Assigned only from that plan.
    pub entry_mode: EntryMode,
    /// The only source of entry mode, roots, and the reachable set.
    /// `None` until `construct` runs.
    entry_plan: Option<EntryPlan>,
    /// Read-only translation coverage record (`translation-coverage.json`).
    pub coverage: crate::report::coverage::Coverage,
    /// One summary per translated function.
    pub subnets: Vec<crate::translate::net::subnets::SubNetContext>,
}

impl<'analysis, 'tcx> PetriNet<'analysis, 'tcx> {
    pub fn tcx(&self) -> rustc_middle::ty::TyCtxt<'tcx> {
        self.tcx
    }

    pub fn options(&self) -> &crate::options::Options {
        &self.options
    }

    pub fn callgraph(&self) -> &'analysis CallGraph<'tcx> {
        self.callgraph
    }

    pub fn new(
        options: Options,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        callgraph: &'analysis CallGraph<'tcx>,
        alias: AliasEngine<'tcx>,
        plan: ResourcePlan<'tcx>,
    ) -> Self {
        Self {
            options,
            tcx,
            net: NetBuilder::new(),
            callgraph,
            alias: RefCell::new(alias),
            plan,
            functions: FunctionRegistry::new(),
            lock_info: Arc::new(FxHashMap::default()),
            resources: ResourceRegistry::new(),
            resource_binder: ResourceBinder::empty(),
            resource_shadow: Vec::new(),
            resource_map: crate::analysis::sync::ResourceMap::default(),
            place_binding: PlaceBinding::default(),
            entry_exit: (PlaceId(0), PlaceId(0)),
            entry_mode: EntryMode::Main,
            entry_plan: None,
            coverage: crate::report::coverage::Coverage::new(),
            subnets: Vec::new(),
        }
    }

    pub fn build(&mut self) {
        let start_time = Instant::now();

        log::info!("Construct Function Start and End Places");
        let (plan, entry_cov) = {
            let tcx = self.tcx;
            let options = &self.options;
            let callgraph = self.callgraph;
            let sync_roots = &self.plan.sync_roots;
            let marks = self.plan.root_marks.clone();
            EntryPlanner {
                tcx,
                options,
                callgraph,
            }
            .plan(sync_roots, &marks)
        };
        for mark in &entry_cov.marks {
            self.coverage.record_concurrent_root(
                mark.instance.index(),
                mark.reason,
                mark.is_private,
            );
        }
        self.construct_entries(&plan);
        self.entry_plan = Some(plan);

        self.construct_lock_places();
        self.construct_atomic_places();
        self.construct_unsafe_places();

        let key_api_regex = KeyApiRegex::new(&self.options.config);
        if self.options.config.bool_guard_abstraction {
            self.construct_bool_guard_predicates(&key_api_regex);
        }
        self.fill_resource_map();
        self.translate_all_functions(&key_api_regex);
        self.emit_resource_shadow();

        log::info!("Visitor Function Body Complete!");
        log::info!("Construct Petri Net Time: {:?}", start_time.elapsed());
    }

    fn translate_all_functions(&mut self, key_api_regex: &KeyApiRegex) {
        let reachable = self.reachable_instance_ids();
        let mut visited_func_id = FxHashSet::<DefId>::default();
        for (node, caller) in self.callgraph.graph.node_references() {
            if let Some(ref set) = reachable {
                if !set.contains(&node) {
                    continue;
                }
            }
            if self.tcx.is_mir_available(caller.instance().def_id())
                && self.crate_filter_match(&format_name(caller.instance().def_id()))
            {
                log::debug!(
                    "Current visitor function body: {:?}",
                    format_name(caller.instance().def_id())
                );
                let def_id = caller.instance().def_id();
                if visited_func_id.contains(&def_id) {
                    continue;
                }
                self.visitor_function_body(node, caller, key_api_regex);
                visited_func_id.insert(def_id);
            }
        }
    }

    /// Resolve `loop_semantics`: an explicit config/CLI value wins; otherwise a
    /// binary crate keeps the historical `cut` and a library crate uses
    /// `summary` (loop-sink false candidates were the dominant
    /// false-positive source in library exploration).
    fn effective_loop_semantics(&self) -> LoopSemantics {
        match self.options.config.loop_semantics {
            Some(mode) => mode,
            None => match self
                .entry_plan
                .as_ref()
                .map(|plan| plan.mode)
                .unwrap_or(self.entry_mode)
            {
                EntryMode::Main => LoopSemantics::Cut,
                EntryMode::LibraryRoots => LoopSemantics::Summary,
            },
        }
    }

    pub fn visitor_function_body(
        &mut self,
        node: NodeIndex,
        caller: &CallGraphNode<'tcx>,
        key_api_regex: &KeyApiRegex,
    ) {
        self.translate_function_body(node, caller, key_api_regex);
    }

    fn translate_function_body(
        &mut self,
        node: NodeIndex,
        caller: &CallGraphNode<'tcx>,
        key_api_regex: &KeyApiRegex,
    ) {
        // Use instance_mir (not optimized_mir) so pointer analysis and translation share the same MIR.
        // instance_mir is correctly monomorphized; optimized_mir may still be polymorphic.
        let body = self.tcx.instance_mir(caller.instance().def);

        if body.source.promoted.is_some() {
            return;
        }

        // MIR dot dumping happens centrally in callback.rs; intermediate dumps could go here.

        let translate_atomic_ordering = false;

        let loop_semantics = self.effective_loop_semantics();
        let mut func_body = BodyToPetriNet::new(
            node,
            caller.instance(),
            body,
            self.tcx,
            &self.callgraph,
            &mut self.net,
            &mut self.alias,
            Arc::clone(&self.lock_info),
            &self.functions,
            &self.resources,
            &self.resource_map,
            &self.place_binding,
            self.entry_exit,
            key_api_regex,
            self.options.config.alias_unknown_policy,
            self.options.config.condvar_model,
            self.options.config.break_cfg_cycles,
            loop_semantics,
            self.options.config.loop_summary_k,
            translate_atomic_ordering,
            &mut self.coverage,
        );
        func_body.translate();
        self.subnets.push(func_body.take_subnet());
    }

    /// Create function places in call-graph order, then mark entry tokens.
    /// `plan.mode` is the only source of `entry_mode`.
    fn construct_entries(&mut self, plan: &EntryPlan) {
        self.entry_mode = plan.mode;
        self.coverage.set_entry_mode(self.entry_mode.as_str());
        match plan.mode {
            EntryMode::Main => {
                let main_func = self.tcx.entry_fn(()).map(|(main_func, _)| main_func);
                let Some(main_func) = main_func else {
                    return;
                };
                self.process_functions(plan.reachable.as_ref(), |self_, func_id, func_name| {
                    if func_id == main_func {
                        let (start, end) = self_.create_function_places(func_name, true);
                        self_.entry_exit = (start, end);
                        (start, end)
                    } else {
                        self_.create_function_places(func_name, false)
                    }
                });
            }
            EntryMode::LibraryRoots => self.construct_library_entries(plan),
        }
    }

    /// Library-crate initial marking: no `entry_fn` exists, so every
    /// *concurrent root* (a function using locks/atomics/condvars —
    /// the same set `translate_concurrent_roots` widens to) is treated as a
    /// possible synchronization entry point and gets one initial token on its
    /// `_start` place. Reading: "any sync entry of the library may be called
    /// concurrently by another thread", which is the correct initial
    /// condition for library-internal interleavings.
    ///
    /// The narrower alternative (initial marking by `#[test]` reachability)
    /// is recorded in the design notes; it is not the default because it
    /// would restrict the analysis to tests that happen to exist.
    fn construct_library_entries(&mut self, plan: &EntryPlan) {
        let exported = &plan.exported;
        let roots = &plan.roots;
        let fallback_used = plan.fallback_used;
        let private_skipped = plan.private_skipped;
        // Every translated function gets its `_start`/`_end` places; only the
        // roots are initially marked below.
        self.process_functions(plan.reachable.as_ref(), |self_, _func_id, func_name| {
            self_.create_function_places(func_name, false)
        });

        let mut marked = 0usize;
        let mut public_marked = 0usize;
        let mut unplaced = 0usize;
        let mut unplaced_roots = Vec::new();
        let mut entries = Vec::new();
        for root in roots {
            let Some(instance) = self.callgraph.index_to_instance(*root) else {
                continue;
            };
            let def_id = instance.instance().def_id();
            if let Some(&(start, _)) = self.functions.counter().get(&def_id) {
                self.net.set_tokens(start, 1);
                marked += 1;
                if exported.contains(root) {
                    public_marked += 1;
                }
                entries.push(format_name(def_id));
            } else {
                // The function was filtered out (crate filter / ignore list);
                // it cannot be an entry point of the analysed net. Logged, not
                // fatal: the remaining roots still cover the library.
                unplaced += 1;
                let func_name = format_name(def_id);
                let reason = if !self.crate_filter_match(&func_name) {
                    "crate_filtered"
                } else {
                    "not_reachable"
                };
                unplaced_roots.push(crate::report::coverage::UnplacedRoot {
                    name: func_name,
                    reason: reason.to_string(),
                });
            }
        }
        self.coverage.record_library_entries(
            marked,
            unplaced,
            public_marked,
            private_skipped,
            fallback_used,
            entries,
            unplaced_roots,
        );
        log::info!(
            "library entry: {marked} root(s) initially marked (public={public_marked}, private_skipped={private_skipped}, fallback={fallback_used}), {unplaced} root(s) without a function place"
        );
    }

    /// The `LibraryRoots` entry points with their `_start`/`_end` places, in a
    /// deterministic order (function name, then place id). Empty in `Main`
    /// mode.
    ///
    /// This is the view the per-entry slicer needs: roots whose instances share
    /// a `DefId` share one place pair (and one initial token), so entries are
    /// deduplicated by their start place. The order is stable across runs even
    /// though the root set is a `FxHashSet`.
    pub fn library_root_entries(&self) -> Vec<LibraryRootEntry> {
        let Some(plan) = self.entry_plan.as_ref() else {
            return Vec::new();
        };
        if plan.mode != EntryMode::LibraryRoots {
            return Vec::new();
        }
        let roots = &plan.roots;
        let mut by_place: std::collections::BTreeMap<usize, LibraryRootEntry> =
            std::collections::BTreeMap::new();
        for root in roots {
            let Some(instance) = self.callgraph.index_to_instance(*root) else {
                continue;
            };
            let def_id = instance.instance().def_id();
            let Some(&(start, end)) = self.functions.counter().get(&def_id) else {
                continue;
            };
            by_place
                .entry(start.index())
                .or_insert_with(|| LibraryRootEntry {
                    name: format_name(def_id),
                    start,
                    end,
                });
        }
        let mut entries: Vec<LibraryRootEntry> = by_place.into_values().collect();
        entries.sort_by(|a, b| {
            a.name
                .cmp(&b.name)
                .then_with(|| a.start.index().cmp(&b.start.index()))
        });
        entries
    }

    fn process_functions<F>(&mut self, reachable: Option<&FxHashSet<InstanceId>>, create_places: F)
    where
        F: Fn(&mut Self, DefId, String) -> (PlaceId, PlaceId),
    {
        let mut with_body = 0usize;
        let mut without_body = 0usize;
        for weight in self.callgraph.graph.node_weights() {
            match weight {
                CallGraphNode::WithBody(_) => with_body += 1,
                CallGraphNode::WithoutBody(_) => without_body += 1,
            }
        }
        self.coverage.record_callgraph_counts(
            self.callgraph.graph.node_count(),
            with_body,
            without_body,
        );

        let mut dispositions: FxHashMap<DefId, crate::report::coverage::FunctionDisposition> =
            FxHashMap::default();
        for node_idx in self.callgraph.graph.node_indices() {
            let func_instance = self.callgraph.graph.node_weight(node_idx).unwrap();
            let func_id = func_instance.instance().def_id();
            if let Some(ref set) = reachable {
                if !set.contains(&node_idx) {
                    dispositions
                        .entry(func_id)
                        .or_insert(crate::report::coverage::FunctionDisposition::NotReachable);
                    continue;
                }
            }
            let func_name = format_name(func_id);
            if !self.crate_filter_match(&func_name) || self.functions.contains(&func_id) {
                if !self.functions.contains(&func_id) {
                    dispositions.insert(
                        func_id,
                        crate::report::coverage::FunctionDisposition::CrateFiltered,
                    );
                }
                continue;
            }

            // Frames exist only for bodies that `translate_all_functions` will
            // actually walk. A `WithoutBody` node or a def with no MIR would
            // otherwise leave an `_end` that no transition can mark, and every
            // caller would wait on it forever. `callee_frame` then returns
            // `None` and `handle_normal_call` keeps the existing direct edge.
            let with_body = matches!(func_instance, CallGraphNode::WithBody(_));
            let mir_available = self.tcx.is_mir_available(func_id);
            if !callee_frame_eligible(with_body, mir_available) {
                dispositions
                    .entry(func_id)
                    .or_insert(crate::report::coverage::FunctionDisposition::NoMirCallee);
                continue;
            }

            let (start, end) = create_places(self, func_id, func_name);
            self.functions.insert(func_id, start, end);
            dispositions.insert(
                func_id,
                crate::report::coverage::FunctionDisposition::Translated,
            );
        }

        let mut translated_functions = 0usize;
        let mut not_reachable = 0usize;
        let mut crate_filtered = 0usize;
        let mut ignored_by_name = 0usize;
        let mut no_mir_callee = 0usize;
        let mut exported_functions = 0usize;
        let mut translated_exported = 0usize;
        let mut method = crate::report::coverage::PublicApiMethod::EffectiveVisibilities;
        let mut dropped = Vec::new();

        for (func_id, disp) in dispositions {
            let (is_exported, api_method) =
                crate::report::coverage::is_function_exported(self.tcx, func_id);
            method = api_method;
            if is_exported {
                exported_functions += 1;
            }
            match disp {
                crate::report::coverage::FunctionDisposition::Translated => {
                    translated_functions += 1;
                    if is_exported {
                        translated_exported += 1;
                    }
                }
                crate::report::coverage::FunctionDisposition::NotReachable => {
                    not_reachable += 1;
                }
                crate::report::coverage::FunctionDisposition::CrateFiltered => {
                    crate_filtered += 1;
                    dropped.push(crate::report::coverage::DroppedFunction {
                        name: format_name(func_id),
                        reason: crate::report::coverage::DropReason::CrateFiltered,
                        pattern: None,
                        span: format!("{:?}", self.tcx.def_span(func_id)),
                    });
                }
                crate::report::coverage::FunctionDisposition::NoMirCallee => {
                    no_mir_callee += 1;
                }
                crate::report::coverage::FunctionDisposition::IgnoredByName(pattern) => {
                    ignored_by_name += 1;
                    dropped.push(crate::report::coverage::DroppedFunction {
                        name: format_name(func_id),
                        reason: crate::report::coverage::DropReason::IgnoredByName,
                        pattern: Some(pattern),
                        span: format!("{:?}", self.tcx.def_span(func_id)),
                    });
                }
            }
        }

        self.coverage.public_api_method = method;
        self.coverage.counts.translated_functions = translated_functions;
        self.coverage.counts.not_reachable = not_reachable;
        self.coverage.counts.crate_filtered = crate_filtered;
        self.coverage.counts.ignored_by_name = ignored_by_name;
        self.coverage.counts.no_mir_callee = no_mir_callee;
        self.coverage.public_api.exported_functions = exported_functions;
        self.coverage.public_api.translated_exported = translated_exported;
        self.coverage.dropped = dropped;
    }

    pub(crate) fn crate_filter_match(&self, func_name: &str) -> bool {
        self.options.crate_filter_match(func_name)
    }

    pub(crate) fn reachable_instance_ids(&self) -> Option<FxHashSet<InstanceId>> {
        self.entry_plan
            .as_ref()
            .and_then(|plan| plan.reachable.clone())
    }
}

#[cfg(test)]
mod callee_frame_tests {
    use super::callee_frame_eligible;

    /// `fixtures/dyn_dispatch_no_wait`: `&dyn Counter::value` is a trait method
    /// with no MIR (`WithBody` is false, or MIR is unavailable). No frame.
    #[test]
    fn dyn_dispatch_no_wait_trait_method_gets_no_frame() {
        assert!(!callee_frame_eligible(false, false));
        assert!(!callee_frame_eligible(false, true));
        assert!(!callee_frame_eligible(true, false));
    }

    /// The same fixture's `local_add` is a local function with MIR. It still
    /// gets `_start`/`_end`, so the caller still builds the wait/ret subnet.
    #[test]
    fn local_function_with_mir_still_gets_a_frame() {
        assert!(callee_frame_eligible(true, true));
    }
}
