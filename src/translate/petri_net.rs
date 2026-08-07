use crate::Options;
use crate::concurrency::atomic::{AtomicCollector, AtomicOrdering};
use crate::concurrency::blocking::BlockingCollector;
use crate::concurrency::channel::{ChannelCollector, ChannelInfo, EndpointType};
use crate::memory::pointsto::AliasId;
use crate::memory::unsafe_memory::UnsafeAnalyzer;
use crate::net::structure::PlaceType;
use crate::translate::structure::{FunctionRegistry, KeyApiRegex, ResourceRegistry};
use crate::util::format_name;
use petgraph::graph::NodeIndex;
use petgraph::visit::IntoNodeReferences;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use std::cell::RefCell;
use std::sync::Arc;
use std::time::Instant;

use super::callgraph::{CallGraph, CallGraphNode, InstanceId};
use crate::concurrency::blocking::{LockGuardId, LockGuardMap, LockGuardTy};
use crate::memory::alias_engine::AliasEngine;
use crate::net::{Net, Place, PlaceId};
use crate::translate::mir_to_pn::BodyToPetriNet;

fn find(union_find: &FxHashMap<LockGuardId, LockGuardId>, x: &LockGuardId) -> LockGuardId {
    let mut current = x;
    while union_find[current] != *current {
        current = &union_find[current];
    }
    current.clone()
}

fn union(union_find: &mut FxHashMap<LockGuardId, LockGuardId>, x: &LockGuardId, y: &LockGuardId) {
    let root_x = find(union_find, x);
    let root_y = find(union_find, y);
    if root_x != root_y {
        union_find.insert(root_y, root_x);
    }
}

pub struct PetriNet<'analysis, 'tcx> {
    options: Options,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    pub net: Net,
    callgraph: &'analysis CallGraph<'tcx>,
    pub alias: RefCell<AliasEngine<'analysis, 'tcx>>,
    functions: FunctionRegistry,
    lock_info: Arc<LockGuardMap<'tcx>>,
    resources: ResourceRegistry,
    pub entry_exit: (PlaceId, PlaceId),
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

    fn create_resource_place(
        &mut self,
        name: String,
        initial: u64,
        capacity: u64,
        span: String,
    ) -> PlaceId {
        let place = Place::new(name, initial, capacity, PlaceType::Resources, span);
        self.net.add_place(place)
    }

    pub fn new(
        options: Options,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        callgraph: &'analysis CallGraph<'tcx>,
    ) -> Self {
        let alias = RefCell::new(AliasEngine::new(tcx, callgraph, &options.config));
        Self {
            options,
            tcx,
            net: Net::empty(),
            callgraph,
            alias,
            functions: FunctionRegistry::new(),
            lock_info: Arc::new(FxHashMap::default()),
            resources: ResourceRegistry::new(),
            entry_exit: (PlaceId::new(0), PlaceId::new(0)),
        }
    }

    pub fn construct_channel_resources(&mut self) {
        let mut channel_collector =
            ChannelCollector::new(self.tcx, self.callgraph, self.options.crate_name.clone());
        channel_collector.analyze();
        channel_collector.to_json_pretty().unwrap();

        let mut span_groups: FxHashMap<String, Vec<(AliasId, ChannelInfo<'tcx>)>> =
            FxHashMap::default();

        for (id, info) in channel_collector.channels {
            let key_string = format!("{:?}", info.span)
                .split(":")
                .take(2)
                .collect::<Vec<&str>>()
                .join("");
            span_groups
                .entry(key_string)
                .or_default()
                .push((AliasId::from(id), info));
        }

        for (i, (span, endpoints)) in span_groups.iter().enumerate() {
            if endpoints.len() == 2 {
                let has_pair = endpoints
                    .iter()
                    .any(|(_, info)| info.endpoint_type == EndpointType::Sender)
                    && endpoints
                        .iter()
                        .any(|(_, info)| info.endpoint_type == EndpointType::Receiver);

                if has_pair {
                    let channel_id = format!("channel_{}", i);
                    let channel_node = self.create_resource_place(channel_id, 0, 100, span.clone());

                    for (id, _) in endpoints {
                        self.resources
                            .channel_places_mut()
                            .insert(*id, channel_node);
                    }

                    log::debug!(
                        "Created shared channel place for endpoints at span: {}",
                        span
                    );
                }
            }
        }
    }

    pub fn construct_atomic_resources(&mut self) {
        let mut atomic_collector =
            AtomicCollector::new(self.tcx, self.callgraph, self.options.crate_name.clone());
        let atomic_vars = atomic_collector.analyze();

        if atomic_vars.is_empty() {
            log::warn!("Not Found Atomic Variables In This Crate");
            return;
        }

        for (_, atomic_info) in atomic_vars {
            let alias_id = atomic_info.get_alias_id();
            if let Some(op) = atomic_info.operations.first() {
                self.resources
                    .atomic_orders_mut()
                    .insert(alias_id, op.ordering);
            } else {
                log::warn!(
                    "atomic variable {:?} has no recorded operations; ordering fallback to Relaxed",
                    alias_id
                );
                self.resources
                    .atomic_orders_mut()
                    .insert(alias_id, AtomicOrdering::Relaxed);
            }

            let policy = self.options.config.alias_unknown_policy;
            let place_ids: Vec<_> = {
                let mut alias_analysis = self.alias.borrow_mut();
                let mut all_places = Vec::new();
                for (existing, places) in self.resources.atomic_places().iter() {
                    if alias_analysis
                        .alias_atomic(alias_id, *existing)
                        .may_alias(policy)
                    {
                        all_places.extend(places.iter().copied());
                    }
                }
                all_places
            };

            let place_ids: Vec<_> = if place_ids.is_empty() {
                let place_name = format!(
                    "Atomic({},{})",
                    alias_id.instance_id.index(),
                    alias_id.local.index()
                );
                let pid = self.create_resource_place(place_name, 1, 1, atomic_info.span.clone());
                vec![pid]
            } else {
                place_ids
                    .into_iter()
                    .collect::<FxHashSet<_>>()
                    .into_iter()
                    .collect()
            };

            self.resources
                .atomic_places_mut()
                .insert(alias_id, place_ids);
        }
    }

    fn construct_unsafe_blocks(&mut self) {
        let unsafe_analyzer =
            UnsafeAnalyzer::new(self.tcx, self.callgraph, self.options.crate_name.clone());
        let (unsafe_info, unsafe_data) = unsafe_analyzer.analyze();
        if unsafe_info.is_empty() {
            log::debug!("Not Found Unsafe Blocks In This Crate");
            return;
        }

        let mut next_alias_id: u32 = 0;
        let mut alias_groups: FxHashMap<u32, Vec<(AliasId, String)>> = FxHashMap::default();
        let places_data: Vec<_> = unsafe_data
            .unsafe_places
            .iter()
            .map(|(local, info)| (*local, info.clone()))
            .collect();

        for i in 0..places_data.len() {
            let (local_i, info_i) = &places_data[i];

            if alias_groups
                .values()
                .any(|group| group.iter().any(|(l, _)| l == local_i))
            {
                continue;
            }

            let mut current_group = vec![(local_i.clone(), info_i.clone())];

            let policy = self.options.config.alias_unknown_policy;
            for j in i + 1..places_data.len() {
                let (local_j, info_j) = &places_data[j];
                if self
                    .alias
                    .borrow_mut()
                    .alias(*local_i, *local_j)
                    .may_alias(policy)
                {
                    current_group.push((local_j.clone(), info_j.clone()));
                }
            }

            if !current_group.is_empty() {
                alias_groups.insert(next_alias_id, current_group);
                next_alias_id += 1;
            }
        }

        for (_, group) in alias_groups {
            let unsafe_span = group[0].1.clone();
            let unsafe_local = group[0].0.clone();
            let unsafe_name = format!("{:?}", unsafe_local);

            let place_id = self.create_resource_place(unsafe_name, 1, 1, unsafe_span);
            self.resources
                .unsafe_places_mut()
                .insert(unsafe_local, place_id);

            for (local, _) in group {
                self.resources.unsafe_places_mut().insert(local, place_id);
            }
        }
    }

    pub fn construct(&mut self /*alias_analysis: &'pn RefCell<AliasAnalysis<'pn, 'tcx>>*/) {
        let start_time = Instant::now();

        log::info!("Construct Function Start and End Places");
        self.construct_func();

        if cfg!(feature = "atomic-violation") {
            self.construct_atomic_resources();
            let key_api_regex = KeyApiRegex::new(&self.options.config);
            self.translate_all_functions(&key_api_regex);
            log::info!("Visitor Function Body Complete!");
            log::info!("Construct Petri Net Time: {:?}", start_time.elapsed());
            return;
        }

        self.construct_lock_with_dfs();
        self.construct_channel_resources();
        self.construct_atomic_resources();
        self.construct_unsafe_blocks();

        let key_api_regex = KeyApiRegex::new(&self.options.config);
        self.translate_all_functions(&key_api_regex);

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
                if visited_func_id.contains(&caller.instance().def_id()) {
                    continue;
                }
                self.visitor_function_body(node, caller, key_api_regex);
                visited_func_id.insert(caller.instance().def_id());
            }
        }
    }

    pub fn visitor_function_body(
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
            self.entry_exit,
            key_api_regex,
            self.options.config.alias_unknown_policy,
            self.options.config.break_cfg_cycles,
        );
        func_body.translate();
    }

    pub fn construct_func(&mut self) {
        let main_func = match self.tcx.entry_fn(()) {
            Some((main_func, _)) => main_func,
            None => {
                log::debug!("cargo pta need a entry point!");
                return;
            }
        };

        self.process_functions(|self_, func_id, func_name| {
            if func_id == main_func {
                let (start, end) = self_.create_function_places(func_name, true);
                self_.entry_exit = (start, end);
                (start, end)
            } else {
                self_.create_function_places(func_name, false)
            }
        });
    }

    fn process_functions<F>(&mut self, create_places: F)
    where
        F: Fn(&mut Self, DefId, String) -> (PlaceId, PlaceId),
    {
        let reachable = self.reachable_instance_ids();
        for node_idx in self.callgraph.graph.node_indices() {
            if let Some(ref set) = reachable {
                if !set.contains(&node_idx) {
                    continue;
                }
            }
            let func_instance = self.callgraph.graph.node_weight(node_idx).unwrap();
            let func_id = func_instance.instance().def_id();
            let func_name = format_name(func_id);
            if !self.crate_filter_match(&func_name)
                || self.functions.contains(&func_id)
                || Self::should_ignore_function(&func_name)
            {
                continue;
            }

            let (start, end) = create_places(self, func_id, func_name);
            self.functions.insert(func_id, start, end);
        }
    }

    fn crate_filter_match(&self, func_name: &str) -> bool {
        use crate::options::CrateNameList;
        let include = match &self.options.crate_filter {
            CrateNameList::White(list) if !list.is_empty() => {
                list.iter().any(|c| func_name.starts_with(c))
            }
            _ => func_name.starts_with(&self.options.crate_name),
        };
        let exclude = match &self.options.crate_filter {
            CrateNameList::Black(list) if !list.is_empty() => {
                list.iter().any(|c| func_name.starts_with(c))
            }
            _ => false,
        };
        include && !exclude
    }

    /// Collect `InstanceId`s for functions that use locks / atomics / condvars / channels.
    /// Used by `translate_concurrent_roots` to widen translation to those roots and callees.
    fn concurrent_root_instance_ids(&self) -> FxHashSet<InstanceId> {
        let mut roots = FxHashSet::default();

        for (instance_id, node) in self.callgraph.graph.node_references() {
            let instance = match node {
                CallGraphNode::WithBody(inst) => inst,
                _ => continue,
            };
            if !instance.def_id().is_local() {
                continue;
            }
            let body = self.tcx.instance_mir(instance.def);
            let mut blocking = BlockingCollector::new(instance_id, instance, body, self.tcx);
            blocking.analyze();
            if !blocking.lockguards.is_empty() || !blocking.condvars.is_empty() {
                roots.insert(instance_id);
            }
        }

        let mut atomic =
            AtomicCollector::new(self.tcx, self.callgraph, self.options.crate_name.clone());
        for info in atomic.analyze().into_values() {
            roots.insert(info.instance_id);
        }

        let mut channel =
            ChannelCollector::new(self.tcx, self.callgraph, self.options.crate_name.clone());
        channel.analyze();
        for (channel_id, _) in channel.channels {
            roots.insert(channel_id.instance_id);
        }

        roots
    }

    fn reachable_instance_ids(&self) -> Option<FxHashSet<InstanceId>> {
        if !self.options.config.entry_reachable {
            return None;
        }
        let main_func = self.tcx.entry_fn(()).map(|(id, _)| id)?;
        let mut reachable = self.callgraph.reachable_from_entry(self.tcx, main_func);

        if self.options.config.translate_concurrent_roots {
            let concurrent_roots = self.concurrent_root_instance_ids();
            let reachable_from_concurrent = self
                .callgraph
                .reachable_from_roots(concurrent_roots.into_iter());
            reachable.extend(reachable_from_concurrent);
        }

        Some(reachable)
    }

    fn should_ignore_function(func_name: &str) -> bool {
        const IGNORED_SUBSTRINGS: &[&str] = &[
            "::serialize",
            "::serialize_",
            "::deserialize",
            "::deserialize_",
            "::serde",
            "::serde_json",
            "::serde_yaml",
            "::serde_with",
            "::__serde",
            "::__private",
            "::Serializer::",
            "::Deserializer::",
            "::Serialize::",
            "::Deserialize::",
            "::visit_",
            "::Visitor::visit",
            "::fmt::",
            "::Debug::fmt",
            "::core::fmt",
            "::alloc::fmt",
            "::tests::",
            "::test::",
            "::bench",
        ];

        IGNORED_SUBSTRINGS
            .iter()
            .any(|pattern| func_name.contains(pattern))
    }

    fn create_function_places(
        &mut self,
        func_name: String,
        with_token: bool,
    ) -> (PlaceId, PlaceId) {
        let start = if with_token {
            Place::new(
                format!("{}_start", func_name),
                1,
                1,
                PlaceType::FunctionStart,
                String::default(),
            )
        } else {
            Place::new(
                format!("{}_start", func_name),
                0,
                1,
                PlaceType::FunctionStart,
                String::default(),
            )
        };
        let end = Place::new(
            format!("{}_end", func_name),
            0,
            1,
            PlaceType::FunctionEnd,
            String::default(),
        );

        let start_id = self.net.add_place(start);
        let end_id = self.net.add_place(end);

        (start_id, end_id)
    }

    pub fn construct_lock_with_dfs(&mut self) {
        let (lockguards, lock_objects) = self.collect_blocking_primitives();
        if lockguards.is_empty() {
            log::debug!("Not Found Lockguards In This Crate");
            return;
        }

        let mut info = FxHashMap::default();

        for (_, map) in lockguards.into_iter() {
            info.extend(map);
        }

        let mut union_find: FxHashMap<LockGuardId, LockGuardId> = FxHashMap::default();
        let lockid_vec: Vec<LockGuardId> = info.clone().into_keys().collect();

        for lock_id in &lockid_vec {
            union_find.insert(lock_id.clone(), lock_id.clone());
        }

        // Two guards belong to the same lock resource when the lock objects
        // they protect may alias. We compare the *acquiring receivers* (the
        // `&Mutex` passed to `lock()`), captured by `BlockingCollector`, rather
        // than the guard objects themselves: distinct guards of the same mutex
        // are different objects (so guard aliasing misses them), while their
        // receivers both point at the same lock. When a receiver is unknown we
        // fall back to guard aliasing to stay sound.
        let alias_id_for = |guard: &LockGuardId| -> AliasId {
            lock_objects.get(guard).copied().unwrap_or_else(|| guard.clone().into())
        };

        let policy = self.options.config.alias_unknown_policy;
        for i in 0..lockid_vec.len() {
            for j in i + 1..lockid_vec.len() {
                if self
                    .alias
                    .borrow_mut()
                    .alias(alias_id_for(&lockid_vec[i]), alias_id_for(&lockid_vec[j]))
                    .may_alias(policy)
                {
                    log::debug!(
                        "Locks {:?} and {:?} may alias",
                        lockid_vec[i],
                        lockid_vec[j]
                    );
                    union(&mut union_find, &lockid_vec[i], &lockid_vec[j]);
                }
            }
        }

        let mut temp_groups: FxHashMap<LockGuardId, Vec<LockGuardId>> = FxHashMap::default();
        for lock_id in &lockid_vec {
            let root = find(&union_find, lock_id);
            temp_groups.entry(root).or_default().push(lock_id.clone());
        }

        let mut group_id = 0;
        for group in temp_groups.values() {
            match &info[&group[0]].lockguard_ty {
                LockGuardTy::StdMutex(_)
                | LockGuardTy::ParkingLotMutex(_)
                | LockGuardTy::SpinMutex(_) => {
                    let lock_name = format!("Mutex_{}", group_id);
                    let lock_node =
                        self.create_resource_place(lock_name.clone(), 1, 1, String::default());
                    log::debug!("Creating Mutex node: {}", lock_name);
                    for lock in group {
                        let alias_id = lock.get_alias_id();
                        self.resources.locks_mut().insert(alias_id, lock_node);
                    }
                }
                _ => {
                    let lock_name = format!("RwLock_{}", group_id);
                    let cap = crate::translate::structure::RWLOCK_CAPACITY;
                    let lock_node =
                        self.create_resource_place(lock_name.clone(), cap, cap, String::default());
                    log::debug!("Creating RwLock node: {}", lock_name);
                    for lock in group {
                        let alias_id = lock.get_alias_id();
                        self.resources.locks_mut().insert(alias_id, lock_node);
                    }
                }
            }
            group_id += 1;
        }
        log::debug!("Total lock groups discovered: {}", group_id);
    }

    fn collect_blocking_primitives(
        &mut self,
    ) -> (
        FxHashMap<InstanceId, LockGuardMap<'tcx>>,
        FxHashMap<LockGuardId, AliasId>,
    ) {
        let mut lockguards = FxHashMap::default();
        let mut lock_objects: FxHashMap<LockGuardId, AliasId> = FxHashMap::default();
        let mut condvars = FxHashMap::default();

        for (instance_id, node) in self.callgraph.graph.node_references() {
            let instance = match node {
                CallGraphNode::WithBody(instance) => instance,
                _ => continue,
            };

            if !instance.def_id().is_local() {
                continue;
            }

            let body = self.tcx.instance_mir(instance.def);
            let mut collector = BlockingCollector::new(instance_id, instance, body, self.tcx);
            collector.analyze();

            if !collector.lockguards.is_empty() {
                lockguards.insert(instance_id, collector.lockguards.clone());
                Arc::make_mut(&mut self.lock_info).extend(collector.lockguards);
            }

            lock_objects.extend(collector.lock_objects);

            if !collector.condvars.is_empty() {
                condvars.insert(instance_id, collector.condvars);
            }
        }

        if !condvars.is_empty() {
            for condvar_map in condvars.into_values() {
                for (condvar_id, span) in condvar_map {
                    let condvar_name = format!("Condvar:{}", span);
                    let condvar_node =
                        self.create_resource_place(condvar_name, 1, 1, String::default());
                    let condvar_alias = condvar_id.get_alias_id();
                    self.resources
                        .condvars_mut()
                        .insert(condvar_alias, condvar_node);
                }
            }
        } else {
            log::debug!("Not Found Condvars In This Crate");
        }

        (lockguards, lock_objects)
    }

    pub fn get_or_insert_node(&mut self, def_id: DefId) -> (PlaceId, PlaceId) {
        self.functions.get_or_insert(def_id, || {
            let func_name = self.tcx.def_path_str(def_id);
            let func_start = Place::new(
                format!("{}_start", func_name),
                0,
                1,
                PlaceType::FunctionStart,
                String::default(),
            );
            let func_start_node_id = self.net.add_place(func_start);
            let func_end = Place::new(
                format!("{}_end", func_name),
                0,
                1,
                PlaceType::FunctionEnd,
                String::default(),
            );
            let func_end_node_id = self.net.add_place(func_end);
            (func_start_node_id, func_end_node_id)
        })
    }

    pub fn unsafe_places(&self) -> &FxHashMap<AliasId, PlaceId> {
        self.resources.unsafe_places()
    }

    pub fn channel_places(&self) -> &FxHashMap<AliasId, PlaceId> {
        self.resources.channel_places()
    }
}
