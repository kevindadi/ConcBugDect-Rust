//! Synchronization resources, before entry planning and place construction.
//!
//! One pointer-analysis engine, one MIR walk, one partition. `EntryPlanner`
//! and `PetriNet::construct` only read the plan.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;

use crate::analysis::callgraph::{CallGraph, InstanceId};
use crate::analysis::entry_plan::RootMark;
use crate::analysis::entry_plan::{RootReason, is_local_exported};
use crate::analysis::memory::alias_engine::AliasEngine;
use crate::analysis::sync::group_locks::{
    discover_custom_groups, discover_guard_groups, lock_records_from_sites,
};
use crate::analysis::sync::partition::partition_indices;
use crate::analysis::sync::{
    CollectStats, Harvest, ResourceInputs, SiteKind, SyncSite, harvest_resources,
};

use super::{Collected, RunCtx};

/// One equivalence class. `members` are indices into [`ResourcePlan::sites`].
///
/// Lock classes stay in root-discovery order: that order is what names
/// `Mutex_N` / `RwLock_N`. Atomic and unsafe classes are already ordered by
/// the minimum member index.
#[derive(Clone, Debug)]
pub struct ResourceClass {
    pub kind: ClassKind,
    pub members: Vec<usize>,
}

/// Which binder a class feeds. Custom locks are guard-less methods; they are
/// not a [`SiteKind`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClassKind {
    Lock,
    CustomLock,
    Atomic,
    Unsafe,
}

/// Collected sites, their classes, and the concurrent roots those facts imply.
pub struct ResourcePlan<'tcx> {
    pub sites: Vec<SyncSite<'tcx>>,
    pub classes: Vec<ResourceClass>,
    pub sync_roots: FxHashSet<InstanceId>,
    pub stats: CollectStats,
    /// Guard types and condvar mailboxes from the same walk. Not a second scan.
    pub inputs: ResourceInputs<'tcx>,
    /// Reasons `EntryPlanner` records when it consumes `sync_roots`.
    pub root_marks: Vec<RootMark>,
    /// Bodies loaded by the one resource walk.
    pub mir_loads: usize,
}

/// The engine moves into `PetriNet`. It is not cloned.
pub struct ResourceAnalysis<'tcx> {
    pub plan: ResourcePlan<'tcx>,
    pub alias: AliasEngine<'tcx>,
}

pub fn analyze_resources<'tcx>(
    ctx: &RunCtx<'_, 'tcx>,
    collected: &Collected<'tcx>,
) -> ResourceAnalysis<'tcx> {
    let mut alias = AliasEngine::new(
        ctx.tcx,
        collected.callgraph.instances_by_index(),
        &ctx.options.config,
    );
    let harvest = harvest_resources(
        ctx.tcx,
        &collected.callgraph,
        ctx.options,
        &mut |instance, local| alias.local_built(*instance, local.as_u32()),
    );
    let (classes, discovery_matches_min) =
        classify(&harvest, &collected.callgraph, ctx, &mut alias);
    let (sync_roots, root_marks) = sync_roots_from(&harvest, &collected.callgraph, ctx);
    log::info!(
        "resource-plan: mir_loads={} sites={} classes={} sync_roots={} lock-class-order-matches-min-index={}",
        harvest.mir_loads,
        harvest.sites.len(),
        classes.len(),
        sync_roots.len(),
        discovery_matches_min,
    );
    let plan = ResourcePlan {
        sites: harvest.sites,
        classes,
        sync_roots,
        stats: CollectStats {
            bodies_visited: harvest.mir_loads,
            alias_queries: harvest.alias_queries,
            elapsed_ms: harvest.elapsed_ms,
        },
        inputs: harvest.inputs,
        root_marks,
        mir_loads: harvest.mir_loads,
    };
    ResourceAnalysis { plan, alias }
}

fn classify<'tcx>(
    harvest: &Harvest<'tcx>,
    callgraph: &CallGraph<'tcx>,
    ctx: &RunCtx<'_, 'tcx>,
    alias: &mut AliasEngine<'tcx>,
) -> (Vec<ResourceClass>, bool) {
    let sites = &harvest.sites;
    let (lockguards, lock_objects, custom_sites) =
        lock_records_from_sites(sites, &harvest.inputs.guard_info, callgraph);
    let policy = ctx.options.config.alias_unknown_policy;
    let guard_groups = discover_guard_groups(
        &lockguards,
        &lock_objects,
        alias,
        policy,
        ctx.options.config.resource_lock_grouper,
    );
    let custom_groups = discover_custom_groups(&custom_sites, alias, policy);

    let mut guard_at: FxHashMap<_, usize> = FxHashMap::default();
    for (index, site) in sites.iter().enumerate() {
        if let Some(id) = site.origin.guard() {
            guard_at.insert(id, index);
        }
    }
    let mut classes = Vec::new();
    let mut lock_mins = Vec::new();
    for group in &guard_groups {
        let members: Vec<usize> = group
            .iter()
            .map(|id| {
                *guard_at
                    .get(id)
                    .expect("lock group member was collected as a guard site")
            })
            .collect();
        if let Some(min) = members.iter().copied().min() {
            lock_mins.push(min);
        }
        classes.push(ResourceClass {
            kind: ClassKind::Lock,
            members,
        });
    }
    let mut sorted_mins = lock_mins.clone();
    sorted_mins.sort_unstable();
    let discovery_matches_min = lock_mins == sorted_mins;

    let mut custom_at: FxHashMap<InstanceId, usize> = FxHashMap::default();
    for (index, site) in sites.iter().enumerate() {
        if site.origin.custom().is_some() {
            custom_at.insert(site.instance, index);
        }
    }
    for group in &custom_groups {
        let members: Vec<usize> = group
            .iter()
            .map(|&index| {
                let instance = custom_sites[index].instance_id;
                *custom_at
                    .get(&instance)
                    .expect("custom group member was collected as a site")
            })
            .collect();
        classes.push(ResourceClass {
            kind: ClassKind::CustomLock,
            members,
        });
    }

    classes.extend(kind_classes(
        sites,
        SiteKind::Atomic,
        ClassKind::Atomic,
        alias,
        policy,
    ));
    classes.extend(kind_classes(
        sites,
        SiteKind::Unsafe,
        ClassKind::Unsafe,
        alias,
        policy,
    ));
    (classes, discovery_matches_min)
}

fn kind_classes<'tcx>(
    sites: &[SyncSite<'tcx>],
    kind: SiteKind,
    class_kind: ClassKind,
    alias: &mut AliasEngine<'tcx>,
    policy: crate::config::AliasUnknownPolicy,
) -> Vec<ResourceClass> {
    let at: Vec<usize> = sites
        .iter()
        .enumerate()
        .filter(|(_, site)| site.kind == kind)
        .map(|(index, _)| index)
        .collect();
    if at.is_empty() {
        return Vec::new();
    }
    let subset: Vec<SyncSite<'tcx>> = at.iter().map(|&index| sites[index].clone()).collect();
    partition_indices(&subset, alias, policy)
        .into_iter()
        .map(|group| ResourceClass {
            kind: class_kind,
            members: group.into_iter().map(|index| at[index]).collect(),
        })
        .collect()
}

/// The old `concurrent_roots` set, from the harvest.
///
/// Local guards and condvars, every custom-lock method (including wrappers),
/// and atomic instances that passed the pointer-analysis filter. Unsafe sites
/// are not roots.
fn sync_roots_from<'tcx>(
    harvest: &Harvest<'tcx>,
    callgraph: &CallGraph<'tcx>,
    ctx: &RunCtx<'_, 'tcx>,
) -> (FxHashSet<InstanceId>, Vec<RootMark>) {
    let tcx = ctx.tcx;
    let mut roots = FxHashSet::default();
    let mut marks = Vec::new();
    let mut guard_instances = FxHashSet::default();
    for id in harvest.inputs.guard_info.keys() {
        guard_instances.insert(id.instance_id);
    }
    let mut condvar_instances = FxHashSet::default();
    for id in harvest.inputs.condvars.keys() {
        condvar_instances.insert(*id);
    }

    for instance_id in guard_instances {
        let Some(def_id) = local_def(callgraph, instance_id) else {
            continue;
        };
        note(
            &mut roots,
            &mut marks,
            instance_id,
            RootReason::Lockguard,
            is_private(tcx, def_id),
        );
    }
    for instance_id in condvar_instances {
        let Some(def_id) = local_def(callgraph, instance_id) else {
            continue;
        };
        note(
            &mut roots,
            &mut marks,
            instance_id,
            RootReason::Condvar,
            is_private(tcx, def_id),
        );
    }
    for instance_id in &harvest.custom_roots {
        let def_id = callgraph
            .index_to_instance(*instance_id)
            .map(|node| node.instance().def_id());
        let private = def_id.map(|id| is_private(tcx, id)).unwrap_or(true);
        note(
            &mut roots,
            &mut marks,
            *instance_id,
            RootReason::CustomLock,
            private,
        );
    }
    let mut seen_atomic = FxHashSet::default();
    for instance_id in &harvest.atomic_roots {
        if !seen_atomic.insert(*instance_id) {
            continue;
        }
        let private = callgraph
            .index_to_instance(*instance_id)
            .map(|node| is_private(tcx, node.instance().def_id()))
            .unwrap_or(true);
        note(
            &mut roots,
            &mut marks,
            *instance_id,
            RootReason::Atomic,
            private,
        );
    }
    (roots, marks)
}

fn local_def<'tcx>(callgraph: &CallGraph<'tcx>, instance_id: InstanceId) -> Option<DefId> {
    let def_id = callgraph
        .index_to_instance(instance_id)?
        .instance()
        .def_id();
    def_id.is_local().then_some(def_id)
}

fn is_private(tcx: rustc_middle::ty::TyCtxt<'_>, def_id: DefId) -> bool {
    !is_local_exported(tcx, def_id)
}

fn note(
    roots: &mut FxHashSet<InstanceId>,
    marks: &mut Vec<RootMark>,
    instance: InstanceId,
    reason: RootReason,
    is_private: bool,
) {
    roots.insert(instance);
    marks.push(RootMark {
        instance,
        reason,
        is_private,
    });
}
