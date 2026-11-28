//! One walk over call-graph bodies. Each extractor sees a body at most once.
//!
//! Lock places still come from the guard map recorded on that walk. `SyncSite`
//! does not store read-versus-write guard types, so the binder cannot be
//! rebuilt from sites alone.

use std::cell::RefCell;

use petgraph::visit::IntoNodeReferences;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, Local, TerminatorKind};
use rustc_middle::ty::{Instance, TyCtxt};

use crate::analysis::callgraph::{CallGraph, CallGraphNode, InstanceId};
use crate::analysis::memory::ownership::{
    CustomLockMethod, CustomLockMode, CustomLockOp, custom_lock_method,
};
use crate::analysis::memory::pointsto::AliasId;
use crate::analysis::memory::unsafe_memory::{UnsafeData, UnsafeInfo};
use crate::analysis::primitives::atomic::{AtomicApi, AtomicCollector};
use crate::analysis::primitives::blocking::{
    BlockingCollector, CondvarMap, LockGuardId, LockGuardInfo,
};
use crate::options::Options;
use crate::util::format_name;

use super::collect::{CollectStats, condvar_ty, guard_class, span_string};
use super::ty::normalized_local_ty;
use super::{SiteKind, SiteOrigin, SiteRole, SyncSite};

/// Shared inputs for one collection. `local_built` runs while atomic sites
/// are filtered, after every body has been offered.
pub struct CollectCtx<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub options: &'a Options,
    pub crate_name: String,
    local_built: RefCell<&'a mut dyn FnMut(&Instance<'tcx>, Local) -> bool>,
}

impl<'a, 'tcx> CollectCtx<'a, 'tcx> {
    fn alias_built(&self, instance: &Instance<'tcx>, local: Local) -> bool {
        (self.local_built.borrow_mut())(instance, local)
    }
}

/// Per-body extractor. `finish` yields sites only; lock and custom-lock
/// records stay on the concrete extractor until the walk ends.
pub trait SiteExtractor<'tcx> {
    fn visit_body(
        &mut self,
        ctx: &CollectCtx<'_, 'tcx>,
        instance_id: InstanceId,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    );
    fn finish(self) -> Vec<SyncSite<'tcx>>;
}

/// Facts recorded while the guard site is built. `SyncSite` does not store
/// read-versus-write, so lowering looks the guard type up by [`LockGuardId`].
/// This is not a second walk.
pub struct ResourceInputs<'tcx> {
    pub guard_info: FxHashMap<LockGuardId, LockGuardInfo<'tcx>>,
    pub condvars: FxHashMap<InstanceId, CondvarMap<'tcx>>,
}

struct BlockingExtract<'tcx> {
    guard_info: FxHashMap<LockGuardId, LockGuardInfo<'tcx>>,
    condvars: FxHashMap<InstanceId, CondvarMap<'tcx>>,
    sites: Vec<SyncSite<'tcx>>,
    bodies_visited: usize,
}

struct CustomCandidate<'tcx> {
    instance_id: InstanceId,
    instance: Instance<'tcx>,
    receiver: Local,
    method: CustomLockMethod,
    def_id: DefId,
    name: String,
    callees: Vec<DefId>,
}

struct CustomExtract<'tcx> {
    candidates: Vec<CustomCandidate<'tcx>>,
    /// Every recognized custom-lock method, including delegating wrappers.
    /// Wrappers are not sites, but they are concurrent roots.
    roots: Vec<InstanceId>,
    bodies_visited: usize,
}

struct AtomicExtract<'tcx> {
    collector: AtomicCollector<'tcx>,
}

struct UnsafeExtract {
    places: UnsafeData,
    bodies_visited: usize,
}

impl<'tcx> BlockingExtract<'tcx> {
    fn new() -> Self {
        Self {
            guard_info: FxHashMap::default(),
            condvars: FxHashMap::default(),
            sites: Vec::new(),
            bodies_visited: 0,
        }
    }
}

impl<'tcx> SiteExtractor<'tcx> for BlockingExtract<'tcx> {
    fn visit_body(
        &mut self,
        ctx: &CollectCtx<'_, 'tcx>,
        instance_id: InstanceId,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) {
        if !instance.def_id().is_local()
            && !ctx
                .options
                .cross_crate_matches(&format_name(instance.def_id()))
        {
            return;
        }
        self.bodies_visited += 1;
        let mut collector = BlockingCollector::new(
            instance_id,
            &instance,
            body,
            ctx.tcx,
            ctx.options.config.condvar_model,
        );
        collector.analyze();

        if !collector.condvars.is_empty() {
            self.condvars
                .insert(instance_id, collector.condvars.clone());
        }

        for (guard_id, info) in &collector.lockguards {
            self.guard_info.insert(*guard_id, info.clone());
            let (kind, protected) = guard_class(&info.lockguard_ty);
            let object = collector
                .lock_objects
                .get(guard_id)
                .copied()
                .unwrap_or_else(|| AliasId::from(*guard_id));
            self.sites.push(SyncSite {
                instance: instance_id,
                local: guard_id.local,
                kind,
                ty: protected,
                role: SiteRole::Acquire,
                span: span_string(info.span),
                object,
                origin: SiteOrigin::Guard(*guard_id),
                atomic_order: None,
            });
        }
        for (condvar_id, span) in &collector.condvars {
            let Some(ty) = condvar_ty(ctx.tcx, instance, body, *condvar_id) else {
                continue;
            };
            self.sites.push(SyncSite {
                instance: instance_id,
                local: condvar_id.local,
                kind: SiteKind::Condvar,
                ty,
                role: SiteRole::Access,
                span: span.clone(),
                object: AliasId::from(*condvar_id),
                origin: SiteOrigin::Condvar(*condvar_id),
                atomic_order: None,
            });
        }
    }

    fn finish(self) -> Vec<SyncSite<'tcx>> {
        self.sites
    }
}

impl<'tcx> CustomExtract<'tcx> {
    fn new() -> Self {
        Self {
            candidates: Vec::new(),
            roots: Vec::new(),
            bodies_visited: 0,
        }
    }

    fn finish_sites(self, ctx: &CollectCtx<'_, 'tcx>) -> (Vec<SyncSite<'tcx>>, Vec<InstanceId>) {
        let roots = self.roots;
        if self.candidates.is_empty() {
            return (Vec::new(), roots);
        }
        let mut by_def = FxHashMap::default();
        for site in &self.candidates {
            by_def.insert(site.def_id, site.method.op);
        }
        let mut kept = Vec::new();
        for site in self.candidates {
            let delegates = site
                .callees
                .iter()
                .any(|callee| by_def.get(callee).copied() == Some(site.method.op));
            if !delegates {
                kept.push(site);
            }
        }
        kept.sort_by(|a, b| {
            a.name
                .cmp(&b.name)
                .then_with(|| a.receiver.as_u32().cmp(&b.receiver.as_u32()))
        });
        let mut sites = Vec::new();
        for site in kept {
            let body = ctx.tcx.instance_mir(site.instance.def);
            let ty = normalized_local_ty(ctx.tcx, site.instance, body, site.receiver);
            let kind = match site.method.mode {
                CustomLockMode::Mutex => SiteKind::Mutex,
                CustomLockMode::RwLockRead | CustomLockMode::RwLockWrite => SiteKind::RwLock,
            };
            let role = match site.method.op {
                CustomLockOp::Acquire => SiteRole::Acquire,
                CustomLockOp::Release => SiteRole::Release,
            };
            let span = body.local_decls[site.receiver].source_info.span;
            sites.push(SyncSite {
                instance: site.instance_id,
                local: site.receiver,
                kind,
                ty,
                role,
                span: span_string(span),
                object: AliasId::new(site.instance_id, site.receiver),
                origin: SiteOrigin::Custom {
                    mode: site.method.mode,
                    op: site.method.op,
                },
                atomic_order: None,
            });
        }
        (sites, roots)
    }
}

impl<'tcx> SiteExtractor<'tcx> for CustomExtract<'tcx> {
    fn visit_body(
        &mut self,
        ctx: &CollectCtx<'_, 'tcx>,
        instance_id: InstanceId,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) {
        let def_id = instance.def_id();
        let name = format_name(def_id);
        if !ctx.tcx.is_mir_available(def_id) || !ctx.options.crate_filter_match(&name) {
            return;
        }
        self.bodies_visited += 1;
        let Some(method) =
            custom_lock_method(def_id, ctx.tcx, &ctx.options.config.custom_lock_types)
        else {
            return;
        };
        // A delegating wrapper and a promoted body are still roots. Only a
        // non-delegating method with a receiver becomes a site.
        self.roots.push(instance_id);
        if body.source.promoted.is_some() {
            return;
        }
        let Some(receiver) = body.args_iter().next() else {
            return;
        };
        let mut callees = Vec::new();
        for data in body.basic_blocks.iter() {
            let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                continue;
            };
            if let rustc_middle::ty::TyKind::FnDef(callee, _) = func.ty(body, ctx.tcx).kind() {
                callees.push(*callee);
            }
        }
        self.candidates.push(CustomCandidate {
            instance_id,
            instance,
            receiver,
            method,
            def_id,
            name,
            callees,
        });
    }

    fn finish(self) -> Vec<SyncSite<'tcx>> {
        Vec::new()
    }
}

impl<'tcx> AtomicExtract<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, callgraph: &CallGraph<'tcx>, crate_name: String) -> Self {
        Self {
            collector: {
                let (forward, back) = callgraph.instance_maps();
                AtomicCollector::new(tcx, crate_name, forward, back)
            },
        }
    }

    fn finish_sites(
        mut self,
        ctx: &CollectCtx<'_, 'tcx>,
        callgraph: &CallGraph<'tcx>,
    ) -> (Vec<SyncSite<'tcx>>, CollectStats, Vec<InstanceId>) {
        let started_bodies = self.collector.bodies_visited;
        self.collector
            .finish_alias_filter(&mut |instance, local| ctx.alias_built(instance, local));
        let atomic_roots: Vec<InstanceId> = self
            .collector
            .atomic_vars
            .values()
            .map(|info| info.instance_id)
            .collect();
        let tcx = ctx.tcx;
        let mut sites = Vec::new();
        for info in self.collector.atomic_vars.values() {
            let Some(node) = callgraph.index_to_instance(info.instance_id) else {
                continue;
            };
            let instance = *node.instance();
            if !tcx.is_mir_available(instance.def_id()) {
                continue;
            }
            let body = tcx.instance_mir(instance.def);
            let Some(_) = body.local_decls.get(info.local_id) else {
                continue;
            };
            let ty = normalized_local_ty(tcx, instance, body, info.local_id);
            let role = match info.operations.first().map(|op| op.api) {
                Some(AtomicApi::Read) => SiteRole::Load,
                Some(AtomicApi::Write) => SiteRole::Store,
                Some(AtomicApi::ReadWrite) => SiteRole::Rmw,
                None => SiteRole::Access,
            };
            let order = info.operations.first().map(|op| op.ordering);
            let alias = info.get_alias_id();
            sites.push(SyncSite {
                instance: info.instance_id,
                local: info.local_id,
                kind: SiteKind::Atomic,
                ty,
                role,
                span: info.span.clone(),
                object: alias,
                origin: SiteOrigin::Alias(alias),
                atomic_order: order,
            });
        }
        (
            sites,
            CollectStats {
                bodies_visited: started_bodies,
                alias_queries: self.collector.alias_queries,
                elapsed_ms: 0,
            },
            atomic_roots,
        )
    }
}

impl<'tcx> SiteExtractor<'tcx> for AtomicExtract<'tcx> {
    fn visit_body(
        &mut self,
        ctx: &CollectCtx<'_, 'tcx>,
        _instance_id: InstanceId,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) {
        self.collector.visit_body(ctx.options, &instance, body);
    }

    fn finish(self) -> Vec<SyncSite<'tcx>> {
        Vec::new()
    }
}

impl UnsafeExtract {
    fn new() -> Self {
        Self {
            places: UnsafeData::default(),
            bodies_visited: 0,
        }
    }
}

impl<'tcx> SiteExtractor<'tcx> for UnsafeExtract {
    fn visit_body(
        &mut self,
        ctx: &CollectCtx<'_, 'tcx>,
        instance_id: InstanceId,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) {
        let def_id = instance.def_id();
        if !(def_id.is_local()
            && format_name(def_id).starts_with(&ctx.crate_name)
            && ctx.tcx.is_mir_available(def_id))
        {
            return;
        }
        self.bodies_visited += 1;
        let (data, _) = UnsafeInfo::collect(instance, Some(instance_id), body, ctx.tcx);
        self.places.unsafe_places.extend(data.unsafe_places);
    }

    fn finish(self) -> Vec<SyncSite<'tcx>> {
        Vec::new()
    }
}

impl UnsafeExtract {
    fn into_sites<'tcx>(
        self,
        ctx: &CollectCtx<'_, 'tcx>,
        callgraph: &CallGraph<'tcx>,
    ) -> (Vec<SyncSite<'tcx>>, usize) {
        let bodies = self.bodies_visited;
        let mut sites = Vec::new();
        for (alias, span) in self.places.unsafe_places {
            let Some(node) = callgraph.index_to_instance(alias.instance_id) else {
                continue;
            };
            let instance = *node.instance();
            if !ctx.tcx.is_mir_available(instance.def_id()) {
                continue;
            }
            let body = ctx.tcx.instance_mir(instance.def);
            let Some(_) = body.local_decls.get(alias.local) else {
                continue;
            };
            let ty = normalized_local_ty(ctx.tcx, instance, body, alias.local);
            sites.push(SyncSite {
                instance: alias.instance_id,
                local: alias.local,
                kind: SiteKind::Unsafe,
                ty,
                role: SiteRole::Access,
                span,
                object: alias,
                origin: SiteOrigin::Alias(alias),
                atomic_order: None,
            });
        }
        (sites, bodies)
    }
}

/// Sites plus the root facts the same walk already proved.
pub struct Harvest<'tcx> {
    pub sites: Vec<SyncSite<'tcx>>,
    pub inputs: ResourceInputs<'tcx>,
    /// Custom-lock methods, including delegating wrappers that are not sites.
    pub custom_roots: Vec<InstanceId>,
    /// Atomic instances that survived the pointer-analysis filter.
    pub atomic_roots: Vec<InstanceId>,
    /// Bodies loaded once, whichever extractors wanted them.
    pub mir_loads: usize,
    pub alias_queries: usize,
    pub elapsed_ms: u128,
}

/// Walk each body once and run whichever extractors apply to it.
pub(crate) fn harvest_resources<'tcx>(
    tcx: TyCtxt<'tcx>,
    callgraph: &CallGraph<'tcx>,
    options: &Options,
    local_built: &mut dyn FnMut(&Instance<'tcx>, Local) -> bool,
) -> Harvest<'tcx> {
    let started = std::time::Instant::now();
    let ctx = CollectCtx {
        tcx,
        options,
        crate_name: options.crate_name.clone(),
        local_built: RefCell::new(local_built),
    };
    let mut blocking = BlockingExtract::new();
    let mut custom = CustomExtract::new();
    let mut atomic = AtomicExtract::new(tcx, callgraph, options.crate_name.clone());
    let mut unsafe_extract = UnsafeExtract::new();
    let mut blocking_ms = 0u128;
    let mut custom_ms = 0u128;
    let mut atomic_ms = 0u128;
    let mut unsafe_ms = 0u128;
    let mut mir_loads = 0usize;

    for (instance_id, node) in callgraph.graph.node_references() {
        let CallGraphNode::WithBody(instance) = node else {
            continue;
        };
        let def_id = instance.def_id();
        let name = format_name(def_id);
        let local = def_id.is_local();
        let cross = options.cross_crate_matches(&name);
        let mir_ok = tcx.is_mir_available(def_id);
        let blocking_wants = local || cross;
        let custom_wants = mir_ok && options.crate_filter_match(&name);
        let atomic_wants = mir_ok
            && crate::analysis::primitives::atomic::atomic_scan_in_scope(
                local,
                &name,
                &options.crate_name,
                options,
            );
        let unsafe_wants = local && mir_ok && name.starts_with(&options.crate_name);
        if !(blocking_wants || custom_wants || atomic_wants || unsafe_wants) {
            continue;
        }
        let body = tcx.instance_mir(instance.def);
        mir_loads += 1;
        let instance = *instance;
        if blocking_wants {
            let step = std::time::Instant::now();
            blocking.visit_body(&ctx, instance_id, instance, body);
            blocking_ms += step.elapsed().as_millis();
        }
        if custom_wants {
            let step = std::time::Instant::now();
            custom.visit_body(&ctx, instance_id, instance, body);
            custom_ms += step.elapsed().as_millis();
        }
        if atomic_wants {
            let step = std::time::Instant::now();
            atomic.visit_body(&ctx, instance_id, instance, body);
            atomic_ms += step.elapsed().as_millis();
        }
        if unsafe_wants {
            let step = std::time::Instant::now();
            unsafe_extract.visit_body(&ctx, instance_id, instance, body);
            unsafe_ms += step.elapsed().as_millis();
        }
    }

    let blocking_bodies = blocking.bodies_visited;
    let custom_bodies = custom.bodies_visited;
    let custom_finish = std::time::Instant::now();
    let (custom_sync_sites, custom_roots) = custom.finish_sites(&ctx);
    custom_ms += custom_finish.elapsed().as_millis();
    let guard_info = std::mem::take(&mut blocking.guard_info);
    let condvars = std::mem::take(&mut blocking.condvars);
    let mut sites = SiteExtractor::finish(blocking);
    let atomic_finish = std::time::Instant::now();
    let (atomic_sites, atomic_stats, atomic_roots) = atomic.finish_sites(&ctx, callgraph);
    atomic_ms += atomic_finish.elapsed().as_millis();
    let (unsafe_sites, unsafe_bodies) = unsafe_extract.into_sites(&ctx, callgraph);
    sites.extend(custom_sync_sites);
    sites.extend(atomic_sites);
    sites.extend(unsafe_sites);
    let elapsed_ms = started.elapsed().as_millis();
    log::info!(
        "resource-collect: blocking bodies={blocking_bodies} {blocking_ms}ms, atomic bodies={} {atomic_ms}ms, unsafe bodies={unsafe_bodies} {unsafe_ms}ms, custom bodies={custom_bodies} {custom_ms}ms",
        atomic_stats.bodies_visited,
    );
    log::info!(
        "resource-collect-alias: blocking=0, atomic={}, unsafe=0, custom=0",
        atomic_stats.alias_queries,
    );
    Harvest {
        sites,
        inputs: ResourceInputs {
            guard_info,
            condvars,
        },
        custom_roots,
        atomic_roots,
        mir_loads,
        alias_queries: atomic_stats.alias_queries,
        elapsed_ms,
    }
}
