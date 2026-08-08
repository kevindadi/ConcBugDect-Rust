extern crate rustc_data_structures;
extern crate rustc_span;

use rustc_middle::ty::{EarlyBinder, TyKind, TypingEnv};

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::{Body, Local, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::{self, Instance, TyCtxt};
use rustc_span::Span;

use crate::memory::ownership;
use crate::memory::pointsto::AliasId;
use crate::translate::callgraph::InstanceId;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LockGuardId {
    pub instance_id: InstanceId,
    pub local: Local,
}

impl LockGuardId {
    pub fn new(instance_id: InstanceId, local: Local) -> Self {
        Self { instance_id, local }
    }

    pub fn get_alias_id(&self) -> AliasId {
        AliasId::new(self.instance_id, self.local)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CondVarId {
    pub instance_id: InstanceId,
    pub local: Local,
}

impl CondVarId {
    pub fn new(instance_id: InstanceId, local: Local) -> Self {
        Self { instance_id, local }
    }

    pub fn get_alias_id(&self) -> AliasId {
        AliasId::new(self.instance_id, self.local)
    }
}

pub type CondvarMap<'tcx> = FxHashMap<CondVarId, String>;

#[derive(Clone, Debug)]
pub enum LockGuardTy<'tcx> {
    StdMutex(ty::Ty<'tcx>),
    ParkingLotMutex(ty::Ty<'tcx>),
    SpinMutex(ty::Ty<'tcx>),
    StdRwLockRead(ty::Ty<'tcx>),
    StdRwLockWrite(ty::Ty<'tcx>),
    ParkingLotRead(ty::Ty<'tcx>),
    ParkingLotWrite(ty::Ty<'tcx>),
    SpinRead(ty::Ty<'tcx>),
    SpinWrite(ty::Ty<'tcx>),
}

use crate::util::has_pn_attribute;

impl<'tcx> LockGuardTy<'tcx> {
    pub fn from_local_ty(local_ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Self> {
        if let ty::TyKind::Adt(adt_def, substs) = local_ty.kind() {
            let def_id = adt_def.did();
            // Check for attributes first
            if has_pn_attribute(tcx, def_id, "pn_mutex_guard") {
                if let Some(inner) = substs.types().next() {
                    return Some(LockGuardTy::StdMutex(inner));
                }
            }
            if has_pn_attribute(tcx, def_id, "pn_rwlock_read_guard") {
                if let Some(inner) = substs.types().next() {
                    return Some(LockGuardTy::StdRwLockRead(inner));
                }
            }
            if has_pn_attribute(tcx, def_id, "pn_rwlock_write_guard") {
                if let Some(inner) = substs.types().next() {
                    return Some(LockGuardTy::StdRwLockWrite(inner));
                }
            }

            let path = tcx.def_path_str(def_id);

            if !path.contains("MutexGuard")
                && !path.contains("RwLockReadGuard")
                && !path.contains("RwLockWriteGuard")
            {
                return None;
            }
            let first_part = path.split('<').next()?;
            if first_part.contains("MutexGuard") {
                if first_part.contains("async")
                    || first_part.contains("tokio")
                    || first_part.contains("future")
                    || first_part.contains("loom")
                {
                    None
                } else if first_part.contains("spin") {
                    Some(LockGuardTy::SpinMutex(substs.types().next()?))
                } else if first_part.contains("lock_api") || first_part.contains("parking_lot") {
                    Some(LockGuardTy::ParkingLotMutex(substs.types().nth(1)?))
                } else {
                    Some(LockGuardTy::StdMutex(substs.types().next()?))
                }
            } else if first_part.contains("RwLockReadGuard") {
                if first_part.contains("async")
                    || first_part.contains("tokio")
                    || first_part.contains("future")
                    || first_part.contains("loom")
                {
                    None
                } else if first_part.contains("spin") {
                    Some(LockGuardTy::SpinRead(substs.types().next()?))
                } else if first_part.contains("lock_api") || first_part.contains("parking_lot") {
                    Some(LockGuardTy::ParkingLotRead(substs.types().nth(1)?))
                } else {
                    Some(LockGuardTy::StdRwLockRead(substs.types().next()?))
                }
            } else if first_part.contains("RwLockWriteGuard") {
                if first_part.contains("async")
                    || first_part.contains("tokio")
                    || first_part.contains("future")
                    || first_part.contains("loom")
                {
                    None
                } else if first_part.contains("spin") {
                    Some(LockGuardTy::SpinWrite(substs.types().next()?))
                } else if first_part.contains("lock_api") || first_part.contains("parking_lot") {
                    Some(LockGuardTy::ParkingLotWrite(substs.types().nth(1)?))
                } else {
                    Some(LockGuardTy::StdRwLockWrite(substs.types().next()?))
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub struct LockGuardInfo<'tcx> {
    pub lockguard_ty: LockGuardTy<'tcx>,
    pub span: Span,
}

impl<'tcx> LockGuardInfo<'tcx> {
    pub fn new(lockguard_ty: LockGuardTy<'tcx>, span: Span) -> Self {
        Self { lockguard_ty, span }
    }
}

pub type LockGuardMap<'tcx> = FxHashMap<LockGuardId, LockGuardInfo<'tcx>>;

/// How a local obtained its value, used to trace a lock guard back to the
/// receiver of its acquiring `lock()/read()/write()` call.
#[derive(Clone, Debug)]
enum DefSource<'tcx> {
    /// `dest = lock(receiver, ..)` — records the receiver place (local + optional field).
    LockAcquire { local: Local, field: Option<u32> },
    /// `dest = move/copy src` — stores the full source place (local + projection).
    Forward {
        local: Local,
        projection: Vec<
            rustc_middle::mir::ProjectionElem<rustc_middle::mir::Local, rustc_middle::ty::Ty<'tcx>>,
        >,
    },
    /// `dest = &borrow(place)` — records the base local and field of the borrowed place.
    /// Used to recover field info from expressions like `_4 = &((*_1).0: Mutex<bool>)`.
    Borrow { base: Local, field: Option<u32> },
}

impl<'tcx> PartialEq for DefSource<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (DefSource::Forward { local: la, .. }, DefSource::Forward { local: lb, .. }) => {
                la == lb
            }
            (
                DefSource::LockAcquire {
                    local: la,
                    field: fa,
                },
                DefSource::LockAcquire {
                    local: lb,
                    field: fb,
                },
            ) => la == lb && fa == fb,
            (
                DefSource::Borrow {
                    base: ba,
                    field: fa,
                },
                DefSource::Borrow {
                    base: bb,
                    field: fb,
                },
            ) => ba == bb && fa == fb,
            _ => false,
        }
    }
}

impl<'tcx> Eq for DefSource<'tcx> {}

impl<'tcx> std::hash::Hash for DefSource<'tcx> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            DefSource::Forward { local, .. } => {
                0u8.hash(state);
                local.hash(state);
            }
            DefSource::LockAcquire { local, field } => {
                1u8.hash(state);
                local.hash(state);
                field.hash(state);
            }
            DefSource::Borrow { base, field } => {
                2u8.hash(state);
                base.hash(state);
                field.hash(state);
            }
        }
    }
}

pub struct BlockingCollector<'a, 'b, 'tcx> {
    instance_id: InstanceId,
    instance: &'a Instance<'tcx>,
    body: &'b Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    pub lockguards: LockGuardMap<'tcx>,
    pub condvars: CondvarMap<'tcx>,
    /// Maps each lock guard to the alias id of the lock object it guards (the
    /// receiver of the acquiring call). Used to group guards by the *lock they
    /// protect* rather than by guard-pointer aliasing.
    pub lock_objects: FxHashMap<LockGuardId, AliasId>,
}

impl<'a, 'b, 'tcx> BlockingCollector<'a, 'b, 'tcx> {
    pub fn new(
        instance_id: InstanceId,
        instance: &'a Instance<'tcx>,
        body: &'b Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Self {
            instance_id,
            instance,
            body,
            tcx,
            lockguards: Default::default(),
            condvars: Default::default(),
            lock_objects: Default::default(),
        }
    }

    pub fn analyze(&mut self) {
        for (local, local_decl) in self.body.local_decls.iter_enumerated() {
            let typing_env = TypingEnv::post_analysis(self.tcx, self.instance.def_id());
            let local_ty = self.instance.instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                typing_env,
                EarlyBinder::bind(local_decl.ty),
            );
            if let Some(lockguard_ty) = LockGuardTy::from_local_ty(local_ty, self.tcx) {
                let lockguard_id = LockGuardId::new(self.instance_id, local);
                let lockguard_info = LockGuardInfo::new(lockguard_ty, local_decl.source_info.span);
                self.lockguards.insert(lockguard_id, lockguard_info);
            }

            if let TyKind::Adt(adt_def, _) = local_ty.kind() {
                let def_id = adt_def.did();
                if has_pn_attribute(self.tcx, def_id, "pn_condvar") {
                    log::warn!(
                        "[condvar-detect] attr match: instance={:?} local={:?} ty={} path={} span={:?}",
                        self.instance.def_id(),
                        local,
                        local_ty,
                        self.tcx.def_path_str(def_id),
                        local_decl.source_info.span,
                    );
                    self.condvars.insert(
                        CondVarId::new(self.instance_id, local),
                        format!("{:?}", local_decl.source_info.span),
                    );
                } else {
                    let path = self.tcx.def_path_str(def_id);
                    if path.starts_with("std::sync::Condvar") {
                        log::warn!(
                            "[condvar-detect] std match: instance={:?} local={:?} ty={} path={} span={:?}",
                            self.instance.def_id(),
                            local,
                            local_ty,
                            path,
                            local_decl.source_info.span,
                        );
                        self.condvars.insert(
                            CondVarId::new(self.instance_id, local),
                            format!("{:?}", local_decl.source_info.span),
                        );
                    }
                }
            }
        }

        self.resolve_lock_objects();
    }

    /// For every collected guard, walk backward through moves, smart-pointer
    /// derefs, and `Result`/`Option` extractors to the acquiring `lock()` call
    /// and record the receiver (the lock object). Guards whose receiver cannot be
    /// determined are simply left out — the consumer falls back to guard
    /// aliasing for those, preserving the previous (sound) behavior.
    fn resolve_lock_objects(&mut self) {
        if self.lockguards.is_empty() {
            return;
        }

        let mut def_source: FxHashMap<Local, DefSource<'tcx>> = FxHashMap::default();

        for bb in self.body.basic_blocks.iter() {
            for stmt in &bb.statements {
                if let StatementKind::Assign(boxed) = &stmt.kind {
                    let (place, rvalue) = &**boxed;
                    if !place.projection.is_empty() {
                        continue;
                    }
                    if let Rvalue::Use(Operand::Move(src) | Operand::Copy(src), _) = rvalue {
                        // Store the full source place including projection
                        let proj = src.projection.to_vec();
                        def_source.insert(
                            place.local,
                            DefSource::Forward {
                                local: src.local,
                                projection: proj,
                            },
                        );
                    } else if let Rvalue::Ref(_, _, borrow) = rvalue {
                        // Handle `_4 = &((*_1).0: Mutex<bool>)` style borrows.
                        // Extract base local and field index from the borrowed place.
                        let base = borrow.local;
                        let field = borrow.projection.iter().find_map(|elem| {
                            if let rustc_middle::mir::ProjectionElem::Field(f, _) = elem {
                                Some(f.as_u32())
                            } else {
                                None
                            }
                        });
                        def_source.insert(place.local, DefSource::Borrow { base, field });
                    }
                }
            }

            if let Some(term) = &bb.terminator {
                if let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } = &term.kind
                {
                    if !destination.projection.is_empty() {
                        continue;
                    }
                    let Some((def_id, substs)) = func.const_fn_def() else {
                        continue;
                    };
                    let arg0_place = args.first().and_then(|a| {
                        // Try to get the place with projection from node
                        match &a.node {
                            rustc_middle::mir::Operand::Move(p)
                            | rustc_middle::mir::Operand::Copy(p) => {
                                Some((p.local, p.projection.to_vec()))
                            }
                            _ => None,
                        }
                    });
                    if let Some((local, projection)) = arg0_place {
                        // Check if this is a lock acquire call
                        if ownership::is_lock_acquire(def_id, self.tcx) {
                            // For field accesses like `self.mu.lock()`, the call argument is
                            // often a borrow temporary (`_4`) whose defining `Rvalue::Ref`
                            // carries the actual base local/field. Normalize through that
                            // local first, then fall back to the call-operand projection.
                            let mut receiver_local = local;
                            let mut receiver_field = projection.iter().find_map(|elem| {
                                if let rustc_middle::mir::ProjectionElem::Field(f, _) = elem {
                                    Some(f.as_u32())
                                } else {
                                    None
                                }
                            });
                            if let Some(DefSource::LockAcquire { local, field }) =
                                Self::trace_receiver(&def_source, receiver_local)
                            {
                                receiver_local = local;
                                receiver_field = receiver_field.or(field);
                            }
                            def_source.insert(
                                destination.local,
                                DefSource::LockAcquire {
                                    local: receiver_local,
                                    field: receiver_field,
                                },
                            );
                        } else if ownership::is_wrapper_extract(def_id, self.tcx)
                            || ownership::is_arc_rc_deref(def_id, substs, self.tcx)
                            || self
                                .lockguards
                                .contains_key(&LockGuardId::new(self.instance_id, destination.local))
                        {
                            // `Result::unwrap()`, `Arc/Rc::deref()`, and any other
                            // guard-producing call (e.g. custom `HandyRwLock::rl/wl`
                            // wrappers) do not change which lock object a guard
                            // protects; they only re-express the receiver through a
                            // temporary local, so forward arg0.
                            def_source.insert(
                                destination.local,
                                DefSource::Forward {
                                    local,
                                    projection: projection.to_vec(),
                                },
                            );
                        }
                    }
                }
            }
        }

        let guard_locals: Vec<Local> = self.lockguards.keys().map(|g| g.local).collect();
        for guard_local in guard_locals {
            if let Some(receiver) = Self::trace_receiver(&def_source, guard_local) {
                let guard_id = LockGuardId::new(self.instance_id, guard_local);
                match receiver {
                    DefSource::LockAcquire { local, field } => {
                        let alias_id = AliasId {
                            instance_id: self.instance_id,
                            local,
                            array_index: None,
                            field,
                        };
                        self.lock_objects.insert(guard_id, alias_id);
                    }
                    DefSource::Forward { .. } => {}
                    DefSource::Borrow { .. } => {}
                }
            }
        }
    }

    /// Follow `Forward` edges until a `LockAcquire` or `Borrow`, returning its DefSource.
    /// Combines projections when following Forward chains to preserve field access info.
    /// Bounded by the number of locals to avoid cycles.
    fn trace_receiver<'s>(
        def_source: &'s FxHashMap<Local, DefSource<'tcx>>,
        start: Local,
    ) -> Option<DefSource<'tcx>> {
        let mut current = start;
        let mut accumulated_projection: Vec<
            rustc_middle::mir::ProjectionElem<rustc_middle::mir::Local, rustc_middle::ty::Ty<'tcx>>,
        > = Vec::new();
        for _ in 0..def_source.len().saturating_add(1) {
            match def_source.get(&current)?.clone() {
                DefSource::LockAcquire { local, field } => {
                    // Combine field from receiver with accumulated projection
                    let combined_field = field.or_else(|| {
                        accumulated_projection.iter().find_map(|elem| {
                            if let rustc_middle::mir::ProjectionElem::Field(f, _) = elem {
                                Some(f.as_u32())
                            } else {
                                None
                            }
                        })
                    });
                    return Some(DefSource::LockAcquire {
                        local,
                        field: combined_field,
                    });
                }
                DefSource::Borrow { base, field } => {
                    // Combine field from borrow with accumulated projection
                    let combined_field = field.or_else(|| {
                        accumulated_projection.iter().find_map(|elem| {
                            if let rustc_middle::mir::ProjectionElem::Field(f, _) = elem {
                                Some(f.as_u32())
                            } else {
                                None
                            }
                        })
                    });
                    return Some(DefSource::LockAcquire {
                        local: base,
                        field: combined_field,
                    });
                }
                DefSource::Forward { local, projection } => {
                    // Prepend the projection from this step
                    let mut combined = projection;
                    combined.extend(std::mem::take(&mut accumulated_projection));
                    accumulated_projection = combined;
                    current = local;
                }
            }
        }
        None
    }
}
