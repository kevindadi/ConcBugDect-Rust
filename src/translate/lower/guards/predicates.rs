//! Finds `Mutex<bool>` writes and `while !*g { cv.wait(g) }` loops.
//! It records the blocks and guards; it does not attach the predicate arcs.
//! Arc wiring lives in `wiring`.

use std::collections::VecDeque;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::{TyCtxt, TyKind};

use crate::analysis::api_patterns::KeyApiRegex;
use crate::analysis::callgraph::InstanceId;
use crate::analysis::primitives::blocking::{
    CondvarCallKind, LockGuardId, LockGuardMap, LockGuardTy, parking_lot_condvar_call,
};
use crate::config::CondvarModel;
use crate::util::{format_name, has_spn_attribute};

use super::super::control_flow::compute_back_edges;

/// Recognized `while !*g { cv.wait(g) }` loop structure in a MIR body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoolWaitLoop {
    pub guard_id: LockGuardId,
    pub header_bb: BasicBlock,
    pub switch_bb: BasicBlock,
    /// Target of `SwitchInt(*g)` when `*g == false` (`0`), i.e., `!*g == true` (enters loop body).
    pub loop_body_bb: BasicBlock,
    /// Target of `SwitchInt(*g)` when `*g == true` (`otherwise`), i.e., `!*g == false` (exits loop).
    pub loop_exit_bb: BasicBlock,
    pub wait_bb: BasicBlock,
    pub latch_bb: BasicBlock,
}

/// Whether `ty` is a `MutexGuard<bool>` (`std`, `parking_lot`, or `spin`).
pub fn is_bool_mutex_ty(ty: &LockGuardTy<'_>) -> bool {
    match ty {
        LockGuardTy::StdMutex(inner)
        | LockGuardTy::ParkingLotMutex(inner)
        | LockGuardTy::SpinMutex(inner) => inner.is_bool(),
        _ => false,
    }
}

fn lockguard_id_for_place(instance_id: InstanceId, place: &Place<'_>) -> LockGuardId {
    let field = place.projection.iter().find_map(|elem| {
        if let ProjectionElem::Field(f, _) = elem {
            Some(f.as_u32())
        } else {
            None
        }
    });
    LockGuardId::with_field(instance_id, place.local, field)
}

fn local_reaches_guard(body: &Body<'_>, start: Local, target_guard: Local) -> bool {
    if start == target_guard {
        return true;
    }
    let mut visited: FxHashSet<Local> = FxHashSet::default();
    let mut queue = VecDeque::new();
    visited.insert(start);
    queue.push_back(start);

    while let Some(curr) = queue.pop_front() {
        if curr == target_guard {
            return true;
        }
        for bb in body.basic_blocks.iter() {
            if bb.is_cleanup || bb.is_empty_unreachable() {
                continue;
            }
            for stmt in &bb.statements {
                let StatementKind::Assign(boxed) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**boxed;
                if !dest.projection.is_empty() || dest.local != curr {
                    continue;
                }
                let src_place = match rvalue {
                    Rvalue::Ref(_, _, p) => Some(p),
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p), _) => Some(p),
                    _ => None,
                };
                if let Some(src) = src_place
                    && src.projection.is_empty()
                    && visited.insert(src.local)
                {
                    queue.push_back(src.local);
                }
            }
        }
    }

    false
}

fn rvalue_is_const_true(rvalue: &Rvalue<'_>) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Constant(c), _) => {
            c.const_.try_to_bool() == Some(true) || format!("{:?}", c).contains("true")
        }
        _ => false,
    }
}

/// Find basic blocks in `body` that execute `*g = true` while holding a
/// `Mutex<bool>` guard `g`.
pub fn find_bool_guard_true_writes<'tcx>(
    instance_id: InstanceId,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    lockguards: &LockGuardMap<'tcx>,
) -> Vec<(BasicBlock, LockGuardId)> {
    let bool_guards: Vec<LockGuardId> = lockguards
        .iter()
        .filter_map(|(&gid, info)| {
            (gid.instance_id == instance_id
                && gid.field.is_none()
                && is_bool_mutex_ty(&info.lockguard_ty))
            .then_some(gid)
        })
        .collect();
    if bool_guards.is_empty() {
        return Vec::new();
    }

    let mut deref_mut_to_guard: FxHashMap<Local, LockGuardId> = FxHashMap::default();
    for bb in body.basic_blocks.iter() {
        if bb.is_cleanup || bb.is_empty_unreachable() {
            continue;
        }
        let Some(term) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        else {
            continue;
        };
        let Some(def_id) = (match func.ty(body, tcx).kind() {
            TyKind::FnDef(id, _) | TyKind::Closure(id, _) => Some(*id),
            _ => None,
        }) else {
            continue;
        };
        let callee_name = format_name(def_id);
        if !callee_name.contains("deref_mut") {
            continue;
        }
        if let Some(arg0) = args.first().and_then(|a| a.node.place())
            && arg0.projection.is_empty()
            && destination.projection.is_empty()
            && let Some(&gid) = bool_guards
                .iter()
                .find(|gid| local_reaches_guard(body, arg0.local, gid.local))
        {
            deref_mut_to_guard.insert(destination.local, gid);
        }
    }

    if deref_mut_to_guard.is_empty() {
        return Vec::new();
    }

    let mut writes = Vec::new();
    for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
        if bb.is_cleanup || bb.is_empty_unreachable() {
            continue;
        }
        for stmt in &bb.statements {
            let StatementKind::Assign(boxed) = &stmt.kind else {
                continue;
            };
            let (dest, rvalue) = &**boxed;
            if dest.projection.len() == 1
                && matches!(dest.projection[0], ProjectionElem::Deref)
                && let Some(&gid) = deref_mut_to_guard.get(&dest.local)
                && rvalue_is_const_true(rvalue)
            {
                writes.push((bb_idx, gid));
            }
        }
    }

    writes
}

/// Find single-guard `while !*g { cv.wait(g) }` loops on `Mutex<bool>` guards in `body`.
pub fn find_bool_guard_wait_loops<'tcx>(
    instance_id: InstanceId,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    lockguards: &LockGuardMap<'tcx>,
    key_api_regex: &KeyApiRegex,
) -> Vec<BoolWaitLoop> {
    let mut bool_guards: Vec<LockGuardId> = lockguards
        .iter()
        .filter_map(|(&gid, info)| {
            (gid.instance_id == instance_id
                && gid.field.is_none()
                && is_bool_mutex_ty(&info.lockguard_ty))
            .then_some(gid)
        })
        .collect();
    bool_guards.sort_by_key(|g| g.local.as_u32());
    if bool_guards.is_empty() {
        return Vec::new();
    }

    let back_edges = compute_back_edges(body);
    if back_edges.is_empty() {
        return Vec::new();
    }

    // Identify `header_bb`: calls `Deref::deref(&g)` -> `switch_bb`.
    let mut deref_calls: Vec<(BasicBlock, BasicBlock, Local, LockGuardId)> = Vec::new();
    for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
        if bb.is_cleanup || bb.is_empty_unreachable() {
            continue;
        }
        let Some(term) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target: Some(next_bb),
            ..
        } = &term.kind
        else {
            continue;
        };
        let Some(def_id) = (match func.ty(body, tcx).kind() {
            TyKind::FnDef(id, _) | TyKind::Closure(id, _) => Some(*id),
            _ => None,
        }) else {
            continue;
        };
        let callee_name = format_name(def_id);
        if !callee_name.contains("::deref") || callee_name.contains("deref_mut") {
            continue;
        }
        if let Some(arg0) = args.first().and_then(|a| a.node.place())
            && arg0.projection.is_empty()
            && destination.projection.is_empty()
            && let Some(&gid) = bool_guards
                .iter()
                .find(|gid| local_reaches_guard(body, arg0.local, gid.local))
        {
            deref_calls.push((bb_idx, *next_bb, destination.local, gid));
        }
    }

    let mut loops = Vec::new();
    for (header_bb, switch_bb, ptr_local, guard_id) in deref_calls {
        let bb = &body.basic_blocks[switch_bb];
        if bb.is_cleanup || bb.is_empty_unreachable() {
            continue;
        }

        // `switch_bb` must read `_cond = (*_ptr)` and end with `SwitchInt(_cond)`.
        let mut cond_locals: FxHashSet<Local> = FxHashSet::default();
        for stmt in &bb.statements {
            let StatementKind::Assign(boxed) = &stmt.kind else {
                continue;
            };
            let (dest, rvalue) = &**boxed;
            if !dest.projection.is_empty() {
                continue;
            }
            if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _) = rvalue
                && src.local == ptr_local
                && src.projection.len() == 1
                && matches!(src.projection[0], ProjectionElem::Deref)
            {
                cond_locals.insert(dest.local);
            }
        }
        if cond_locals.is_empty() {
            continue;
        }

        let Some(term) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::SwitchInt { discr, targets } = &term.kind else {
            continue;
        };
        let Some(discr_place) = discr.place() else {
            continue;
        };
        if !discr_place.projection.is_empty() || !cond_locals.contains(&discr_place.local) {
            continue;
        }

        let Some((_, loop_body_bb)) = targets.iter().find(|&(val, _)| val == 0) else {
            continue;
        };
        let loop_exit_bb = targets.otherwise();

        // Single-guard monitor check: at `switch_bb`, the ONLY lock guard held
        // by this frame must be `guard_id` itself (if an outer lock is held
        // across `cv.wait(g)`, as in `*_deadlock_wait`, the wait does not
        // release all held locks).
        let held = guards_held_at_block_exit(instance_id, body, lockguards, &back_edges, switch_bb);
        if held.as_slice() != &[guard_id] {
            continue;
        }

        // Find `wait_bb` reachable from `loop_body_bb` (without crossing `header_bb` or `loop_exit_bb`).
        let Some(wait_bb) = find_wait_bb_in_loop(
            body,
            tcx,
            key_api_regex,
            guard_id,
            loop_body_bb,
            header_bb,
            loop_exit_bb,
        ) else {
            continue;
        };

        // Find back edge `(latch_bb, header_bb)` reachable from `wait_bb`.
        let Some(&(latch_bb, _)) = back_edges.iter().find(|&&(src, dst)| {
            dst == header_bb && block_reaches_without(body, wait_bb, src, header_bb)
        }) else {
            continue;
        };

        loops.push(BoolWaitLoop {
            guard_id,
            header_bb,
            switch_bb,
            loop_body_bb,
            loop_exit_bb,
            wait_bb,
            latch_bb,
        });
    }

    loops
}

fn find_wait_bb_in_loop<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    key_api_regex: &KeyApiRegex,
    guard_id: LockGuardId,
    start_bb: BasicBlock,
    header_bb: BasicBlock,
    exit_bb: BasicBlock,
) -> Option<BasicBlock> {
    let mut visited = vec![false; body.basic_blocks.len()];
    let mut queue = VecDeque::new();
    visited[start_bb.index()] = true;
    queue.push_back(start_bb);

    while let Some(bb_idx) = queue.pop_front() {
        let bb = &body.basic_blocks[bb_idx];
        if bb.is_cleanup || bb.is_empty_unreachable() {
            continue;
        }
        if let Some(term) = &bb.terminator {
            if let TerminatorKind::Call { func, args, .. } = &term.kind
                && let Some(def_id) = (match func.ty(body, tcx).kind() {
                    TyKind::FnDef(id, _) | TyKind::Closure(id, _) => Some(*id),
                    _ => None,
                })
            {
                let name = format_name(def_id);
                let def_path = tcx.def_path_str(def_id);
                let is_wait = crate::analysis::memory::ownership::is_condvar_wait(def_id, tcx)
                    || has_spn_attribute(tcx, def_id, "pn_condvar_wait")
                    || key_api_regex.matches_condvar_wait(&name)
                    || parking_lot_condvar_call(&def_path, CondvarModel::All)
                        == Some(CondvarCallKind::Wait);
                if is_wait {
                    let uses_guard = args.iter().skip(1).any(|arg| {
                        arg.node.place().is_some_and(|p| {
                            p.projection.is_empty()
                                && local_reaches_guard(body, p.local, guard_id.local)
                        })
                    });
                    if uses_guard {
                        return Some(bb_idx);
                    }
                }
            }

            for succ in term.successors() {
                if succ == header_bb || succ == exit_bb {
                    continue;
                }
                if !body.basic_blocks[succ].is_cleanup && !visited[succ.index()] {
                    visited[succ.index()] = true;
                    queue.push_back(succ);
                }
            }
        }
    }

    None
}

fn block_reaches_without(
    body: &Body<'_>,
    from: BasicBlock,
    target: BasicBlock,
    forbidden: BasicBlock,
) -> bool {
    let mut visited = vec![false; body.basic_blocks.len()];
    let mut queue = VecDeque::new();
    visited[from.index()] = true;
    queue.push_back(from);
    while let Some(bb) = queue.pop_front() {
        if bb == target {
            return true;
        }
        if let Some(term) = &body.basic_blocks[bb].terminator {
            for succ in term.successors() {
                if succ == forbidden {
                    continue;
                }
                if !body.basic_blocks[succ].is_cleanup && !visited[succ.index()] {
                    visited[succ.index()] = true;
                    queue.push_back(succ);
                }
            }
        }
    }
    false
}

fn guards_held_at_block_exit<'tcx>(
    instance_id: InstanceId,
    body: &Body<'tcx>,
    lockguards: &LockGuardMap<'tcx>,
    back_edges: &FxHashSet<(BasicBlock, BasicBlock)>,
    target_bb: BasicBlock,
) -> Vec<LockGuardId> {
    let mut frame_guards: Vec<LockGuardId> = lockguards
        .keys()
        .filter(|g| g.instance_id == instance_id)
        .copied()
        .collect();
    frame_guards.sort_by_key(|g| (g.local.as_u32(), g.field));

    frame_guards
        .into_iter()
        .filter(|&gid| guard_reaches_block_exit_held(instance_id, body, back_edges, gid, target_bb))
        .collect()
}

fn guard_reaches_block_exit_held<'tcx>(
    instance_id: InstanceId,
    body: &Body<'tcx>,
    back_edges: &FxHashSet<(BasicBlock, BasicBlock)>,
    guard_id: LockGuardId,
    target_bb: BasicBlock,
) -> bool {
    let num_bbs = body.basic_blocks.len();
    let mut entered_held = vec![false; num_bbs];
    let mut exited_held = vec![false; num_bbs];
    let mut worklist: VecDeque<BasicBlock> = VecDeque::new();

    for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
        if bb.is_cleanup || bb.is_empty_unreachable() {
            continue;
        }
        if eval_block_for_guard(instance_id, bb, guard_id, false) {
            worklist.push_back(bb_idx);
        }
    }

    while let Some(bb_idx) = worklist.pop_front() {
        let bb = &body.basic_blocks[bb_idx];
        if bb.is_cleanup || bb.is_empty_unreachable() {
            continue;
        }
        let held_at_exit =
            eval_block_for_guard(instance_id, bb, guard_id, entered_held[bb_idx.index()]);
        if held_at_exit && !exited_held[bb_idx.index()] {
            exited_held[bb_idx.index()] = true;
            if bb_idx == target_bb {
                return true;
            }
            if let Some(term) = &bb.terminator {
                for succ in term.successors() {
                    if body.basic_blocks[succ].is_cleanup {
                        continue;
                    }
                    if back_edges.contains(&(bb_idx, succ)) {
                        continue;
                    }
                    if !entered_held[succ.index()] {
                        entered_held[succ.index()] = true;
                        worklist.push_back(succ);
                    }
                }
            }
        }
    }

    exited_held.get(target_bb.index()).copied().unwrap_or(false)
}

fn eval_block_for_guard<'tcx>(
    instance_id: InstanceId,
    bb: &BasicBlockData<'tcx>,
    guard_id: LockGuardId,
    mut held: bool,
) -> bool {
    for stmt in &bb.statements {
        if let StatementKind::Assign(boxed) = &stmt.kind {
            let (dest, rvalue) = &**boxed;
            if let Rvalue::Use(Operand::Move(src), _) = rvalue {
                if lockguard_id_for_place(instance_id, src) == guard_id {
                    held = false;
                }
            }
            if lockguard_id_for_place(instance_id, dest) == guard_id {
                held = true;
            }
        }
    }
    if let Some(term) = &bb.terminator {
        match &term.kind {
            TerminatorKind::Drop { place, .. } => {
                if lockguard_id_for_place(instance_id, place) == guard_id {
                    held = false;
                }
            }
            TerminatorKind::Call {
                args,
                destination,
                target: Some(_),
                ..
            } => {
                for arg in args.iter() {
                    if let Operand::Move(src) = &arg.node {
                        if lockguard_id_for_place(instance_id, src) == guard_id {
                            held = false;
                        }
                    }
                }
                if lockguard_id_for_place(instance_id, destination) == guard_id {
                    held = true;
                }
            }
            _ => {}
        }
    }
    held
}
