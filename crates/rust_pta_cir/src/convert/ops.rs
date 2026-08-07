//! Map Petri-net `TransitionType` values to CIR operations.

use rust_petri_net_analysis::net::structure::TransitionType;

use crate::ast::Op;

/// Human-readable resource name derived from a place index embedded in transition types.
pub fn resource_name_from_index(idx: usize, prefix: &str) -> String {
    format!("{prefix}_{idx}")
}

/// Best-effort mapping from a sync Petri-net transition to a CIR op.
pub fn transition_to_op(transition_type: &TransitionType, transition_name: &str) -> Op {
    match transition_type {
        TransitionType::Lock(idx) => Op::ResOp {
            resource: resource_name_from_index(*idx, "lock"),
            action: "lock".into(),
            args: vec![],
        },
        TransitionType::RwLockRead(idx) | TransitionType::RwLockWrite(idx) => Op::ResOp {
            resource: resource_name_from_index(*idx, "lock"),
            action: "lock".into(),
            args: vec![],
        },
        TransitionType::Unlock(idx) => Op::ResOp {
            resource: resource_name_from_index(*idx, "lock"),
            action: "drop".into(),
            args: vec![],
        },
        TransitionType::Notify(idx) => Op::ResOp {
            resource: resource_name_from_index(*idx, "condvar"),
            action: "notify".into(),
            args: vec![],
        },
        TransitionType::Wait => Op::ResOp {
            resource: "condvar_0".into(),
            action: "wait".into(),
            args: vec!["lock_0".into()],
        },
        TransitionType::Spawn(target) => Op::Spawn(clean_fn_name(target)),
        TransitionType::Join(target) => Op::Join(clean_fn_name(target)),
        TransitionType::AtomicLoad(_, _, _, _) => Op::ResOp {
            resource: "atomic_0".into(),
            action: "load".into(),
            args: vec![],
        },
        TransitionType::AtomicStore(_, _, _, _) => Op::ResOp {
            resource: "atomic_0".into(),
            action: "store".into(),
            args: vec!["val".into()],
        },
        TransitionType::AtomicCmpXchg(_, _, _, _, _) => Op::ResOp {
            resource: "atomic_0".into(),
            action: "cas".into(),
            args: vec!["expected".into(), "desired".into()],
        },
        TransitionType::Function => Op::Call(extract_call_target(transition_name)),
        TransitionType::Return(_) => Op::Return,
        _ => Op::Nop,
    }
}

fn clean_fn_name(raw: &str) -> String {
    raw.rsplit("::").next().unwrap_or(raw).to_string()
}

fn extract_call_target(name: &str) -> String {
    if let Some(idx) = name.rfind("_call") {
        name[..idx].rsplit('_').next().unwrap_or(name).to_string()
    } else {
        clean_fn_name(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lock_maps_to_res_op() {
        let op = transition_to_op(&TransitionType::Lock(3), "t");
        assert!(matches!(
            op,
            Op::ResOp {
                resource,
                action,
                ..
            } if resource == "lock_3" && action == "lock"
        ));
    }

    #[test]
    fn spawn_maps_to_spawn() {
        let op = transition_to_op(&TransitionType::Spawn("worker".into()), "t");
        assert!(matches!(op, Op::Spawn(ref n) if n == "worker"));
    }
}
