//! Extract CIR resources from Petri-net places and transition types.

use indexmap::IndexSet;
use rust_petri_net_analysis::net::Net;
use rust_petri_net_analysis::net::ids::TransitionId;
use rust_petri_net_analysis::net::structure::{PlaceType, TransitionType};
use serde_json::json;

use crate::ast::{BaseType, Resource, ResourceKind, SyncMode};

pub fn extract_resources(net: &Net) -> Vec<Resource> {
    let mut names = IndexSet::new();
    let mut out = Vec::new();

    for place in net.places.iter() {
        if place.place_type != PlaceType::Resources {
            continue;
        }
        let name = sanitize_resource_name(&place.name);
        if !names.insert(name.clone()) {
            continue;
        }
        out.push(infer_resource_from_place_name(&name));
    }

    for transition in net.transitions.iter() {
        for inferred in infer_resources_from_transition(&transition.transition_type) {
            if names.insert(inferred.name.clone()) {
                out.push(inferred);
            }
        }
    }

    out.sort_by(|a, b| a.name.cmp(&b.name));
    out
}

fn sanitize_resource_name(raw: &str) -> String {
    raw.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

fn infer_resource_from_place_name(name: &str) -> Resource {
    let lower = name.to_ascii_lowercase();
    if lower.contains("mutex") || lower.starts_with("lock") {
        sync_resource(name, "Mutex")
    } else if lower.contains("rwlock") {
        sync_resource(name, "RwLock")
    } else if lower.contains("condvar") || lower.contains("cond") {
        sync_resource(name, "Condvar")
    } else if lower.contains("channel") {
        Resource {
            name: name.into(),
            kind: ResourceKind::Sync,
            res_type: "Channel".into(),
            mode: Some(SyncMode::Sync),
            count: None,
            base: Some(BaseType::Primitive("Int".into())),
            init: None,
        }
    } else if lower.contains("atomic") {
        Resource {
            name: name.into(),
            kind: ResourceKind::Var,
            res_type: "Atomic".into(),
            mode: None,
            count: None,
            base: Some(BaseType::Primitive("Int".into())),
            init: Some(json!(0)),
        }
    } else if lower.contains("unsafe") {
        Resource {
            name: name.into(),
            kind: ResourceKind::Var,
            res_type: "Var".into(),
            mode: None,
            count: None,
            base: Some(BaseType::Primitive("Int".into())),
            init: Some(json!(0)),
        }
    } else {
        Resource {
            name: name.into(),
            kind: ResourceKind::Var,
            res_type: "Var".into(),
            mode: None,
            count: None,
            base: Some(BaseType::Primitive("Int".into())),
            init: Some(json!(0)),
        }
    }
}

fn sync_resource(name: &str, ty: &str) -> Resource {
    Resource {
        name: name.into(),
        kind: ResourceKind::Sync,
        res_type: ty.into(),
        mode: Some(SyncMode::Sync),
        count: None,
        base: None,
        init: None,
    }
}

fn infer_resources_from_transition(tt: &TransitionType) -> Vec<Resource> {
    let mut out = Vec::new();
    match tt {
        TransitionType::Lock(idx)
        | TransitionType::RwLockRead(idx)
        | TransitionType::RwLockWrite(idx)
        | TransitionType::Unlock(idx) => {
            out.push(sync_resource(
                &super::ops::resource_name_from_index(*idx, "lock"),
                "Mutex",
            ));
        }
        TransitionType::Notify(idx) => {
            out.push(sync_resource(
                &super::ops::resource_name_from_index(*idx, "condvar"),
                "Condvar",
            ));
        }
        TransitionType::Wait => {
            out.push(sync_resource("condvar_0", "Condvar"));
            out.push(sync_resource(
                &super::ops::resource_name_from_index(0, "lock"),
                "Mutex",
            ));
        }
        TransitionType::AtomicLoad(_, _, _, _)
        | TransitionType::AtomicStore(_, _, _, _)
        | TransitionType::AtomicCmpXchg(_, _, _, _, _) => {
            out.push(Resource {
                name: "atomic_0".into(),
                kind: ResourceKind::Var,
                res_type: "Atomic".into(),
                mode: None,
                count: None,
                base: Some(BaseType::Primitive("Int".into())),
                init: Some(json!(0)),
            });
        }
        _ => {}
    }
    out
}

/// Collect transition ids that carry concurrency semantics (for function body stubs).
pub fn concurrency_transition_ids(net: &Net) -> Vec<TransitionId> {
    net.transitions
        .iter_enumerated()
        .filter_map(|(tid, t)| {
            if matches!(
                t.transition_type,
                TransitionType::Lock(_)
                    | TransitionType::RwLockRead(_)
                    | TransitionType::RwLockWrite(_)
                    | TransitionType::Unlock(_)
                    | TransitionType::Notify(_)
                    | TransitionType::Wait
                    | TransitionType::Spawn(_)
                    | TransitionType::Join(_)
                    | TransitionType::AtomicLoad(_, _, _, _)
                    | TransitionType::AtomicStore(_, _, _, _)
                    | TransitionType::Function
                    | TransitionType::Return(_)
            ) {
                Some(tid)
            } else {
                None
            }
        })
        .collect()
}
