//! Writes `subnets.json` (`pn-subnets/2`), one summary per translated frame.
//! The summary is projected from the built net and provenance. It does not
//! change the net.
//!
//! v2 differs from v1 (`pn-subnets/1`, the lowering record):
//! 1. `resource_ports` covers every sync resource (mutex, rwlock, condvar,
//!    atomic), not only locks.
//! 2. `kind` comes from the place role. A read lock is `rwlock`, not `mutex`.
//! 3. `calls` includes calls the record skipped, such as closures and static
//!    initializers.
//! 4. `thread_place` is the `ThreadPlace` role, so a detached spawn has one.
//!
//! `held_on_entry` / `held_on_exit` replay only lock acquire and release
//! (`Mutex` / `RwLock` on `Lock`, `RwLock*`, `Unlock`, `DropRead`, `DropWrite`).
//! Condvar, atomic, and thread arcs stay in `resource_ports`.

use std::fs;
use std::path::Path;

use serde::Serialize;
use unipn::net::ArcDir;
use unipn::pt::{PtNet, ResourceKind, TransitionType};
use unipn::{ControlSub, PlaceClass, PlaceId, TransitionId, TransitionRole};

use crate::translate::lower::facts::TranslationProvenance;

pub const SCHEMA: &str = "pn-subnets/2";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResourcePort {
    pub kind: String,
    pub direction: String,
    pub place: PlaceId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResourceSlot {
    pub kind: String,
    pub place: PlaceId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CalleeEdge {
    pub callee: String,
    pub call_site: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SubNetContext {
    pub fn_def_path: String,
    pub start: PlaceId,
    pub end: PlaceId,
    pub resource_ports: Vec<ResourcePort>,
    pub held_on_entry: Vec<ResourceSlot>,
    pub held_on_exit: Vec<ResourceSlot>,
    pub spawn_ports: Vec<PlaceId>,
    pub thread_place: Option<PlaceId>,
    pub calls: Vec<CalleeEdge>,
}

impl SubNetContext {
    pub fn new(fn_def_path: String, start: PlaceId, end: PlaceId) -> Self {
        Self {
            fn_def_path,
            start,
            end,
            resource_ports: Vec::new(),
            held_on_entry: Vec::new(),
            held_on_exit: Vec::new(),
            spawn_ports: Vec::new(),
            thread_place: None,
            calls: Vec::new(),
        }
    }

    /// Project this frame's summary from the built net and provenance.
    ///
    /// `start` and `end` come from the function-place registry. The
    /// projection does not read the lowering stack. Provenance stores the
    /// function name, and a transition belongs to this frame when that name
    /// matches.
    pub fn project(
        net: &PtNet,
        frame_name: &str,
        provenance: &TranslationProvenance,
        start: PlaceId,
        end: PlaceId,
    ) -> Self {
        let mut resource_ports = Vec::new();
        let mut hold_ports = Vec::new();
        let mut calls = Vec::new();
        let mut spawn_ports = Vec::new();
        let mut thread_place = None;

        for index in 0..net.num_transitions() {
            let tid = TransitionId::from(index);
            let Some(transition) = net.transition(tid) else {
                continue;
            };
            let Some(origin) = provenance.origin(tid) else {
                continue;
            };
            if !frame_owns(&origin.fn_def_path, frame_name) {
                continue;
            }
            let ty = &transition.kind.transition_type;
            let is_spawn = matches!(ty, TransitionType::Spawn(_));
            let is_function = matches!(ty, TransitionType::Function);

            for arc in net.arcs_for(tid) {
                let Some(place) = net.place(arc.place) else {
                    continue;
                };
                match arc.direction {
                    ArcDir::Input | ArcDir::Output => {
                        if is_resource(place) {
                            let port = ResourcePort {
                                kind: port_kind(net, arc.place, arc.weight),
                                direction: if arc.direction == ArcDir::Input {
                                    "acquire"
                                } else {
                                    "release"
                                }
                                .to_string(),
                                place: arc.place,
                            };
                            if net.resource_kind(arc.place).is_some_and(is_holdable)
                                && (transition.kind.is_acquire() || transition.kind.is_release())
                            {
                                hold_ports.push(port.clone());
                            }
                            resource_ports.push(port);
                        }
                        if arc.direction == ArcDir::Output {
                            if is_function && is_function_start(place) {
                                calls.push(CalleeEdge {
                                    callee: strip_start(&place.name),
                                    call_site: origin.span.clone(),
                                });
                            }
                            if is_spawn && is_function_start(place) {
                                spawn_ports.push(arc.place);
                            }
                            if is_spawn && net.is_thread_place(arc.place) && thread_place.is_none()
                            {
                                thread_place = Some(arc.place);
                            }
                        }
                    }
                    ArcDir::Read | ArcDir::Inhibitor | ArcDir::Reset => {}
                }
            }
        }
        let (held_on_entry, held_on_exit) = replay_holds(&hold_ports);
        Self {
            fn_def_path: frame_name.to_string(),
            start,
            end,
            resource_ports,
            held_on_entry,
            held_on_exit,
            spawn_ports,
            thread_place,
            calls,
        }
    }
}

/// A lock can be held across a call. Only `Lock` / `RwLock*` / `Unlock` /
/// `DropRead` / `DropWrite` move the stack. A condvar wait also takes and
/// returns the mutex, but that pair is not a frame-level hold: those arcs
/// stay in `resource_ports`. Condvar, atomic, and thread places
/// never enter the stack.
fn is_holdable(kind: ResourceKind) -> bool {
    matches!(kind, ResourceKind::Mutex | ResourceKind::RwLock)
}

/// Acquire pushes. Release pops. A release on an empty stack is a resource
/// the frame already held on entry. Whatever is still on the stack when the
/// frame ends is held on exit. Pop does not match the released place.
fn replay_holds(ports: &[ResourcePort]) -> (Vec<ResourceSlot>, Vec<ResourceSlot>) {
    let mut held_on_entry = Vec::new();
    let mut stack = Vec::new();
    for port in ports {
        let slot = ResourceSlot {
            kind: port.kind.clone(),
            place: port.place,
        };
        if port.direction == "acquire" {
            stack.push(slot);
        } else if port.direction == "release" && stack.pop().is_none() {
            held_on_entry.push(slot);
        }
    }
    (held_on_entry, stack)
}

fn frame_owns(origin_fn: &str, frame_name: &str) -> bool {
    origin_fn == frame_name
}

fn is_resource(place: &unipn::net::Place<unipn::pt::PtPlaceKind>) -> bool {
    matches!(place.kind.place_type, PlaceClass::Resource(_))
}

fn is_function_start(place: &unipn::net::Place<unipn::pt::PtPlaceKind>) -> bool {
    matches!(
        place.kind.place_type,
        PlaceClass::Control(ControlSub::FunctionStart)
    )
}

fn port_kind(net: &PtNet, place: PlaceId, weight: usize) -> String {
    let labeled = match net.resource_kind(place) {
        Some(ResourceKind::Mutex) => "mutex",
        Some(ResourceKind::RwLock) => "rwlock",
        Some(ResourceKind::Condvar) => "condvar",
        Some(ResourceKind::Atomic) => "atomic",
        Some(ResourceKind::Thread) => "thread",
        _ => {
            if weight > 1 {
                "rwlock"
            } else {
                "mutex"
            }
        }
    };
    labeled.to_string()
}

fn strip_start(name: &str) -> String {
    name.strip_suffix("_start").unwrap_or(name).to_string()
}

/// Same-function spawn/join binds the join to the thread place created by
/// spawn. A join with no thread place in this frame is a cross-function
/// `JoinHandle`, which this translator does not model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JoinDecision {
    ConsumeLocal,
    UnsupportedCrossFunction,
}

pub fn join_decision(have_local_thread_place: bool) -> JoinDecision {
    if have_local_thread_place {
        JoinDecision::ConsumeLocal
    } else {
        JoinDecision::UnsupportedCrossFunction
    }
}

pub fn write_subnets(
    dir: &Path,
    net: &PtNet,
    provenance: &TranslationProvenance,
    frames: &[SubNetContext],
) -> std::io::Result<()> {
    write_named(dir, project_frames(net, provenance, frames), "subnets.json")
}

pub fn write_projected_subnets(
    dir: &Path,
    net: &PtNet,
    provenance: &TranslationProvenance,
    frames: &[SubNetContext],
) -> std::io::Result<()> {
    write_named(
        dir,
        project_frames(net, provenance, frames),
        "subnets-projected.json",
    )
}

fn project_frames(
    net: &PtNet,
    provenance: &TranslationProvenance,
    frames: &[SubNetContext],
) -> Vec<SubNetContext> {
    frames
        .iter()
        .map(|frame| {
            SubNetContext::project(net, &frame.fn_def_path, provenance, frame.start, frame.end)
        })
        .collect()
}

fn write_named(dir: &Path, mut items: Vec<SubNetContext>, file_name: &str) -> std::io::Result<()> {
    items.sort_by(|a, b| {
        a.fn_def_path
            .cmp(&b.fn_def_path)
            .then_with(|| a.start.index().cmp(&b.start.index()))
            .then_with(|| a.end.index().cmp(&b.end.index()))
    });
    let body = serde_json::json!({
        "schema": SCHEMA,
        "subnets": items,
    });
    let mut text = serde_json::to_string_pretty(&body).map_err(std::io::Error::other)?;
    text.push('\n');
    fs::create_dir_all(dir)?;
    fs::write(dir.join(file_name), text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use unipn::ControlSub;
    use unipn::analysis::pt::reachability::StateGraph;
    use unipn::pt::{PlaceType, PtBuilder, PtPlaceKind, PtTransitionKind, TransitionType};

    #[test]
    fn same_function_spawn_join_consumes_thread_place() {
        assert_eq!(join_decision(true), JoinDecision::ConsumeLocal);

        let mut net = PtBuilder::empty();
        let start = net.add_marked_place(
            "main_start",
            PtPlaceKind {
                place_type: PlaceType::Control(ControlSub::FunctionStart),
                span: String::new(),
                capacity: None,
            },
            1,
        );
        let spawned = net.add_place(
            "child_start",
            PtPlaceKind {
                place_type: PlaceType::Control(ControlSub::FunctionStart),
                span: String::new(),
                capacity: None,
            },
        );
        let child_end = net.add_place(
            "child_end",
            PtPlaceKind {
                place_type: PlaceType::Control(ControlSub::FunctionEnd),
                span: String::new(),
                capacity: None,
            },
        );
        let thread_place = net.add_place(
            "main_thread_0",
            PtPlaceKind {
                place_type: PlaceType::Control(ControlSub::FunctionEnd),
                span: String::new(),
                capacity: Some(1),
            },
        );
        let after = net.add_place(
            "main_after",
            PtPlaceKind {
                place_type: PlaceType::Control(ControlSub::BasicBlock),
                span: String::new(),
                capacity: None,
            },
        );
        let spawn = net.add_transition(
            "spawn",
            PtTransitionKind::new(TransitionType::Spawn("spawn".into())),
        );
        net.add_input_arc(start, spawn, 1);
        net.add_output_arc(spawned, spawn, 1);
        net.add_output_arc(thread_place, spawn, 1);
        let child = net.add_transition("child", PtTransitionKind::new(TransitionType::Function));
        net.add_input_arc(spawned, child, 1);
        net.add_output_arc(child_end, child, 1);
        let join = net.add_transition(
            "join",
            PtTransitionKind::new(TransitionType::Join("join".into())),
        );
        net.add_input_arc(thread_place, join, 1);
        net.add_input_arc(child_end, join, 1);
        net.add_output_arc(after, join, 1);

        let (pt, marking) = net.build();
        let graph = StateGraph::from_net(&pt, marking);
        assert!(
            graph
                .states
                .iter()
                .any(|state| state.marking.tokens(after) == 1),
            "same-function join must be able to consume thread_place and the child end"
        );
        assert!(graph.deadlock_states(&pt).is_empty());
    }

    #[test]
    fn cross_function_join_is_unsupported() {
        assert_eq!(join_decision(false), JoinDecision::UnsupportedCrossFunction);
        let mut coverage = crate::report::coverage::Coverage::new();
        assert!(coverage.note_unsupported_cross_fn_join("crate::a"));
        assert!(!coverage.note_unsupported_cross_fn_join("crate::b"));
        assert_eq!(coverage.unsupported_cross_fn_join, 2);
    }

    #[test]
    fn project_twice_writes_identical_subnets() {
        use crate::translate::lower::facts::{TransOrigin, TranslationProvenance};
        use crate::translate::net::{NetBuilder, TransitionKind};
        use unipn::ResourceKind;

        let mut net = NetBuilder::new();
        let start = net.marked_place(
            PlaceClass::Control(ControlSub::FunctionStart),
            "crate::worker_start",
            1,
        );
        let end = net.place(
            PlaceClass::Control(ControlSub::FunctionEnd),
            "crate::worker_end",
            usize::MAX,
        );
        let child = net.place(
            PlaceClass::Control(ControlSub::FunctionStart),
            "child_start",
            usize::MAX,
        );
        let thread = net.place(
            PlaceClass::Control(ControlSub::ThreadPlace),
            "crate::worker_thread_0",
            1,
        );
        let mutex = net.place(PlaceClass::Resource(ResourceKind::Mutex), "Mutex_0", 1);
        net.set_tokens(mutex, 1);
        let rwlock = net.place(PlaceClass::Resource(ResourceKind::RwLock), "RwLock_0", 1);
        net.set_tokens(rwlock, 1);
        let condvar = net.place(PlaceClass::Resource(ResourceKind::Condvar), "Condvar_0", 1);
        let atomic = net.place(PlaceClass::Resource(ResourceKind::Atomic), "Atomic_0", 1);
        net.set_tokens(atomic, 1);

        let lock = net.transition(
            TransitionKind::new(TransitionType::Lock(mutex.index())),
            "lock",
        );
        net.arc_in(mutex, lock, 1);
        let unlock = net.transition(
            TransitionKind::new(TransitionType::Unlock(mutex.index())),
            "unlock",
        );
        net.arc_out(mutex, unlock, 1);
        let read = net.transition(
            TransitionKind::new(TransitionType::RwLockRead(rwlock.index())),
            "read",
        );
        net.arc_in(rwlock, read, 1);
        let wait = net.transition(TransitionKind::new(TransitionType::Wait), "wait");
        net.arc_out(mutex, wait, 1);
        net.arc_in(condvar, wait, 1);
        let call = net.transition(TransitionKind::new(TransitionType::Function), "call");
        net.arc_out(child, call, 1);
        let spawn = net.transition(
            TransitionKind::new(TransitionType::Spawn("spawn".to_string())),
            "spawn",
        );
        net.arc_out(child, spawn, 1);
        net.arc_out(thread, spawn, 1);
        let store = net.transition(TransitionKind::new(TransitionType::Normal), "store");
        net.arc_in(atomic, store, 1);
        net.arc_out(atomic, store, 1);

        let (pt, _) = net.finish();
        let provenance = TranslationProvenance {
            origins: (0..pt.num_transitions())
                .map(|_| TransOrigin {
                    fn_def_path: "crate::worker".to_string(),
                    bb: 0,
                    span: "src/lib.rs:1:1: 1:2 (#0)".to_string(),
                })
                .collect(),
            ..TranslationProvenance::default()
        };
        let once = SubNetContext::project(&pt, "crate::worker", &provenance, start, end);
        let twice = SubNetContext::project(&pt, "crate::worker", &provenance, start, end);
        assert_eq!(once, twice);
        assert!(once.held_on_entry.is_empty());
        assert_eq!(
            once.held_on_exit,
            vec![ResourceSlot {
                kind: "rwlock".to_string(),
                place: rwlock,
            }]
        );
        assert_eq!(once.thread_place, Some(thread));
        assert_eq!(once.calls.len(), 1);
        assert_eq!(once.calls[0].callee, "child");
        let kinds: Vec<&str> = once
            .resource_ports
            .iter()
            .map(|port| port.kind.as_str())
            .collect();
        assert!(kinds.contains(&"mutex"));
        assert!(kinds.contains(&"rwlock"));
        assert!(kinds.contains(&"condvar"));
        assert!(kinds.contains(&"atomic"));
        assert!(once.held_on_entry.iter().all(|slot| slot.kind != "condvar"));
        assert!(once.held_on_exit.iter().all(|slot| slot.kind != "atomic"));

        let root = std::env::temp_dir().join(format!("pn-subnet-twice-{}", std::process::id()));
        let left = root.join("a").join("crate");
        let right = root.join("b").join("crate");
        let frame = SubNetContext::new("crate::worker".to_string(), start, end);
        write_subnets(&left, &pt, &provenance, &[frame.clone()]).unwrap();
        write_subnets(&right, &pt, &provenance, &[frame]).unwrap();
        let left_bytes = std::fs::read(left.join("subnets.json")).unwrap();
        let right_bytes = std::fs::read(right.join("subnets.json")).unwrap();
        assert_eq!(left_bytes, right_bytes);
        let body: serde_json::Value = serde_json::from_slice(&left_bytes).unwrap();
        assert_eq!(body["schema"], "pn-subnets/2");
        let _ = std::fs::remove_dir_all(&root);
    }
}
