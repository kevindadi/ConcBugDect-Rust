//! JSON for blocked places, σ steps, and transition types.
//! Field names and order are fixed by the schema, including `is_wait_point`.
//! It does not choose which deadlocks are reported.

use serde_json::{Value, json};
use unipn::net::{ArcDir, Marking, PlaceId, PlaceRole, TransitionId};
use unipn::pt::{PtNet, TransitionType};

use super::{RawTrans, SigmaStep};

/// One blocked place: its identity plus, per transition that could consume its
/// token, the inputs that are short.
pub(super) fn blocked_place_json(net: &PtNet, marking: &Marking, place: PlaceId) -> Value {
    let (name, place_type, span) = match net.place(place) {
        Some(p) => (
            p.name.clone(),
            // The Debug rendering (`Control(BasicBlock)`) is the shape the
            // schema fixes; serde would spell the class as
            // `{"Control":"BasicBlock"}`.
            format!("{:?}", p.kind.place_type),
            p.kind.span.clone(),
        ),
        None => {
            log::error!("deadlock report: place {} is out of range", place.index());
            (String::new(), String::new(), String::new())
        }
    };

    let outgoing: Vec<Value> = net
        .arcs_at(place)
        .filter(|arc| arc.direction == ArcDir::Input)
        .map(|arc| outgoing_transition_json(net, marking, arc.transition))
        .collect();

    json!({
        "place_id": place.index(),
        "name": name,
        "place_type": place_type,
        "span": span,
        "is_wait_point": net.is_wait_point(place),
        "outgoing": outgoing,
    })
}

fn outgoing_transition_json(net: &PtNet, marking: &Marking, transition: TransitionId) -> Value {
    let (name, transition_type) = match net.transition(transition) {
        Some(t) => (
            t.name.clone(),
            transition_type_json(&t.kind.transition_type),
        ),
        None => {
            log::error!(
                "deadlock report: transition {} is out of range",
                transition.index()
            );
            (String::new(), Value::Null)
        }
    };

    // The inputs the transition cannot get: `tokens_available < weight`, with
    // the arc's own weight (an `RwLockWrite` acquire asks for the full
    // `RWLOCK_CAPACITY`).
    let missing_inputs: Vec<Value> = net
        .arcs_of(transition, ArcDir::Input)
        .filter(|arc| marking.tokens(arc.place) < arc.weight)
        .map(|arc| {
            let (place_name, is_resource) = match net.place(arc.place) {
                Some(p) => (p.name.clone(), p.kind.is_resource()),
                None => {
                    log::error!(
                        "deadlock report: place {} is out of range",
                        arc.place.index()
                    );
                    (String::new(), false)
                }
            };
            json!({
                "place_id": arc.place.index(),
                "name": place_name,
                "is_resource": is_resource,
                "weight_required": arc.weight,
                "tokens_available": marking.tokens(arc.place),
            })
        })
        .collect();

    // Every resource place the transition reads, not only the ones it cannot
    // get. A `Condvar::wait` re-acquires the guard's mutex when it wakes, so
    // its input arcs name both the condvar (an event source, not a lock) and
    // the mutex the waiter holds. The replay evidence reports unmatched
    // *locks*, so the diagnosis needs the mutex to line up with it.
    let resource_inputs: Vec<Value> = net
        .arcs_of(transition, ArcDir::Input)
        .filter_map(|arc| {
            let place = match net.place(arc.place) {
                Some(place) => place,
                None => {
                    log::error!(
                        "deadlock report: place {} is out of range",
                        arc.place.index()
                    );
                    return None;
                }
            };
            if !place.kind.is_resource() {
                return None;
            }
            Some(json!({
                "place_id": arc.place.index(),
                "name": place.name.clone(),
                "weight": arc.weight,
                "tokens_available": marking.tokens(arc.place),
            }))
        })
        .collect();

    json!({
        "transition_id": transition.index(),
        "name": name,
        "transition_type": transition_type,
        "missing_inputs": missing_inputs,
        "resource_inputs": resource_inputs,
    })
}

/// The JSON projection of one structured σ step. Field names and order must
/// stay exactly as the schema fixes them.
pub(super) fn sigma_step_json(step: &SigmaStep) -> Value {
    json!({
        "step": step.step,
        "from_state": step.from_state,
        "to_state": step.to_state,
        "transition_id": step.transition_id.index(),
        "name": step.name,
        "transition_type": transition_type_json(&step.transition_type),
        "raw": step.raw.iter().map(raw_trans_json).collect::<Vec<Value>>(),
    })
}

fn raw_trans_json(raw: &RawTrans) -> Value {
    json!({ "transition_id": raw.transition_id.index(), "name": raw.name })
}

/// The JSON shape of a transition type: serde's own rendering, never a hand
/// written spelling (`{"Lock": 3}` for payload variants, `"Wait"` for bare
/// ones). Falls back to `null` if serialization somehow fails, which for this
/// enum cannot happen.
fn transition_type_json(transition_type: &TransitionType) -> Value {
    serde_json::to_value(transition_type).unwrap_or(Value::Null)
}

#[cfg(test)]
mod tests {
    use super::super::fixture::{add_t, bb, end, report_of, res, state_graph};
    use super::super::{NO_EXCLUSIONS, ReportInputs, build_deadlock_report};
    use serde_json::{Value, json};
    use unipn::NetLike;
    use unipn::analysis::pt::reduce::{ReductionOptions, reduce_in_place};
    use unipn::net::{Marking, PlaceId, TransitionId, TransitionRole};
    use unipn::pt::{PtBuilder, TransitionType};

    #[test]
    fn lock_order_inversion_reports_replayable_sigma() {
        let mut b = PtBuilder::new();
        let l1 = b.add_marked_place("L1", res(), 1);
        let l2 = b.add_marked_place("L2", res(), 1);
        let a: Vec<PlaceId> = (0..5)
            .map(|i| {
                b.add_marked_place(
                    format!("a{i}"),
                    if i == 4 { end() } else { bb() },
                    usize::from(i == 0),
                )
            })
            .collect();
        let c: Vec<PlaceId> = (0..5)
            .map(|i| {
                b.add_marked_place(
                    format!("b{i}"),
                    if i == 4 { end() } else { bb() },
                    usize::from(i == 0),
                )
            })
            .collect();

        add_t(
            &mut b,
            "A lock L1",
            TransitionType::Lock(l1.index()),
            &[a[0], l1],
            &[a[1]],
        );
        add_t(
            &mut b,
            "A lock L2",
            TransitionType::Lock(l2.index()),
            &[a[1], l2],
            &[a[2]],
        );
        add_t(
            &mut b,
            "A unlock L2",
            TransitionType::Unlock(l2.index()),
            &[a[2]],
            &[a[3], l2],
        );
        add_t(
            &mut b,
            "A unlock L1",
            TransitionType::Unlock(l1.index()),
            &[a[3]],
            &[a[4], l1],
        );
        add_t(
            &mut b,
            "B lock L2",
            TransitionType::Lock(l2.index()),
            &[c[0], l2],
            &[c[1]],
        );
        add_t(
            &mut b,
            "B lock L1",
            TransitionType::Lock(l1.index()),
            &[c[1], l1],
            &[c[2]],
        );
        add_t(
            &mut b,
            "B unlock L1",
            TransitionType::Unlock(l1.index()),
            &[c[2]],
            &[c[3], l1],
        );
        add_t(
            &mut b,
            "B unlock L2",
            TransitionType::Unlock(l2.index()),
            &[c[3]],
            &[c[4], l2],
        );
        let (net, m0) = b.build();

        let sg = state_graph(&net, &m0);
        let deadlocks = sg.deadlock_states(&net);
        assert_eq!(deadlocks.len(), 1, "one crossed-lock deadlock");
        let deadlock_marking = sg.states[deadlocks[0]].marking.clone();
        assert_eq!(deadlock_marking.tokens(a[1]), 1, "A holds L1, wants L2");
        assert_eq!(deadlock_marking.tokens(c[1]), 1, "B holds L2, wants L1");
        assert_eq!(
            sg.stats().blocked_count,
            2,
            "the deadlock and the clean end"
        );

        let report = report_of("lock_order_inversion", &net, &sg);
        assert_eq!(report["net"]["reduced"], false);
        assert_eq!(report["state_graph"]["deadlock_count"], 1);
        assert_eq!(report["state_graph"]["reported"], 1);
        let entries = report["deadlocks"].as_array().unwrap();
        assert_eq!(entries.len(), 1);
        let deadlock = &entries[0];
        assert_eq!(deadlock["sigma_truncated"], false);

        // σ replays from the initial marking and reaches exactly the deadlock
        // marking, stepping through the very states the graph recorded.
        let sigma = deadlock["sigma"].as_array().unwrap();
        assert!(!sigma.is_empty());
        assert_eq!(
            sigma[0]["from_state"].as_u64().unwrap() as usize,
            sg.initial
        );
        let mut marking = m0.clone();
        for (step, entry) in sigma.iter().enumerate() {
            assert_eq!(entry["step"].as_u64().unwrap() as usize, step);
            let t = TransitionId(entry["transition_id"].as_u64().unwrap() as usize);
            marking = net.fire(&marking, t).expect("sigma step is enabled");
            let to = entry["to_state"].as_u64().unwrap() as usize;
            assert_eq!(marking, sg.states[to].marking, "replay matches the graph");
        }
        assert_eq!(marking, deadlock_marking);

        // Both stuck threads are diagnosed as waiting for the other's lock.
        let blocked_places = deadlock["blocked_places"].as_array().unwrap();
        assert_eq!(blocked_places.len(), 2);
        for place in blocked_places {
            assert_eq!(place["is_wait_point"], false);
            let outgoing = place["outgoing"].as_array().unwrap();
            assert_eq!(outgoing.len(), 1);
            let t = TransitionId(outgoing[0]["transition_id"].as_u64().unwrap() as usize);
            assert!(
                net.transition(t).unwrap().kind.is_acquire(),
                "the blocked transition is a lock acquire"
            );
            let missing = outgoing[0]["missing_inputs"].as_array().unwrap();
            assert_eq!(missing.len(), 1);
            assert_eq!(missing[0]["is_resource"], true);
            assert_eq!(missing[0]["tokens_available"], 0);
            assert_eq!(missing[0]["weight_required"], 1);
        }
    }

    /// A blocked thread parked before a `Wait` transition *is* a wait point:
    /// it waits for an event (here a notification that never comes) rather
    /// than for a resource somebody holds.
    #[test]
    fn wait_point_is_diagnosed() {
        let mut b = PtBuilder::new();
        let a0 = b.add_marked_place("a0", bb(), 1);
        let a1 = b.add_place("a1", end());
        let sig = b.add_marked_place("Sig", res(), 0);
        add_t(&mut b, "a wait", TransitionType::Wait, &[a0, sig], &[a1]);
        let (net, m0) = b.build();

        let sg = state_graph(&net, &m0);
        let deadlocks = sg.deadlock_states(&net);
        assert_eq!(deadlocks.len(), 1, "the initial state is the deadlock");
        assert_eq!(deadlocks[0], sg.initial);

        let report = report_of("wait_point", &net, &sg);
        let deadlock = &report["deadlocks"][0];
        assert_eq!(deadlock["sigma"], json!([]));
        assert_eq!(deadlock["sigma_truncated"], false);

        let blocked = deadlock["blocked_places"].as_array().unwrap();
        assert_eq!(blocked.len(), 1);
        assert_eq!(blocked[0]["is_wait_point"], true);
        let outgoing = blocked[0]["outgoing"].as_array().unwrap();
        assert_eq!(outgoing.len(), 1);
        assert_eq!(outgoing[0]["transition_type"], json!("Wait"));
        let missing = outgoing[0]["missing_inputs"].as_array().unwrap();
        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0]["is_resource"], true);
        assert_eq!(missing[0]["tokens_available"], 0);
    }

    /// A `Condvar::wait` re-acquires the guard's mutex when it wakes, so its
    /// transition reads the mutex as well as the condvar. The blocked-place
    /// diagnosis must expose the mutex (`resource_inputs`): the replay's
    /// unmatched-lock set names locks, never condvars, so without it a
    /// lost-wakeup diagnosis can never line up with the runtime evidence.
    #[test]
    fn wait_point_reports_the_reacquired_mutex() {
        const CONDVAR: &str = "Condvar:src/main.rs:1:1: 1:2 (#0)";
        let mut b = PtBuilder::new();
        let a0 = b.add_marked_place("a0", bb(), 1);
        let a1 = b.add_place("a1", end());
        let sig = b.add_marked_place(CONDVAR, res(), 0);
        let mutex = b.add_marked_place("Mutex_0", res(), 1);
        add_t(
            &mut b,
            "a wait",
            TransitionType::Wait,
            &[a0, sig, mutex],
            &[a1, mutex],
        );
        let (net, m0) = b.build();

        let sg = state_graph(&net, &m0);
        let deadlocks = sg.deadlock_states(&net);
        assert_eq!(deadlocks.len(), 1, "the wait blocks on the condvar");

        let report = report_of("wait_point_mutex", &net, &sg);
        let outgoing = report["deadlocks"][0]["blocked_places"][0]["outgoing"]
            .as_array()
            .unwrap();
        assert_eq!(outgoing.len(), 1);
        let missing = outgoing[0]["missing_inputs"].as_array().unwrap();
        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0]["name"], json!(CONDVAR));

        let resources = outgoing[0]["resource_inputs"].as_array().unwrap();
        let names: Vec<&str> = resources
            .iter()
            .map(|entry| entry["name"].as_str().unwrap())
            .collect();
        assert!(names.contains(&CONDVAR), "the condvar is still an input");
        assert!(
            names.contains(&"Mutex_0"),
            "the waiter's internal mutex must be reported"
        );
        let mutex_entry = resources
            .iter()
            .find(|entry| entry["name"] == json!("Mutex_0"))
            .unwrap();
        assert_eq!(mutex_entry["tokens_available"], 1);
    }

    #[test]
    fn report_round_trips_through_serde() {
        let mut b = PtBuilder::new();
        let l = b.add_marked_place("L", res(), 1);
        let a0 = b.add_marked_place("a0", bb(), 1);
        let a1 = b.add_place("a1", bb());
        let c0 = b.add_marked_place("b0", bb(), 1);
        let c1 = b.add_place("b1", bb());
        add_t(
            &mut b,
            "A lock",
            TransitionType::Lock(l.index()),
            &[a0, l],
            &[a1],
        );
        add_t(
            &mut b,
            "B lock",
            TransitionType::Lock(l.index()),
            &[c0, l],
            &[c1],
        );
        let (net, m0) = b.build();

        let sg = state_graph(&net, &m0);
        let report = report_of("round_trip", &net, &sg);
        let text = serde_json::to_string(&report).unwrap();
        let parsed: Value = serde_json::from_str(&text).unwrap();
        assert_eq!(serde_json::to_string(&parsed).unwrap(), text);
    }

    /// The `raw` lift, with and without reduction.
    ///
    /// (a) pins the direction of `transition_mapping`: sequence merge records
    /// the originals in chain order, head transition first. (b) builds a net
    /// whose deadlock is only reachable through a merged chain, checks the
    /// reported `raw` list and replays it on the *original* net step by step.
    /// (c) repeats (b) without reduction, where every `raw` list is `[self]`.
    #[test]
    fn trace_lifting_round_trips() {
        // (a) direction check on a minimal mergeable chain.
        let mut b = PtBuilder::new();
        let p0 = b.add_marked_place("p0", bb(), 1);
        let p1 = b.add_place("p1", bb());
        let p2 = b.add_place("p2", end());
        let t0 = add_t(&mut b, "t0", TransitionType::Normal, &[p0], &[p1]);
        let t1 = add_t(&mut b, "t1", TransitionType::Normal, &[p1], &[p2]);
        let (net, m0) = b.build();
        let reduced =
            reduce_in_place(&net, &m0, ReductionOptions::default()).expect("reduction succeeds");
        assert_eq!(reduced.net.num_transitions(), 1, "t0 and t1 merge");
        assert_eq!(
            reduced.trace.transition_mapping,
            vec![vec![t0, t1]],
            "originals are recorded head-first in chain order"
        );

        // (b) a deadlock reachable only through the merged chain: thread A
        // walks t0, t1 and then blocks on L1, which thread B never hands back.
        // The chain ends on a branch place (two outputs), which is what stops
        // the merge from swallowing the blocking acquire.
        let mut b = PtBuilder::new();
        let l1 = b.add_marked_place("L1", res(), 1);
        let a0 = b.add_marked_place("a0", bb(), 1);
        let a1 = b.add_place("a1", bb());
        let a2 = b.add_place("a2", bb());
        let q = b.add_place("q", bb());
        let a3 = b.add_place("a3", bb());
        let a4 = b.add_place("a4", end());
        let b0 = b.add_marked_place("b0", bb(), 1);
        let b1 = b.add_place("b1", bb());
        let b2 = b.add_place("b2", end());
        add_t(&mut b, "t0", TransitionType::Normal, &[a0], &[a1]);
        add_t(&mut b, "t1", TransitionType::Normal, &[a1], &[a2]);
        add_t(&mut b, "t_plain", TransitionType::Normal, &[a2], &[q]);
        add_t(&mut b, "t_skip", TransitionType::Normal, &[a2], &[a4]);
        add_t(
            &mut b,
            "t_lock",
            TransitionType::Lock(l1.index()),
            &[q, l1],
            &[a3],
        );
        add_t(
            &mut b,
            "t_unlock",
            TransitionType::Unlock(l1.index()),
            &[a3],
            &[a4, l1],
        );
        add_t(
            &mut b,
            "tb_lock",
            TransitionType::Lock(l1.index()),
            &[b0, l1],
            &[b1],
        );
        add_t(&mut b, "tb_end", TransitionType::Normal, &[b1], &[b2]);
        let (net, m0) = b.build();

        let reduced =
            reduce_in_place(&net, &m0, ReductionOptions::default()).expect("reduction succeeds");
        let trace = &reduced.trace;
        let sg = state_graph(&reduced.net, &reduced.marking);
        let deadlocks = sg.deadlock_states(&reduced.net);
        assert_eq!(deadlocks.len(), 1);
        let deadlock_marking = sg.states[deadlocks[0]].marking.clone();

        let report = build_deadlock_report(&ReportInputs {
            crate_name: "trace_lifting",
            raw_net: &net,
            net: &reduced.net,
            state_graph: &sg,
            reduce_trace: Some(trace),
            excluded: &NO_EXCLUSIONS,
            entry_mode: "main",
            slice_layout: None,
        });
        assert_eq!(report["net"]["reduced"], true);
        assert_eq!(
            report["net"]["places"].as_u64().unwrap() as usize,
            reduced.net.num_places()
        );
        assert_eq!(
            report["net"]["raw_places"].as_u64().unwrap() as usize,
            net.num_places()
        );
        assert_eq!(report["state_graph"]["deadlock_count"], 1);

        let sigma = report["deadlocks"][0]["sigma"].as_array().unwrap();
        assert!(!sigma.is_empty());
        let merged = sigma
            .iter()
            .find(|step| step["name"] == json!("seq_merge#0"))
            .expect("σ crosses the merged chain");
        assert_eq!(
            merged["raw"],
            json!([
                { "transition_id": t0.index(), "name": "t0" },
                { "transition_id": t1.index(), "name": "t1" },
            ]),
            "raw is lifted head-first, matching transition_mapping"
        );

        // Replay: fire every raw transition on the original net; each step is
        // enabled, and after each σ step the marking projected onto the kept
        // places equals the graph state the step reached. The graph marking
        // already lives in reduced-id space (this engine never merges places),
        // so the projection is only needed on the raw side.
        let project = |marking: &Marking| -> Vec<usize> {
            trace
                .place_mapping
                .iter()
                .map(|raws| raws.iter().map(|p| marking.tokens(*p)).sum::<usize>())
                .collect()
        };
        let expected_final = deadlock_marking.0.clone();
        let mut marking = m0.clone();
        for entry in sigma {
            for raw in entry["raw"].as_array().unwrap() {
                let id = TransitionId(raw["transition_id"].as_u64().unwrap() as usize);
                marking = net.fire(&marking, id).expect("raw step is enabled");
            }
            let to = entry["to_state"].as_u64().unwrap() as usize;
            assert_eq!(
                project(&marking),
                sg.states[to].marking.0,
                "projection after a σ step matches the graph state"
            );
        }
        assert_eq!(project(&marking), expected_final);

        // (c) without reduction every step lifts to itself.
        let raw_sg = state_graph(&net, &m0);
        let raw_deadlocks = raw_sg.deadlock_states(&net);
        assert_eq!(raw_deadlocks.len(), 1);
        let raw_report = report_of("trace_lifting_raw", &net, &raw_sg);
        assert_eq!(raw_report["net"]["reduced"], false);
        let raw_sigma = raw_report["deadlocks"][0]["sigma"].as_array().unwrap();
        assert!(!raw_sigma.is_empty());
        for entry in raw_sigma {
            assert_eq!(
                entry["raw"],
                json!([{ "transition_id": entry["transition_id"], "name": entry["name"] }])
            );
        }
    }
}
