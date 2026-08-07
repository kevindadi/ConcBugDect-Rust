//! Async-PPN translation.
//!
//! Lowers `tokio::spawn` + `JoinHandle.await` and `.await` suspend points into Async-PPN subnets.

use rust_petri_net_analysis::net::{Net, PlaceId, TransitionId};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;

use crate::transition::{AsyncTransitionKind, make_transition};
use crate::translate::async_ppn::{AsyncPoint, EventId, SourceLoc, TaskId, add_worker_place};

/// Collect async suspend points from MIR (`Yield` terminators).
pub fn collect_async_points_from_mir<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<AsyncPoint> {
    let fn_name = tcx.def_path_str(def_id);
    let mut points = Vec::new();
    for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
        if bb.is_cleanup || bb.is_empty_unreachable() {
            continue;
        }
        if let Some(ref term) = bb.terminator {
            if let rustc_middle::mir::TerminatorKind::Yield { .. } = &term.kind {
                let loc = SourceLoc {
                    file: None,
                    line: None,
                    fn_name: Some(fn_name.clone()),
                    bb: Some(bb_idx.index()),
                };
                points.push(AsyncPoint::new(points.len(), None, loc));
            }
        }
    }
    points
}

/// Wire async task lifecycle subnets onto an existing net / CFG fragment.
pub struct AsyncNetBuilder<'a> {
    pub net: &'a mut Net,
    pub worker_place: PlaceId,
    pub worker_count: u64,
    pub next_task_id: usize,
    pub next_event_id: usize,
}

impl<'a> AsyncNetBuilder<'a> {
    pub fn new(net: &'a mut Net, worker_count: u64) -> Self {
        let worker_place = add_worker_place(net, worker_count);
        Self {
            net,
            worker_place,
            worker_count,
            next_task_id: 0,
            next_event_id: 0,
        }
    }

    pub fn with_existing_worker(
        net: &'a mut Net,
        worker_place: PlaceId,
        worker_count: u64,
    ) -> Self {
        Self {
            net,
            worker_place,
            worker_count,
            next_task_id: 0,
            next_event_id: 0,
        }
    }

    pub fn alloc_task_id(&mut self) -> TaskId {
        let id = TaskId::new(self.next_task_id);
        self.next_task_id += 1;
        id
    }

    pub fn alloc_event_id(&mut self) -> EventId {
        let id = EventId::new(self.next_event_id);
        self.next_event_id += 1;
        id
    }

    pub fn add_spawn_transition(
        &mut self,
        task_id: TaskId,
        from_place: PlaceId,
        to_place: PlaceId,
        p_ready: PlaceId,
        name: &str,
    ) -> TransitionId {
        let t = self.net.add_transition(make_transition(
            format!("{}_spawn_{}", name, task_id.index()),
            AsyncTransitionKind::Spawn {
                task_id: task_id.index(),
            },
        ));
        self.net.add_input_arc(from_place, t, 1);
        self.net.add_output_arc(to_place, t, 1);
        self.net.add_output_arc(p_ready, t, 1);
        t
    }

    pub fn add_poll_transition(
        &mut self,
        task_id: TaskId,
        p_ready: PlaceId,
        p_running: PlaceId,
    ) -> TransitionId {
        let t = self.net.add_transition(make_transition(
            format!("poll_{}", task_id.index()),
            AsyncTransitionKind::Poll {
                task_id: task_id.index(),
            },
        ));
        self.net.add_input_arc(p_ready, t, 1);
        self.net.add_input_arc(self.worker_place, t, 1);
        self.net.add_output_arc(p_running, t, 1);
        t
    }

    pub fn add_await_ready_transition(
        &mut self,
        task_id: TaskId,
        await_point: usize,
        p_running: PlaceId,
        seg_from: PlaceId,
        seg_to: PlaceId,
    ) -> TransitionId {
        let t = self.net.add_transition(make_transition(
            format!("await_ready_{}_{}", task_id.index(), await_point),
            AsyncTransitionKind::AwaitReady {
                task_id: task_id.index(),
                await_point,
            },
        ));
        self.net.add_input_arc(p_running, t, 1);
        self.net.add_output_arc(p_running, t, 1);
        self.net.add_input_arc(seg_from, t, 1);
        self.net.add_output_arc(seg_to, t, 1);
        t
    }

    pub fn add_await_pending_transition(
        &mut self,
        task_id: TaskId,
        await_point: usize,
        p_running: PlaceId,
        p_blocked: PlaceId,
        seg_from: PlaceId,
        event_id: Option<EventId>,
    ) -> TransitionId {
        let t = self.net.add_transition(make_transition(
            format!("await_pending_{}_{}", task_id.index(), await_point),
            AsyncTransitionKind::AwaitPending {
                task_id: task_id.index(),
                await_point,
                event_id: event_id.map(|e| e.index()),
            },
        ));
        self.net.add_input_arc(p_running, t, 1);
        self.net.add_output_arc(p_blocked, t, 1);
        self.net.add_output_arc(self.worker_place, t, 1);
        self.net.add_input_arc(seg_from, t, 1);
        t
    }

    pub fn add_wake_transition(
        &mut self,
        task_id: TaskId,
        event_id: EventId,
        p_blocked: PlaceId,
        p_ready: PlaceId,
    ) -> TransitionId {
        let t = self.net.add_transition(make_transition(
            format!("wake_{}_{}", task_id.index(), event_id.index()),
            AsyncTransitionKind::Wake {
                task_id: task_id.index(),
                event_id: event_id.index(),
            },
        ));
        self.net.add_input_arc(p_blocked, t, 1);
        self.net.add_output_arc(p_ready, t, 1);
        t
    }

    pub fn add_done_transition(
        &mut self,
        task_id: TaskId,
        p_running: PlaceId,
        p_completed: PlaceId,
        seg_from: PlaceId,
    ) -> TransitionId {
        let t = self.net.add_transition(make_transition(
            format!("done_{}", task_id.index()),
            AsyncTransitionKind::Done {
                task_id: task_id.index(),
            },
        ));
        self.net.add_input_arc(p_running, t, 1);
        self.net.add_output_arc(p_completed, t, 1);
        self.net.add_output_arc(self.worker_place, t, 1);
        self.net.add_input_arc(seg_from, t, 1);
        t
    }

    pub fn add_join_transition(
        &mut self,
        task_id: TaskId,
        from_place: PlaceId,
        to_place: PlaceId,
        p_completed: PlaceId,
        name: &str,
    ) -> TransitionId {
        let t = self.net.add_transition(make_transition(
            format!("{}_join_{}", name, task_id.index()),
            AsyncTransitionKind::Join {
                task_id: task_id.index(),
            },
        ));
        self.net.add_input_arc(from_place, t, 1);
        self.net.add_input_arc(p_completed, t, 1);
        self.net.add_output_arc(to_place, t, 1);
        t
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transition::make_transition;
    use crate::translate::async_ppn::add_task_lifecycle_places;
    use rust_petri_net_analysis::net::structure::{Place, PlaceType};

    #[test]
    fn async_spawn_join_basic() {
        let mut net = Net::empty();
        let main_start = net.add_place(Place::new(
            "main_start",
            1,
            1,
            PlaceType::FunctionStart,
            String::new(),
        ));
        let main_end = net.add_place(Place::new(
            "main_end",
            0,
            1,
            PlaceType::FunctionEnd,
            String::new(),
        ));
        let task_start = net.add_place(Place::new(
            "task_start",
            0,
            1,
            PlaceType::FunctionStart,
            String::new(),
        ));
        let task_end = net.add_place(Place::new(
            "task_end",
            0,
            1,
            PlaceType::FunctionEnd,
            String::new(),
        ));

        let tp = add_task_lifecycle_places(&mut net, TaskId::new(0), &[], false);

        let mut builder = AsyncNetBuilder::new(&mut net, 1);
        let task_id = TaskId::new(0);

        let _t_spawn = builder.net.add_transition(make_transition(
            "spawn_0",
            AsyncTransitionKind::Spawn { task_id: 0 },
        ));
        builder.net.add_input_arc(main_start, _t_spawn, 1);
        builder.net.add_output_arc(tp.ready, _t_spawn, 1);

        let _t_poll = builder.add_poll_transition(task_id, tp.ready, tp.running);
        builder.net.add_output_arc(task_start, _t_poll, 1);

        let _t_done = builder.add_done_transition(task_id, tp.running, tp.completed, task_end);

        let _t_join =
            builder.add_join_transition(task_id, main_start, main_end, tp.completed, "main");
        builder.net.add_input_arc(main_start, _t_join, 1);

        drop(builder);
        let place_names: Vec<_> = net.places.iter().map(|p| p.name.as_str()).collect();
        assert!(place_names.iter().any(|n| *n == "task_0_ready"));
        assert!(place_names.iter().any(|n| *n == "task_0_running"));
        assert!(place_names.iter().any(|n| *n == "task_0_completed"));
        assert!(place_names.iter().any(|n| *n == "async_worker"));

        let trans_names: Vec<_> = net.transitions.iter().map(|t| t.name.as_str()).collect();
        assert!(trans_names.iter().any(|n| n.contains("poll_0")));
        assert!(trans_names.iter().any(|n| n.contains("done_")));
    }
}
