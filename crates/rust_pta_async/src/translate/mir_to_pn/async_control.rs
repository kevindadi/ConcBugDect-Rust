//! Async control: `handle_async_spawn`, `handle_async_join`.

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Operand;
use rustc_span::Spanned;
use rust_petri_net_analysis::memory::pointsto::AliasId;
use rust_petri_net_analysis::net::{Net, PlaceId, TransitionId};

use crate::transition::{AsyncTransitionKind, make_transition, tag_transition};
use crate::translate::async_context::AsyncTranslateContext;

/// Context for wiring async spawn/join into an existing sync-translated net fragment.
pub struct AsyncControlCtx<'a> {
    pub net: &'a mut Net,
    pub async_ctx: &'a mut AsyncTranslateContext,
    pub functions: &'a FxHashMap<DefId, (PlaceId, PlaceId)>,
    pub instance_id: rust_petri_net_analysis::translate::callgraph::InstanceId,
}

impl AsyncControlCtx<'_> {
    pub fn connect_to_target(
        net: &mut Net,
        bb_end: TransitionId,
        target_bb_start: PlaceId,
    ) {
        net.add_output_arc(target_bb_start, bb_end, 1);
    }

    pub fn handle_async_spawn(
        &mut self,
        _args: &Box<[Spanned<Operand<'_>>]>,
        target_bb_start: Option<PlaceId>,
        bb_end: TransitionId,
        closure_def_id: Option<DefId>,
    ) {
        let task_id = self.async_ctx.alloc_task_id();
        let worker_place = self.async_ctx.ensure_worker_place(self.net);
        let tp = self.async_ctx.add_task_simple(self.net, task_id);
        if let Some(def_id) = closure_def_id {
            self.async_ctx.register_spawn(def_id, task_id);
        }

        self.net.add_output_arc(tp.ready, bb_end, 1);

        let t_poll = self.net.add_transition(make_transition(
            format!("poll_{}", task_id.index()),
            AsyncTransitionKind::Poll {
                task_id: task_id.index(),
            },
        ));
        self.net.add_input_arc(tp.ready, t_poll, 1);
        self.net.add_input_arc(worker_place, t_poll, 1);
        self.net.add_output_arc(tp.running, t_poll, 1);

        if let Some(closure_def_id) = closure_def_id {
            if let Some((closure_start, closure_end)) = self.functions.get(&closure_def_id).copied()
            {
                self.net.add_output_arc(closure_start, t_poll, 1);
                let t_done = self.net.add_transition(make_transition(
                    format!("done_{}", task_id.index()),
                    AsyncTransitionKind::Done {
                        task_id: task_id.index(),
                    },
                ));
                self.net.add_input_arc(tp.running, t_done, 1);
                self.net.add_input_arc(closure_end, t_done, 1);
                self.net.add_output_arc(tp.completed, t_done, 1);
                self.net.add_output_arc(worker_place, t_done, 1);
            }
        }

        if let Some(transition) = self.net.get_transition_mut(bb_end) {
            tag_transition(
                transition,
                AsyncTransitionKind::Spawn {
                    task_id: task_id.index(),
                },
            );
        }
        if let Some(target) = target_bb_start {
            Self::connect_to_target(self.net, bb_end, target);
        }
    }

    pub fn handle_async_join(
        &mut self,
        join_id: AliasId,
        matching_spawn_def_ids: &[DefId],
        target_bb_start: Option<PlaceId>,
        bb_end: TransitionId,
    ) {
        for spawn_def_id in matching_spawn_def_ids {
            if let Some(task_id) = self.async_ctx.get_task_for_spawn(*spawn_def_id) {
                if let Some(tp) = self.async_ctx.get_task_places(task_id) {
                    self.net.add_input_arc(tp.completed, bb_end, 1);
                }
            }
        }

        let task_id = matching_spawn_def_ids
            .first()
            .and_then(|d| self.async_ctx.get_task_for_spawn(*d))
            .map(|t| t.index())
            .unwrap_or(0);
        if let Some(transition) = self.net.get_transition_mut(bb_end) {
            tag_transition(
                transition,
                AsyncTransitionKind::Join { task_id },
            );
        }
        if let Some(target) = target_bb_start {
            Self::connect_to_target(self.net, bb_end, target);
        }
        let _ = join_id;
    }
}
