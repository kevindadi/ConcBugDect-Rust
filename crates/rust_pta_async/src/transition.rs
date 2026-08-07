//! Async-specific transition kinds (stored in transition names; core `TransitionType` stays sync-only).

use rust_petri_net_analysis::net::structure::{Transition, TransitionType};

/// Async-PPN transition classification (experiment crate only).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AsyncTransitionKind {
    Spawn { task_id: usize },
    Join { task_id: usize },
    Poll { task_id: usize },
    AwaitReady { task_id: usize, await_point: usize },
    AwaitPending {
        task_id: usize,
        await_point: usize,
        event_id: Option<usize>,
    },
    Wake { task_id: usize, event_id: usize },
    Done { task_id: usize },
    Abort { task_id: usize },
}

impl AsyncTransitionKind {
    pub fn tag(self) -> &'static str {
        match self {
            Self::Spawn { .. } => "async_spawn",
            Self::Join { .. } => "async_join",
            Self::Poll { .. } => "async_poll",
            Self::AwaitReady { .. } => "async_await_ready",
            Self::AwaitPending { .. } => "async_await_pending",
            Self::Wake { .. } => "async_wake",
            Self::Done { .. } => "async_done",
            Self::Abort { .. } => "async_abort",
        }
    }
}

pub fn make_transition(name: impl Into<String>, kind: AsyncTransitionKind) -> Transition {
    let base = name.into();
    Transition::new_with_transition_type(
        format!("{}:{}", kind.tag(), base),
        TransitionType::Function,
    )
}

pub fn tag_transition(transition: &mut Transition, kind: AsyncTransitionKind) {
    if !transition.name.contains(':') {
        transition.name = format!("{}:{}", kind.tag(), transition.name);
    }
    transition.transition_type = TransitionType::Function;
}
