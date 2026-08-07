//! PPN extension: transition metadata.
//!
//! Each transition may carry `{file, line, fn, bb, task_id, optional awaited_event_id}`.

use serde::{Deserialize, Serialize};

use super::ids::{EventId, TaskId};

/// Metadata attached to transitions for provenance / async scheduling.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TransitionMeta {
    pub file: Option<String>,
    pub line: Option<u32>,
    pub fn_name: Option<String>,
    pub bb: Option<usize>,
    pub task_id: Option<TaskId>,
    pub awaited_event_id: Option<EventId>,
}

impl TransitionMeta {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_file(mut self, file: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self
    }

    pub fn with_line(mut self, line: u32) -> Self {
        self.line = Some(line);
        self
    }

    pub fn with_fn(mut self, fn_name: impl Into<String>) -> Self {
        self.fn_name = Some(fn_name.into());
        self
    }

    pub fn with_bb(mut self, bb: usize) -> Self {
        self.bb = Some(bb);
        self
    }

    pub fn with_task(mut self, task_id: TaskId) -> Self {
        self.task_id = Some(task_id);
        self
    }

    pub fn with_awaited_event(mut self, event_id: EventId) -> Self {
        self.awaited_event_id = Some(event_id);
        self
    }
}
