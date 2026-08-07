//! PPN extension: transition labels / op kinds.
//!
//! Classifies read/write/lock/unlock/spawn/join/await_ready/await_pending/wake/done/abort, etc.

use serde::{Deserialize, Serialize};

/// High-level operation tag for async PPN / race filtering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum OpKind {
    Read,
    Write,
    Lock,
    Unlock,
    Spawn,
    Join,
    AwaitReady,
    AwaitPending,
    Wake,
    Done,
    Abort,
    /// Scheduler poll step: ready → running.
    Poll,
    /// Ordinary control flow (non-async).
    Goto,
    Function,
    Return,
    /// Fallback / uncategorized.
    Other,
}

impl Default for OpKind {
    fn default() -> Self {
        OpKind::Other
    }
}

impl OpKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            OpKind::Read => "read",
            OpKind::Write => "write",
            OpKind::Lock => "lock",
            OpKind::Unlock => "unlock",
            OpKind::Spawn => "spawn",
            OpKind::Join => "join",
            OpKind::AwaitReady => "await_ready",
            OpKind::AwaitPending => "await_pending",
            OpKind::Wake => "wake",
            OpKind::Done => "done",
            OpKind::Abort => "abort",
            OpKind::Poll => "poll",
            OpKind::Goto => "goto",
            OpKind::Function => "function",
            OpKind::Return => "return",
            OpKind::Other => "other",
        }
    }
}
