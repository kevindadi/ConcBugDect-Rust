//! Async PPN identifiers: `TaskId`, `EventId`.

use std::fmt;

use serde::{Deserialize, Serialize};

/// Logical async task id (`tokio::spawn`, etc.).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TaskId(pub usize);

impl TaskId {
    pub fn new(idx: usize) -> Self {
        Self(idx)
    }

    pub fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for TaskId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "task_{}", self.0)
    }
}

/// Identifier for an awaited event (mutex, channel, …).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct EventId(pub usize);

impl EventId {
    pub fn new(idx: usize) -> Self {
        Self(idx)
    }

    pub fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for EventId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ev_{}", self.0)
    }
}
