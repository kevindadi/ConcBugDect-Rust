//! Async-PPN extension: Tokio-like cooperative async/await scheduling.
//!
//! Goals:
//! 1. Restrict semantic interleavings to `.await` suspension points.
//! 2. Enable async-specific bug checks.

pub mod async_point;
pub mod ids;
pub mod labels;
pub mod meta;
pub mod model;

pub use async_point::{AsyncPoint, SourceLoc};
pub use ids::{EventId, TaskId};
pub use labels::OpKind;
pub use meta::TransitionMeta;
pub use model::{
    AsyncSchedulerState, TaskLifecyclePlaces, add_task_lifecycle_places, add_worker_place,
};
