//! Whole-program analysis: API recognition, the call graph, entry policy, and
//! synchronization resources. Net construction stays in `translate`.

pub mod api_patterns;
pub mod callgraph;
pub mod entry_plan;
pub mod memory;
pub mod primitives;
pub mod sync;
pub mod unsafe_scan;
