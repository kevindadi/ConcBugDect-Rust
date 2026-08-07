//! Async suspension-point abstraction.
//!
//! Mirrors MIR `Yield` / suspend-resume sites or a precomputed suspend list.

use super::ids::EventId;

/// Source-span snapshot.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceLoc {
    pub file: Option<String>,
    pub line: Option<u32>,
    pub fn_name: Option<String>,
    pub bb: Option<usize>,
}

/// Async suspend site corresponding to `.await` in the CFG.
#[derive(Debug, Clone)]
pub struct AsyncPoint {
    pub id: usize,
    /// Awaited resource when known (otherwise a generic `EventId`).
    pub event: Option<EventId>,
    pub loc: SourceLoc,
}

impl AsyncPoint {
    pub fn new(id: usize, event: Option<EventId>, loc: SourceLoc) -> Self {
        Self { id, event, loc }
    }

    /// Constructed from precomputed lists without event detail.
    pub fn simple(id: usize, bb: usize, fn_name: impl Into<String>) -> Self {
        Self {
            id,
            event: None,
            loc: SourceLoc {
                file: None,
                line: None,
                fn_name: Some(fn_name.into()),
                bb: Some(bb),
            },
        }
    }
}
