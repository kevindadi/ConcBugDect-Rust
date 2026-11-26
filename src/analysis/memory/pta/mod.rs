//! Field-sensitive, k-CFA, inclusion-based pointer analysis.
//! The solver core is rustc-free; MIR lowering and library models sit on top.
//! It does not emit Petri-net arcs.

pub mod adapter;
pub mod analysis;
pub mod builder;
pub mod constraint;
pub mod context;
pub mod differential;
pub mod intern;
pub mod interproc;
pub mod loc;
pub mod model;
pub mod result;
pub mod solver;
mod typeutil;

pub use adapter::PtaAliasAnalysis;
pub use analysis::PointerAnalysis;
pub use builder::{PendingCall, PlaceWalk, ProjKind, build_body};
pub use constraint::{Constraint, ConstraintSet};
pub use context::{CallSite, Context, ContextPolicy, KCallSite};
pub use differential::{alias_pairs, alias_relation_is_superset, points_to_is_superset};
pub use interproc::{FuncMap, bind_call_edges};
pub use loc::{AbstractLoc, AllocSite, CiKey, FieldPath, LocArena, LocId, ProjElem};
pub use model::{CallModel, CallNodes, ModelRegistry};
pub use result::PointsToResult;
pub use solver::{PointsTo, Solver};
