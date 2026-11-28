//! Stages of one analysis run: collect, analyze resources, construct, plan, explore, project.
//! Each stage keeps the order and outputs of the old straight-line driver.
//! Cache lookup and the memory watcher stay in `callback`.

pub mod analyze;
pub mod collect;
pub mod construct;
pub mod explore;
pub mod plan;
pub mod project;
pub mod slices;

use std::path::PathBuf;

use rustc_middle::ty::{Instance, TyCtxt};
use unipn::analysis::pt::reachability::StateGraph;
use unipn::analysis::pt::reduce::ReductionTrace;
use unipn::net::Marking;
use unipn::pt::PtNet;

use crate::analysis::callgraph::CallGraph;
use crate::options::Options;
use slices::SliceLayout;
use crate::translate::construct::{LibraryRootEntry, PetriNet};
use crate::translate::lower::facts::TranslationProvenance;
pub struct RunCtx<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub options: &'a Options,
    pub crate_name: String,
    pub output_dir: PathBuf,
}

pub struct Collected<'tcx> {
    pub instances: Vec<Instance<'tcx>>,
    pub callgraph: CallGraph<'tcx>,
    /// `--stop-after callgraph`: net construction must not run.
    pub stop: bool,
}

/// `PetriNet` borrows the call graph, so this struct borrows [`Collected`].
pub struct Constructed<'a, 'tcx> {
    pub petri: PetriNet<'a, 'tcx>,
    pub net: PtNet,
    pub marking: Marking,
    pub raw_net: PtNet,
    pub provenance: TranslationProvenance,
    pub library_roots: Vec<LibraryRootEntry>,
}

pub struct SlicePlan {
    pub groups: Vec<Vec<usize>>,
    pub slices: Vec<Vec<usize>>,
}

/// The driver keeps one merged state graph. Per-slice counts stay in
/// `slice_layout`; the old code does not retain a graph per slice.
pub struct SliceOutcome {
    pub state_graph: StateGraph,
    pub slice_layout: Option<SliceLayout>,
}

pub struct Explored {
    pub results: Vec<SliceOutcome>,
    pub reduce_trace: Option<ReductionTrace>,
    pub stop: PhaseStop,
}

/// Why a later phase must not run. `None` means the driver continues.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PhaseStop {
    None,
    AfterPointsTo,
    AfterStateGraph,
}

pub use analyze::analyze_resources;
pub use collect::collect;
pub use construct::construct;
pub use explore::explore;
pub use plan::plan;
pub(crate) use project::handle_visualizations;
pub use project::project;
