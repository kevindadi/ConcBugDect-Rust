//! Whole-program unsafe-block scan. Per-body collection stays in `memory`.

use petgraph::visit::{IntoNodeReferences, NodeRef};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::callgraph::{CallGraph, CallGraphNode};
use crate::analysis::memory::unsafe_memory::{UnsafeData, UnsafeInfo};
use crate::util::format_name;

pub struct UnsafeAnalyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    callgraph: &'a CallGraph<'tcx>,
    crate_name: String,
    bodies_visited: std::cell::Cell<usize>,
}

impl<'a, 'tcx> UnsafeAnalyzer<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, callgraph: &'a CallGraph<'tcx>, crate_name: String) -> Self {
        Self {
            tcx,
            callgraph,
            crate_name,
            bodies_visited: std::cell::Cell::new(0),
        }
    }

    pub fn bodies_visited(&self) -> usize {
        self.bodies_visited.get()
    }

    pub fn analyze(&self) -> (FxHashMap<DefId, UnsafeInfo>, UnsafeData) {
        let mut unsafe_info = FxHashMap::default();
        let mut unsafe_data = UnsafeData::default();
        let mut bodies_visited = 0usize;
        for node_ref in self.callgraph.graph.node_references() {
            if let CallGraphNode::WithBody(instance) = node_ref.weight() {
                let def_id = instance.def_id();
                if def_id.is_local()
                    && format_name(def_id).starts_with(&self.crate_name)
                    && self.tcx.is_mir_available(def_id)
                {
                    // Use instance_mir so pointer analysis and Petri lowering agree on MIR bodies.
                    let body = self.tcx.instance_mir(instance.def);
                    bodies_visited += 1;
                    let instance_id = self.callgraph.instance_to_index(instance);
                    let unsafe_collector =
                        UnsafeInfo::collect(*instance, instance_id, body, self.tcx);
                    unsafe_info.insert(def_id, unsafe_collector.1);
                    unsafe_data
                        .unsafe_places
                        .extend(unsafe_collector.0.unsafe_places);
                }
            }
        }

        self.bodies_visited.set(bodies_visited);
        (unsafe_info, unsafe_data)
    }
}
