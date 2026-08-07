use crate::memory::pointsto::AliasId;
use crate::translate::callgraph::{CallGraph, CallGraphNode, InstanceId};
use crate::util::format_name;
use petgraph::csr::IndexType;
use petgraph::visit::{IntoNodeReferences, NodeRef};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    Body, Local, LocalKind, Location, Operand, Place, ProjectionElem, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind,
};
use rustc_middle::ty::{Instance, TyCtxt, TyKind};
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
pub struct UnsafeBlockInfo {
    pub span: String,
    pub block: usize,
    pub locations: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub enum UnsafeOperation {
    Read(String),
    Write(String),
    Deref(String),
    AddrOf(String),
    Cast(String),
    Call(String),
}

#[derive(Debug, Clone, Serialize)]
pub struct UnsafePlaceInfo {
    pub local: usize,
    pub ty_string: String,
    pub span: String,
    pub is_param: bool,
    pub operations: Vec<UnsafeOperation>,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct UnsafeInfo {
    pub is_unsafe_fn: bool,
    pub unsafe_blocks: Vec<UnsafeBlockInfo>,
    pub unsafe_places: FxHashMap<usize, UnsafePlaceInfo>,
}

pub struct UnsafeData {
    pub unsafe_places: FxHashMap<AliasId, String>,
}

impl Default for UnsafeData {
    fn default() -> Self {
        Self {
            unsafe_places: FxHashMap::default(),
        }
    }
}

impl UnsafeData {
    pub fn get_or_insert(&mut self, alias_id: AliasId, span: String) {
        for (id, old_span) in self.unsafe_places.iter() {
            if *id == alias_id && *old_span == span {
                return;
            }
        }
        self.unsafe_places.insert(alias_id, span);
    }
}

pub struct UnsafeDataInfo {
    pub local: Local,

    pub span: String,
}

impl UnsafeInfo {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn collect<'tcx>(
        instance: Instance<'tcx>,
        instance_id: Option<InstanceId>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> (UnsafeData, UnsafeInfo) {
        let mut collector = UnsafeCollector::new(instance, instance_id, body, tcx);
        let unsafe_data = collector.analyze();
        (unsafe_data, collector.finish())
    }
}

struct UnsafeCollector<'a, 'tcx> {
    #[allow(unused)]
    instance: Instance<'tcx>,
    instance_id: Option<InstanceId>,
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    info: UnsafeInfo,
}

impl<'a, 'tcx> UnsafeCollector<'a, 'tcx> {
    fn new(
        instance: Instance<'tcx>,
        instance_id: Option<InstanceId>,
        body: &'a Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Self {
            instance,
            instance_id,
            body,
            tcx,
            info: UnsafeInfo::new(),
        }
    }

    fn analyze(&mut self) -> UnsafeData {
        let mut unsafe_data = UnsafeData::default();

        self.collect_unsafe_locals(&mut unsafe_data);

        self.info.is_unsafe_fn = self.check_unsafe_fn();
        self.visit_body(self.body);
        unsafe_data
    }

    fn collect_unsafe_locals(&mut self, unsafe_data: &mut UnsafeData) {
        for (local, local_decl) in self.body.local_decls.iter_enumerated() {
            let ty = local_decl.ty;
            if matches!(ty.kind(), TyKind::RawPtr(..)) {
                let info = UnsafePlaceInfo {
                    local: local.index(),
                    ty_string: ty.to_string(),
                    span: format!("{:?}", local_decl.source_info.span),
                    is_param: matches!(self.body.local_kind(local), LocalKind::Arg),
                    operations: Vec::new(),
                };
                let unsafe_data_info = UnsafeDataInfo {
                    local: local,
                    span: format!("{:?}", local_decl.source_info.span),
                };
                self.info.unsafe_places.insert(local.index(), info);
                match self.instance_id {
                    Some(instance_id) => {
                        unsafe_data
                            .get_or_insert(AliasId::new(instance_id, local), unsafe_data_info.span);
                    }
                    None => {}
                }
            }
        }
    }

    pub fn finish(self) -> UnsafeInfo {
        self.info
    }

    fn check_unsafe_fn(&self) -> bool {
        self.info
            .unsafe_places
            .values()
            .any(|place| !place.is_param)
    }

    fn is_unsafe_operation(&mut self, statement: &Statement<'tcx>, location: Location) -> bool {
        match &statement.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let loc_str = format!("{:?}", location);

                if self.info.unsafe_places.contains_key(&place.local.index()) {
                    if let Some(place_info) = self.info.unsafe_places.get_mut(&place.local.index())
                    {
                        place_info
                            .operations
                            .push(UnsafeOperation::Write(loc_str.clone()));
                    }
                }

                match rvalue {
                    Rvalue::Use(operand, _) => {
                        self.check_operand_usage(operand, &loc_str);
                        self.is_unsafe_operand(operand)
                    }
                    Rvalue::Ref(_, _, place) => {
                        if self.info.unsafe_places.contains_key(&place.local.index()) {
                            if let Some(place_info) =
                                self.info.unsafe_places.get_mut(&place.local.index())
                            {
                                place_info.operations.push(UnsafeOperation::AddrOf(loc_str));
                            }
                            true
                        } else {
                            false
                        }
                    }
                    Rvalue::Cast(_, operand, _) => {
                        if self.is_unsafe_operand(operand) {
                            if let Operand::Copy(place) | Operand::Move(place) = operand {
                                if let Some(place_info) =
                                    self.info.unsafe_places.get_mut(&place.local.index())
                                {
                                    place_info.operations.push(UnsafeOperation::Cast(loc_str));
                                }
                            }
                            true
                        } else {
                            false
                        }
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn check_operand_usage(&mut self, operand: &Operand<'tcx>, loc_str: &str) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if self.info.unsafe_places.contains_key(&place.local.index()) {
                    if let Some(place_info) = self.info.unsafe_places.get_mut(&place.local.index())
                    {
                        place_info
                            .operations
                            .push(UnsafeOperation::Read(loc_str.to_string()));

                        if place
                            .projection
                            .iter()
                            .any(|elem| matches!(elem, ProjectionElem::Deref))
                        {
                            place_info
                                .operations
                                .push(UnsafeOperation::Deref(loc_str.to_string()));
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn is_unsafe_place(&self, place: Place<'tcx>) -> bool {
        place
            .projection
            .iter()
            .any(|elem| matches!(elem, ProjectionElem::Deref))
            && self.info.unsafe_places.contains_key(&place.local.index())
    }

    #[allow(dead_code)]
    fn is_unsafe_rvalue(&self, rvalue: &Rvalue<'tcx>) -> bool {
        match rvalue {
            Rvalue::Ref(_, _, place) => self.is_unsafe_place(*place),
            Rvalue::Cast(_, operand, _) => self.is_unsafe_operand(operand),
            _ => false,
        }
    }

    fn is_unsafe_operand(&self, operand: &Operand<'tcx>) -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.is_unsafe_place(*place),
            _ => false,
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for UnsafeCollector<'a, 'tcx> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        if self.is_unsafe_operation(statement, location) {
            if let Some(block_info) = self
                .info
                .unsafe_blocks
                .iter_mut()
                .find(|block| block.block.index() == location.block.index())
            {
                block_info.locations.push(format!("{:?}", location));
            } else {
                let unsafe_block = UnsafeBlockInfo {
                    span: format!("{:?}", statement.source_info.span),
                    block: location.block.index(),
                    locations: vec![format!("{:?}", location)],
                };
                self.info.unsafe_blocks.push(unsafe_block);
            }
        }

        self.super_statement(statement, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match terminator.kind {
            TerminatorKind::Call { ref func, .. } => {
                let func_ty = func.ty(self.body, self.tcx);
                if let TyKind::FnDef(def_id, _) = func_ty.kind() {
                    if self.tcx.is_mir_available(*def_id) {
                        if def_id.is_local() {
                            // TODO: Need a new way to detect `unsafe` fn bodies; skip until API lands.
                            // let hir_id = self.tcx.local_def_id_to_hir_id(def_id.expect_local());
                            // if matches!(
                            //     self.tcx
                            //         .hir()
                            //         .fn_sig_by_hir_id(hir_id)
                            //         .unwrap()
                            //         .header
                            //         .safety,
                            //     rustc_hir::Safety::Unsafe
                            // ) {
                            //     self.info.unsafe_blocks.push(UnsafeBlockInfo {
                            //         span: format!("{:?}", terminator.source_info.span),
                            //         block: location.block.index(),
                            //         locations: vec![format!("{:?}", location)],
                            //     });
                            // }
                        }
                    }
                }
            }
            _ => {}
        }

        self.super_terminator(terminator, location);
    }
}

pub struct UnsafeAnalyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    callgraph: &'a CallGraph<'tcx>,
    crate_name: String,
}

impl<'a, 'tcx> UnsafeAnalyzer<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, callgraph: &'a CallGraph<'tcx>, crate_name: String) -> Self {
        Self {
            tcx,
            callgraph,
            crate_name,
        }
    }

    pub fn analyze(&self) -> (FxHashMap<DefId, UnsafeInfo>, UnsafeData) {
        let mut unsafe_info = FxHashMap::default();
        let mut unsafe_data = UnsafeData::default();
        for node_ref in self.callgraph.graph.node_references() {
            if let CallGraphNode::WithBody(instance) = node_ref.weight() {
                let def_id = instance.def_id();
                if def_id.is_local()
                    && format_name(def_id).starts_with(&self.crate_name)
                    && self.tcx.is_mir_available(def_id)
                {
                    // Use instance_mir so pointer analysis and Petri lowering agree on MIR bodies.
                    let body = self.tcx.instance_mir(instance.def);
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

        (unsafe_info, unsafe_data)
    }
}
