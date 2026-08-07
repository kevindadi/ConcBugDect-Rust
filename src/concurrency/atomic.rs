extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_middle;

use once_cell::sync::Lazy;
use petgraph::visit::{IntoNodeReferences, NodeRef};
use regex::Regex;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::StatementKind;
use rustc_middle::mir::{
    Body, Local, Location, Operand, PlaceElem, Terminator, TerminatorKind, visit::Visitor,
};
use rustc_middle::ty::{self, GenericArg, Instance, List, Ty, TyCtxt, TyKind};
use serde_json::json;

use crate::memory::pointsto::AliasId;
use crate::translate::callgraph::{CallGraph, CallGraphNode, InstanceId};
use rustc_middle::mir::PlaceRef;

fn extract_array_index(place: PlaceRef<'_>) -> Option<u64> {
    if place
        .projection
        .iter()
        .any(|e| matches!(e, PlaceElem::Index(_)))
    {
        return None;
    }
    place.projection.iter().rev().find_map(|elem| {
        if let PlaceElem::ConstantIndex { offset, .. } = elem {
            Some(*offset)
        } else {
            None
        }
    })
}
use crate::util::format_name;

static ATOMIC_PTR_STORE: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"^(std|core)::sync::atomic::AtomicPtr::<.*>::store").unwrap());

pub fn is_atomic_ptr_store<'tcx>(
    def_id: DefId,
    substs: &'tcx List<GenericArg<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let path = tcx.def_path_str_with_args(def_id, substs);
    ATOMIC_PTR_STORE.is_match(&path)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AtomicApi {
    Read,
    Write,
    ReadWrite,
}

pub fn atomic_api_from_name(fn_name: &str) -> Option<AtomicApi> {
    let last_segment = fn_name.rsplit("::").next().unwrap_or(fn_name);
    match last_segment {
        "load" => Some(AtomicApi::Read),
        "store" => Some(AtomicApi::Write),
        "compare_exchange" | "fetch_add" | "fetch_sub" | "fetch_and" | "fetch_or" | "fetch_xor"
        | "swap" => Some(AtomicApi::ReadWrite),
        _ => None,
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum AtomicOrdering {
    Relaxed,
    Release,
    Acquire,
    AcqRel,
    SeqCst,
}

impl AtomicOrdering {
    pub fn from_u32(value: u32) -> Self {
        match value {
            0 => AtomicOrdering::Relaxed,
            1 => AtomicOrdering::Release,
            2 => AtomicOrdering::Acquire,
            3 => AtomicOrdering::AcqRel,
            4 => AtomicOrdering::SeqCst,
            _ => AtomicOrdering::SeqCst,
        }
    }
    pub fn from_u128(value: u128) -> Self {
        match value {
            0 => AtomicOrdering::Relaxed,
            1 => AtomicOrdering::Release,
            2 => AtomicOrdering::Acquire,
            3 => AtomicOrdering::AcqRel,
            4 => AtomicOrdering::SeqCst,
            _ => AtomicOrdering::SeqCst,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AtomicOperation {
    pub api: AtomicApi,
    pub ordering: AtomicOrdering,
    pub location: String,
}

#[derive(Debug, Clone)]
pub struct AtomicVarInfo {
    pub var_type: String,
    pub instance_id: InstanceId,
    pub local_id: Local,
    pub array_index: Option<u64>,
    pub span: String,
    pub operations: Vec<AtomicOperation>,
}

impl AtomicVarInfo {
    pub fn get_alias_id(&self) -> AliasId {
        let mut id = AliasId::new(self.instance_id, self.local_id);
        id.array_index = self.array_index;
        id
    }
}

pub type AtomicVarMap = FxHashMap<String, AtomicVarInfo>;

pub struct AtomicCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    callgraph: &'a CallGraph<'tcx>,
    crate_name: String,
    pub atomic_vars: AtomicVarMap,
}

impl<'a, 'tcx> AtomicCollector<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, callgraph: &'a CallGraph<'tcx>, crate_name: String) -> Self {
        Self {
            tcx,
            callgraph,
            crate_name,
            atomic_vars: AtomicVarMap::default(),
        }
    }

    pub fn analyze(&mut self) -> AtomicVarMap {
        for node_ref in self.callgraph.graph.node_references() {
            if let CallGraphNode::WithBody(instance) = node_ref.weight() {
                let def_id = instance.def_id();

                if def_id.is_local() && format_name(def_id).starts_with(&self.crate_name) {
                    if self.tcx.is_mir_available(def_id) {
                        // Use instance_mir so pointer analysis and Petri lowering agree on MIR bodies.
                        let body = self.tcx.instance_mir(instance.def);
                        self.collect_atomic_vars(instance, body);
                    }
                }
            }
        }
        self.atomic_vars.clone()
    }

    fn collect_atomic_vars(&mut self, instance: &Instance<'tcx>, body: &Body<'tcx>) {
        for (local, local_decl) in body.local_decls.iter_enumerated() {
            let ty = local_decl.ty;
            if self.is_atomic_type(ty) && !ty.to_string().contains("Ordering") {
                let var_name = format!(
                    "{}_{}",
                    self.tcx.def_path_str(instance.def_id()),
                    local.index()
                );
                let info = AtomicVarInfo {
                    var_type: ty.to_string(),
                    instance_id: self.callgraph.instance_to_index(instance).unwrap(),
                    local_id: local,
                    array_index: None,
                    span: format!("{:?}", local_decl.source_info.span),
                    operations: Vec::new(),
                };
                self.atomic_vars.insert(var_name, info);
            }
        }

        let mut visitor = AtomicVisitor {
            instance: *instance,
            instance_id: self.callgraph.instance_to_index(instance).unwrap(),
            body,
            tcx: self.tcx,
            atomic_vars: &mut self.atomic_vars,
        };
        visitor.visit_body(body);
    }

    fn is_atomic_type(&self, ty: Ty<'tcx>) -> bool {
        if let TyKind::Adt(adt_def, _) = ty.kind() {
            let path = self.tcx.def_path_str(adt_def.did());
            path.contains("::sync::atomic::")
        } else {
            false
        }
    }

    pub fn to_json_pretty(&self) -> Result<(), serde_json::Error> {
        if self.atomic_vars.is_empty() {
            log::info!("No atomic variables found");
        } else {
            for (var_name, info) in self.atomic_vars.iter() {
                log::info!(
                    "Atomic Variable {}:\n{}",
                    var_name,
                    serde_json::to_string_pretty(&json!({
                        "type": info.var_type,
                        "defined_at": info.span,
                        "operations": info.operations
                            .iter()
                            .map(|op| json!({
                                "api": format!("{:?}", op.api),
                                "ordering": format!("{:?}", op.ordering),
                                "location": op.location
                            }))
                            .collect::<Vec<_>>()
                    }))
                    .unwrap()
                );
            }
        }
        Ok(())
    }
}

struct AtomicVisitor<'a, 'tcx> {
    instance: Instance<'tcx>,
    instance_id: InstanceId,
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    pub atomic_vars: &'a mut AtomicVarMap,
}

impl<'a, 'tcx> Visitor<'tcx> for AtomicVisitor<'a, 'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            let func_ty = func.ty(self.body, self.tcx);
            if let TyKind::FnDef(def_id, _) = func_ty.kind() {
                let fn_name = self.tcx.def_path_str(*def_id);

                let api = atomic_api_from_name(&fn_name);

                if let Some(api) = api {
                    log::debug!("Found atomic operation: {:?} in {}", api, fn_name);

                    if let Some(arg) = args.get(0) {
                        if let Operand::Move(first_place) | Operand::Copy(first_place) = &arg.node {
                            let array_index = extract_array_index(first_place.as_ref());
                            let var_name = format!(
                                "{}_{}_{}",
                                self.tcx.def_path_str(self.instance.def_id()),
                                first_place.local.index(),
                                array_index
                                    .map(|i| i.to_string())
                                    .unwrap_or_else(|| "n".to_string())
                            );
                            let first_place_ty = &self.body.local_decls[first_place.local].ty;

                            log::debug!("Processing atomic variable: {}", var_name.clone());

                            let ordering_idx = match api {
                                AtomicApi::Read => 1,
                                AtomicApi::Write => 2,
                                AtomicApi::ReadWrite => args.len() - 1,
                            };

                            if let Some(arg) = args.get(ordering_idx) {
                                log::debug!("Found ordering argument: {:?}", arg);
                                match &arg.node {
                                    Operand::Constant(c) => {
                                        log::debug!("Found constant: {:?}", c);
                                        if let Some(val) = c.const_.try_to_scalar() {
                                            let ordering_val = val.to_u32().unwrap();
                                            log::debug!(
                                                "Found ordering value: {:?}",
                                                AtomicOrdering::from_u32(ordering_val)
                                            );
                                            if let Some(info) = self.atomic_vars.get_mut(&var_name)
                                            {
                                                log::debug!(
                                                    "Found ordering value: {}",
                                                    ordering_val
                                                );
                                                let op = AtomicOperation {
                                                    api,
                                                    ordering: AtomicOrdering::from_u32(
                                                        ordering_val,
                                                    ),
                                                    location: format!(
                                                        "{:?}",
                                                        self.body.source_info(location).span
                                                    ),
                                                };
                                                info.operations.push(op.clone());
                                                log::debug!("Added operation: {:?}", op);
                                            }
                                        }
                                    }
                                    Operand::Move(ordering_place) => {
                                        log::debug!("Found move operand: {:?}", ordering_place);
                                        let local_decl =
                                            &self.body.local_decls[ordering_place.local];

                                        let mut ordering = AtomicOrdering::SeqCst;
                                        if let ty::TyKind::Adt(adt_def, _) = local_decl.ty.kind() {
                                            if adt_def.is_enum() {
                                                for (_, data) in
                                                    self.body.basic_blocks.iter_enumerated()
                                                {
                                                    for (_, statement) in
                                                        data.statements.iter().enumerate()
                                                    {
                                                        if let StatementKind::Assign(box (
                                                            lhs,
                                                            rhs,
                                                        )) = &statement.kind
                                                        {
                                                            if lhs.local.index()
                                                                == ordering_place.local.index()
                                                            {
                                                                let rvalue_str =
                                                                    format!("{:?}", rhs);
                                                                ordering = match rvalue_str
                                                                    .split("::")
                                                                    .last()
                                                                {
                                                                    Some("Relaxed") => {
                                                                        AtomicOrdering::Relaxed
                                                                    }
                                                                    Some("Release") => {
                                                                        AtomicOrdering::Release
                                                                    }
                                                                    Some("Acquire") => {
                                                                        AtomicOrdering::Acquire
                                                                    }
                                                                    Some("AcqRel") => {
                                                                        AtomicOrdering::AcqRel
                                                                    }
                                                                    Some("SeqCst") => {
                                                                        AtomicOrdering::SeqCst
                                                                    }
                                                                    _ => AtomicOrdering::SeqCst,
                                                                }
                                                            }
                                                        }
                                                    }
                                                }

                                                if let Some(info) =
                                                    self.atomic_vars.get_mut(&var_name)
                                                {
                                                    let op = AtomicOperation {
                                                        api,
                                                        ordering,
                                                        location: format!(
                                                            "{:?}",
                                                            self.body.source_info(location).span
                                                        ),
                                                    };
                                                    info.operations.push(op);
                                                } else {
                                                    let op = AtomicOperation {
                                                        api,
                                                        ordering,
                                                        location: format!(
                                                            "{:?}",
                                                            self.body.source_info(location).span
                                                        ),
                                                    };
                                                    self.atomic_vars.insert(
                                                        var_name,
                                                        AtomicVarInfo {
                                                            var_type: first_place_ty.to_string(),
                                                            instance_id: self.instance_id,
                                                            local_id: first_place.local,
                                                            array_index,
                                                            span: format!(
                                                                "{:?}",
                                                                self.body
                                                                    .source_info(location)
                                                                    .span
                                                            ),
                                                            operations: vec![op],
                                                        },
                                                    );
                                                }
                                            }
                                        }
                                    }

                                    _ => {
                                        log::error!("Unknown operand: {:?}", arg);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        self.super_terminator(terminator, location);
    }
}
