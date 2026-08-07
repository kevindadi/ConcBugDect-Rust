extern crate rustc_hir;
extern crate rustc_index;

use std::cmp::{Ordering, PartialOrd};
use std::collections::VecDeque;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    AggregateKind, Body, ConstOperand, Local, Location, Operand, Place, PlaceElem, PlaceRef,
    ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
};
use rustc_span::Spanned;

use rustc_middle::mir::Const;
use rustc_middle::ty::{Instance, TyCtxt, TyKind};

use petgraph::dot::{Config, Dot};
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::{Directed, Direction, Graph};

use crate::concurrency::atomic::is_atomic_ptr_store;
use crate::concurrency::blocking::{CondVarId, LockGuardId};
use crate::concurrency::channel::ChannelId;
use crate::memory::ownership;
use crate::translate::callgraph::{CallGraph, CallGraphNode, CallSiteLocation, InstanceId};
use crate::translate::mir_utils::operand_place;

pub struct Andersen<'a, 'tcx> {
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    pts: PointsToMap<'tcx>,
}

pub type PointsToMap<'tcx> = FxHashMap<ConstraintNode<'tcx>, FxHashSet<ConstraintNode<'tcx>>>;

impl<'a, 'tcx> Andersen<'a, 'tcx> {
    pub fn new(body: &'a Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            body,
            tcx,
            pts: Default::default(),
        }
    }

    pub fn analyze(&mut self) {
        let mut collector = ConstraintGraphCollector::new(self.body, self.tcx);
        collector.visit_body(self.body);
        let mut graph = collector.finish();
        let mut worklist = VecDeque::new();

        for node in graph.nodes() {
            match node {
                ConstraintNode::Place(place) => {
                    graph.add_alloc(place);
                }
                ConstraintNode::Constant(ref constant) => {
                    graph.add_constant(*constant);

                    worklist.push_back(ConstraintNode::ConstantDeref(*constant));
                }
                _ => {}
            }
            worklist.push_back(node);
        }

        for (source, target, weight) in graph.edges() {
            if weight == ConstraintEdge::Address {
                self.pts.entry(target.clone()).or_default().insert(source);
                worklist.push_back(target);
            }
        }

        while let Some(node) = worklist.pop_front() {
            if !self.pts.contains_key(&node) {
                continue;
            }
            for o in self.pts.get(&node).unwrap() {
                for source in graph.store_sources(&node) {
                    if graph.insert_edge(source.clone(), o.clone(), ConstraintEdge::Copy) {
                        worklist.push_back(source);
                    }
                }

                for target in graph.load_targets(&node) {
                    if graph.insert_edge(o.clone(), target, ConstraintEdge::Copy) {
                        worklist.push_back(o.clone());
                    }
                }
            }

            for target in graph.alias_copy_targets(&node) {
                if graph.insert_edge(node.clone(), target, ConstraintEdge::Copy) {
                    worklist.push_back(node.clone());
                }
            }

            for target in graph.copy_targets(&node) {
                if self.union_pts(&target, &node) {
                    worklist.push_back(target);
                }
            }
        }
        self.propagate_points_to();
    }

    fn propagate_points_to(&mut self) {
        let mut field_parent_map = FxHashMap::default();
        for node in self.pts.keys() {
            if let ConstraintNode::Place(place) | ConstraintNode::Alloc(place) = node {
                if !place.projection.is_empty() {
                    let parent = PlaceRef {
                        local: place.local,
                        projection: &[],
                    };
                    field_parent_map.insert(node.clone(), ConstraintNode::Place(parent));
                }
            }
        }
        for (field_node, parent_node) in field_parent_map {
            let to_add: Vec<_> = self
                .pts
                .get(&parent_node)
                .map(|s| s.iter().cloned().collect())
                .unwrap_or_default();
            if !to_add.is_empty() {
                self.pts.entry(field_node).or_default().extend(to_add);
            }
        }
    }

    fn union_pts(&mut self, target: &ConstraintNode<'tcx>, source: &ConstraintNode<'tcx>) -> bool {
        if matches!(target, ConstraintNode::Alloc(_)) {
            return false;
        }
        let to_add: Vec<_> = self.pts.get(source).unwrap().iter().cloned().collect();
        let target_pts = self.pts.get_mut(target).unwrap();
        let old_len = target_pts.len();
        target_pts.extend(to_add);
        old_len != target_pts.len()
    }

    pub fn finish(self) -> FxHashMap<ConstraintNode<'tcx>, FxHashSet<ConstraintNode<'tcx>>> {
        self.pts
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstraintNode<'tcx> {
    Alloc(PlaceRef<'tcx>),
    Place(PlaceRef<'tcx>),
    Constant(Const<'tcx>),
    ConstantDeref(Const<'tcx>),
}

impl<'tcx> std::fmt::Display for ConstraintNode<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintNode::Place(place) => {
                write!(f, "_{}", place.local.as_u32())?;
                if !place.projection.is_empty() {
                    write!(f, "{:?}", place.projection)?;
                }
                Ok(())
            }
            ConstraintNode::Alloc(place) => {
                write!(f, "Alloc(_{}", place.local.as_u32())?;
                if !place.projection.is_empty() {
                    write!(f, "{:?}", place.projection)?;
                }
                write!(f, ")")
            }
            ConstraintNode::Constant(c) => write!(f, "Const({:?})", c),
            ConstraintNode::ConstantDeref(c) => write!(f, "*Const({:?})", c),
        }
    }
}

impl<'tcx> ConstraintNode<'tcx> {
    /// Returns the local variable index if this node refers to a place or alloc.
    pub fn local(&self) -> Option<Local> {
        match self {
            ConstraintNode::Place(p) | ConstraintNode::Alloc(p) => Some(p.local),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstraintEdge {
    Address,
    Copy,
    Load,
    Store,
    AliasCopy,
}

#[derive(Debug)]
enum AccessPattern<'tcx> {
    Ref(PlaceRef<'tcx>),
    Indirect(PlaceRef<'tcx>),
    Direct(PlaceRef<'tcx>),
    Constant(Const<'tcx>),
}

#[derive(Default)]
struct ConstraintGraph<'tcx> {
    graph: Graph<ConstraintNode<'tcx>, ConstraintEdge, Directed>,
    node_map: FxHashMap<ConstraintNode<'tcx>, NodeIndex>,
}

impl<'tcx> ConstraintGraph<'tcx> {
    fn get_or_insert_node(&mut self, node: ConstraintNode<'tcx>) -> NodeIndex {
        if let Some(idx) = self.node_map.get(&node) {
            *idx
        } else {
            let idx = self.graph.add_node(node.clone());
            self.node_map.insert(node, idx);
            idx
        }
    }

    fn get_node(&self, node: &ConstraintNode<'tcx>) -> Option<NodeIndex> {
        self.node_map.get(node).copied()
    }

    fn add_alloc(&mut self, place: PlaceRef<'tcx>) {
        let lhs = ConstraintNode::Place(place);
        let rhs = ConstraintNode::Alloc(place);
        let lhs = self.get_or_insert_node(lhs);
        let rhs = self.get_or_insert_node(rhs);
        self.graph.add_edge(rhs, lhs, ConstraintEdge::Address);
    }

    fn add_constant(&mut self, constant: Const<'tcx>) {
        let lhs = ConstraintNode::Constant(constant);
        let rhs = ConstraintNode::ConstantDeref(constant);
        let lhs = self.get_or_insert_node(lhs);
        let rhs = self.get_or_insert_node(rhs);
        self.graph.add_edge(rhs, lhs, ConstraintEdge::Address);

        self.graph.add_edge(rhs, rhs, ConstraintEdge::Address);
    }

    fn add_address(&mut self, lhs: PlaceRef<'tcx>, rhs: PlaceRef<'tcx>) {
        let lhs = ConstraintNode::Place(lhs);
        let rhs = ConstraintNode::Place(rhs);
        let lhs = self.get_or_insert_node(lhs);
        let rhs = self.get_or_insert_node(rhs);
        self.graph.add_edge(rhs, lhs, ConstraintEdge::Address);
    }

    fn add_copy(&mut self, lhs: PlaceRef<'tcx>, rhs: PlaceRef<'tcx>) {
        let lhs = ConstraintNode::Place(lhs);
        let rhs = ConstraintNode::Place(rhs);
        let lhs = self.get_or_insert_node(lhs);
        let rhs = self.get_or_insert_node(rhs);
        self.graph.add_edge(rhs, lhs, ConstraintEdge::Copy);
    }

    fn add_copy_constant(&mut self, lhs: PlaceRef<'tcx>, rhs: Const<'tcx>) {
        let lhs = ConstraintNode::Place(lhs);
        let rhs = ConstraintNode::Constant(rhs);
        let lhs = self.get_or_insert_node(lhs);
        let rhs = self.get_or_insert_node(rhs);
        self.graph.add_edge(rhs, lhs, ConstraintEdge::Copy);
    }

    fn add_load(&mut self, lhs: PlaceRef<'tcx>, rhs: PlaceRef<'tcx>) {
        let lhs = ConstraintNode::Place(lhs);
        let rhs = ConstraintNode::Place(rhs);
        let lhs = self.get_or_insert_node(lhs);
        let rhs = self.get_or_insert_node(rhs);
        self.graph.add_edge(rhs, lhs, ConstraintEdge::Load);
    }

    fn add_store(&mut self, lhs: PlaceRef<'tcx>, rhs: PlaceRef<'tcx>) {
        let lhs = ConstraintNode::Place(lhs);
        let rhs = ConstraintNode::Place(rhs);
        let lhs = self.get_or_insert_node(lhs);
        let rhs = self.get_or_insert_node(rhs);
        self.graph.add_edge(rhs, lhs, ConstraintEdge::Store);
    }

    fn add_store_constant(&mut self, lhs: PlaceRef<'tcx>, rhs: Const<'tcx>) {
        let lhs = ConstraintNode::Place(lhs);
        let rhs = ConstraintNode::Constant(rhs);
        let lhs = self.get_or_insert_node(lhs);
        let rhs = self.get_or_insert_node(rhs);
        self.graph.add_edge(rhs, lhs, ConstraintEdge::Store);
    }

    fn add_alias_copy(&mut self, lhs: PlaceRef<'tcx>, rhs: PlaceRef<'tcx>) {
        let lhs = ConstraintNode::Place(lhs);
        let rhs = ConstraintNode::Place(rhs);
        let lhs = self.get_or_insert_node(lhs);
        let rhs = self.get_or_insert_node(rhs);
        self.graph.add_edge(rhs, lhs, ConstraintEdge::AliasCopy);
    }

    fn nodes(&self) -> Vec<ConstraintNode<'tcx>> {
        self.node_map.keys().cloned().collect::<_>()
    }

    fn edges(&self) -> Vec<(ConstraintNode<'tcx>, ConstraintNode<'tcx>, ConstraintEdge)> {
        let mut v = Vec::new();
        for edge in self.graph.edge_references() {
            let source = self.graph.node_weight(edge.source()).cloned().unwrap();
            let target = self.graph.node_weight(edge.target()).cloned().unwrap();
            let weight = *edge.weight();
            v.push((source, target, weight));
        }
        v
    }

    fn store_sources(&self, lhs: &ConstraintNode<'tcx>) -> Vec<ConstraintNode<'tcx>> {
        let lhs = self.get_node(lhs).unwrap();
        let mut sources = Vec::new();
        for edge in self.graph.edges_directed(lhs, Direction::Incoming) {
            if *edge.weight() == ConstraintEdge::Store {
                let source = self.graph.node_weight(edge.source()).cloned().unwrap();
                sources.push(source);
            }
        }
        sources
    }

    fn load_targets(&self, rhs: &ConstraintNode<'tcx>) -> Vec<ConstraintNode<'tcx>> {
        let rhs = self.get_node(rhs).unwrap();
        let mut targets = Vec::new();
        for edge in self.graph.edges_directed(rhs, Direction::Outgoing) {
            if *edge.weight() == ConstraintEdge::Load {
                let target = self.graph.node_weight(edge.target()).cloned().unwrap();
                targets.push(target);
            }
        }
        targets
    }

    fn copy_targets(&self, rhs: &ConstraintNode<'tcx>) -> Vec<ConstraintNode<'tcx>> {
        let rhs = self.get_node(rhs).unwrap();
        let mut targets = Vec::new();
        for edge in self.graph.edges_directed(rhs, Direction::Outgoing) {
            if *edge.weight() == ConstraintEdge::Copy {
                let target = self.graph.node_weight(edge.target()).cloned().unwrap();
                targets.push(target);
            }
        }
        targets
    }

    fn alias_copy_targets(&self, rhs: &ConstraintNode<'tcx>) -> Vec<ConstraintNode<'tcx>> {
        let rhs = self.get_node(rhs).unwrap();
        self.graph
            .edges_directed(rhs, Direction::Outgoing)
            .filter_map(|edge| {
                if *edge.weight() == ConstraintEdge::AliasCopy {
                    Some(edge.target())
                } else {
                    None
                }
            })
            .fold(Vec::new(), |mut acc, copy_alias_target| {
                let address_targets = self
                    .graph
                    .edges_directed(copy_alias_target, Direction::Outgoing)
                    .filter_map(|edge| {
                        if *edge.weight() == ConstraintEdge::Address {
                            Some(self.graph.node_weight(edge.target()).cloned().unwrap())
                        } else {
                            None
                        }
                    });
                acc.extend(address_targets);
                acc
            })
    }

    fn insert_edge(
        &mut self,
        from: ConstraintNode<'tcx>,
        to: ConstraintNode<'tcx>,
        weight: ConstraintEdge,
    ) -> bool {
        let from = self.get_node(&from).unwrap();
        let to = self.get_node(&to).unwrap();
        if let Some(edge) = self.graph.find_edge(from, to) {
            if let Some(w) = self.graph.edge_weight(edge) {
                if *w == weight {
                    return false;
                }
            }
        }
        self.graph.add_edge(from, to, weight);
        true
    }

    #[allow(dead_code)]
    pub fn dot(&self) {
        println!(
            "{:?}",
            Dot::with_config(&self.graph, &[Config::GraphContentOnly])
        );
    }
}

struct ConstraintGraphCollector<'a, 'tcx> {
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    graph: ConstraintGraph<'tcx>,
}

impl<'a, 'tcx> ConstraintGraphCollector<'a, 'tcx> {
    fn new(body: &'a Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            body,
            tcx,
            graph: ConstraintGraph::default(),
        }
    }

    fn process_assignment(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>) {
        let lhs_pattern = Self::process_place(place.as_ref());
        let rhs_patterns = Self::process_rvalue(rvalue);

        if let Rvalue::Aggregate(box AggregateKind::Closure(_def_id, _args), fields) = rvalue {
            let upvar_tys = _args.as_closure().upvar_tys();

            for (idx, (operand, upvar_ty)) in fields.iter_enumerated().zip(upvar_tys).enumerate() {
                if let Some(rhs) = operand.1.place() {
                    let lhs_field = match place.projection.last() {
                        Some(_) => self.tcx.mk_place_field(*place, idx.into(), upvar_ty),

                        None => Place {
                            local: place.local,
                            projection: self
                                .tcx
                                .mk_place_elems(&[ProjectionElem::Field(idx.into(), upvar_ty)]),
                        },
                    };

                    self.graph.add_copy(lhs_field.as_ref(), rhs.as_ref());

                    if upvar_ty.is_ref() {
                        self.graph.add_address(lhs_field.as_ref(), rhs.as_ref());
                    }
                }
            }
        }

        for rhs_pattern in rhs_patterns.into_iter() {
            match (&lhs_pattern, rhs_pattern) {
                (AccessPattern::Direct(lhs), Some(AccessPattern::Ref(rhs))) => {
                    self.graph.add_address(*lhs, rhs);
                }

                (AccessPattern::Direct(lhs), Some(AccessPattern::Direct(rhs))) => {
                    self.graph.add_copy(*lhs, rhs);
                }

                (AccessPattern::Direct(lhs), Some(AccessPattern::Constant(rhs))) => {
                    self.graph.add_copy_constant(*lhs, rhs);
                }

                (AccessPattern::Direct(lhs), Some(AccessPattern::Indirect(rhs))) => {
                    self.graph.add_load(*lhs, rhs);
                }

                (AccessPattern::Indirect(lhs), Some(AccessPattern::Direct(rhs))) => {
                    self.graph.add_store(*lhs, rhs);
                }

                (AccessPattern::Indirect(lhs), Some(AccessPattern::Constant(rhs))) => {
                    self.graph.add_store_constant(*lhs, rhs);
                }

                (AccessPattern::Indirect(lhs), Some(AccessPattern::Ref(rhs))) => {
                    // *x = &y: store the address of y through pointer x
                    self.graph.add_store(*lhs, rhs);
                    self.graph.add_address(*lhs, rhs);
                }

                (AccessPattern::Indirect(lhs), Some(AccessPattern::Indirect(rhs))) => {
                    // *x = *y: load from y, store into x
                    // Modeled conservatively by copying through the indirect
                    self.graph.add_load(*lhs, rhs);
                }

                _ => {}
            }
        }
    }

    fn process_place(place_ref: PlaceRef<'tcx>) -> AccessPattern<'tcx> {
        match place_ref {
            PlaceRef {
                local: l,
                projection: [ProjectionElem::Deref, remain @ ..],
            } => AccessPattern::Indirect(PlaceRef {
                local: l,
                projection: remain,
            }),
            _ => AccessPattern::Direct(place_ref),
        }
    }

    fn process_operand(operand: &Operand<'tcx>) -> Option<AccessPattern<'tcx>> {
        match operand {
            Operand::Move(place) | Operand::Copy(place) => {
                Some(AccessPattern::Direct(place.as_ref()))
            }
            Operand::Constant(box ConstOperand {
                span: _,
                user_ty: _,
                const_,
            }) => Some(AccessPattern::Constant(*const_)),
            Operand::RuntimeChecks(_) => {
                todo!("Handle RuntimeChecks operand in points-to analysis");
            }
        }
    }

    fn process_rvalue(rvalue: &Rvalue<'tcx>) -> Vec<Option<AccessPattern<'tcx>>> {
        match rvalue {
            Rvalue::Use(operand, _)
            | Rvalue::Repeat(operand, _)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::UnaryOp(_, operand) => {
                vec![Self::process_operand(operand)]
            }

            Rvalue::RawPtr(_, place)
            | Rvalue::Discriminant(place)
            | Rvalue::CopyForDeref(place) => match place.as_ref() {
                PlaceRef {
                    local: l,
                    projection: [ProjectionElem::Deref, remain @ ..],
                } => vec![Some(AccessPattern::Direct(PlaceRef {
                    local: l,
                    projection: remain,
                }))],
                _ => vec![Some(AccessPattern::Ref(place.as_ref()))],
            },
            Rvalue::Ref(_, _, place) => {
                vec![Some(AccessPattern::Ref(place.as_ref()))]
            }

            Rvalue::BinaryOp(_, box (left, right)) => {
                vec![Self::process_operand(left), Self::process_operand(right)]
            }

            Rvalue::Aggregate(box kind, fields) => match kind {
                AggregateKind::RawPtr(_, _) => {
                    vec![Self::process_operand(
                        &fields.iter_enumerated().next().unwrap().1,
                    )]
                }
                _ => fields.iter().map(Self::process_operand).collect::<Vec<_>>(),
            },

            Rvalue::ThreadLocalRef(_) => vec![],
            _ => vec![],
        }
    }

    fn process_call_arg_dest(&mut self, arg: PlaceRef<'tcx>, dest: PlaceRef<'tcx>) {
        self.graph.add_copy(dest, arg);
    }

    fn process_alias_copy(&mut self, arg: PlaceRef<'tcx>, dest: PlaceRef<'tcx>) {
        self.graph.add_load(dest, arg);
        self.graph.add_alias_copy(dest, arg);
    }

    fn process_generic_call(&mut self, args: &[Spanned<Operand<'tcx>>], destination: &Place<'tcx>) {
        for arg in args {
            if let Some(place) = operand_place(&arg.node) {
                self.graph.add_copy(destination.as_ref(), place.as_ref());
            }
        }
    }

    fn projection_may_alias(p1: &[PlaceElem<'tcx>], p2: &[PlaceElem<'tcx>]) -> bool {
        if p1.len() != p2.len() {
            return false;
        }
        for (a, b) in p1.iter().zip(p2.iter()) {
            let matches = match (a, b) {
                (PlaceElem::Index(_), PlaceElem::Index(_)) => true,
                (PlaceElem::Index(_), PlaceElem::ConstantIndex { .. })
                | (PlaceElem::ConstantIndex { .. }, PlaceElem::Index(_)) => true,
                (
                    PlaceElem::ConstantIndex { offset: o1, .. },
                    PlaceElem::ConstantIndex { offset: o2, .. },
                ) => o1 == o2,
                (PlaceElem::Subslice { .. }, PlaceElem::Subslice { .. }) => true,
                (PlaceElem::Subslice { .. }, PlaceElem::Index(_))
                | (PlaceElem::Index(_), PlaceElem::Subslice { .. }) => true,
                (PlaceElem::Subslice { .. }, PlaceElem::ConstantIndex { .. })
                | (PlaceElem::ConstantIndex { .. }, PlaceElem::Subslice { .. }) => true,
                (a, b) => a == b,
            };
            if !matches {
                return false;
            }
        }
        true
    }

    fn add_partial_copy(&mut self) {
        let nodes = self.graph.nodes();
        for (idx, n1) in nodes.iter().enumerate() {
            for n2 in nodes.iter().skip(idx + 1) {
                if let (ConstraintNode::Place(p1), ConstraintNode::Place(p2)) = (n1, n2) {
                    if p1.local == p2.local {
                        if p1.projection.len() > p2.projection.len() {
                            if &p1.projection[..p2.projection.len()] == p2.projection {
                                self.graph.add_copy(*p2, *p1);
                            }
                        } else if &p2.projection[..p1.projection.len()] == p1.projection {
                            self.graph.add_copy(*p1, *p2);
                        } else if Self::projection_may_alias(p1.projection, p2.projection) {
                            self.graph.add_copy(*p1, *p2);
                            self.graph.add_copy(*p2, *p1);
                        }
                    }
                }
            }
        }
    }

    fn finish(mut self) -> ConstraintGraph<'tcx> {
        self.add_partial_copy();
        self.graph
    }
}

impl<'a, 'tcx> Visitor<'tcx> for ConstraintGraphCollector<'a, 'tcx> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, _location: Location) {
        match &statement.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                self.process_assignment(place, rvalue);
            }

            StatementKind::FakeRead(_) => {}

            StatementKind::SetDiscriminant { .. } => {}

            StatementKind::StorageLive(_) => {}

            StatementKind::StorageDead(_) => {}

            // StatementKind::Retag(_, _, _) => {}

            StatementKind::AscribeUserType(_, _)
            | StatementKind::Coverage(_)
            | StatementKind::Nop => {}

            StatementKind::PlaceMention(_) => {}
            StatementKind::ConstEvalCounter
            | StatementKind::Intrinsic(_)
            | StatementKind::BackwardIncompatibleDropHint { .. } => {}
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, _location: Location) {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            match (
                args.iter()
                    .map(|x| x.node.clone())
                    .collect::<Vec<_>>()
                    .as_slice(),
                destination,
            ) {
                (&[Operand::Move(arg)], dest) | (&[Operand::Copy(arg)], dest) => {
                    let func_ty = func.ty(self.body, self.tcx);
                    if let TyKind::FnDef(def_id, substs) = func_ty.kind() {
                        if ownership::is_arc_or_rc_clone(*def_id, substs, self.tcx)
                            || ownership::is_ptr_read(*def_id, self.tcx)
                        {
                            return self.process_alias_copy(arg.as_ref(), dest.as_ref());
                        }
                    }
                    self.process_call_arg_dest(arg.as_ref(), dest.as_ref());
                }
                (&[Operand::Move(arg), _], dest) => {
                    let func_ty = func.ty(self.body, self.tcx);
                    if let TyKind::FnDef(def_id, _) = func_ty.kind() {
                        if ownership::is_index(*def_id, self.tcx) {
                            return self.process_call_arg_dest(arg.as_ref(), dest.as_ref());
                        }
                    }
                    self.process_generic_call(args, destination);
                }
                (
                    &[
                        Operand::Move(arg0),
                        Operand::Move(arg1),
                        Operand::Move(_arg2),
                    ],
                    _dest,
                )
                | (
                    &[
                        Operand::Move(arg0),
                        Operand::Move(arg1),
                        Operand::Copy(_arg2),
                    ],
                    _dest,
                ) => {
                    let func_ty = func.ty(self.body, self.tcx);
                    if let TyKind::FnDef(def_id, list) = func_ty.kind() {
                        if is_atomic_ptr_store(*def_id, list, self.tcx) {
                            return self.process_call_arg_dest(arg1.as_ref(), arg0.as_ref());
                        }
                    }
                    self.process_generic_call(args, destination);
                }

                _ => {
                    self.process_generic_call(args, destination);
                }
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ApproximateAliasKind {
    Probably,
    Possibly,
    Unlikely,
    Unknown,
}

impl PartialOrd for ApproximateAliasKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use ApproximateAliasKind::*;
        match (*self, *other) {
            (Probably, Probably)
            | (Possibly, Possibly)
            | (Unlikely, Unlikely)
            | (Unknown, Unknown) => Some(Ordering::Equal),
            (Probably, _) | (Possibly, Unlikely) | (Possibly, Unknown) | (Unlikely, Unknown) => {
                Some(Ordering::Greater)
            }
            (_, Probably) | (Unlikely, Possibly) | (Unknown, Possibly) | (Unknown, Unlikely) => {
                Some(Ordering::Less)
            }
        }
    }
}

impl ApproximateAliasKind {
    /// Whether this alias should add arcs under the configured Unknown policy (treat as possible alias).
    pub fn may_alias(self, policy: crate::config::AliasUnknownPolicy) -> bool {
        use crate::config::AliasUnknownPolicy;
        match self {
            ApproximateAliasKind::Probably | ApproximateAliasKind::Possibly => true,
            ApproximateAliasKind::Unlikely => false,
            ApproximateAliasKind::Unknown => matches!(policy, AliasUnknownPolicy::Conservative),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AliasId {
    pub instance_id: InstanceId,
    pub local: Local,
    /// Constant index distinguishes `arr[0]` vs `arr[1]`; dynamic index or non-array ⇒ `None` (merged).
    pub array_index: Option<u64>,
    /// For field accesses (like self.mu), this stores the field index to distinguish
    /// different fields of the same struct. None means no field projection.
    pub field: Option<u32>,
}

impl AliasId {
    pub fn new(instance_id: InstanceId, local: Local) -> Self {
        Self {
            instance_id,
            local,
            array_index: None,
            field: None,
        }
    }

    /// Build from `Place`, extracting constant indices to distinguish `arr[0]` vs `arr[1]`
    /// and field index to distinguish `self.mu` vs `self.rw1`.
    pub fn from_place<'tcx>(instance_id: InstanceId, place: PlaceRef<'tcx>) -> Self {
        let array_index = if place
            .projection
            .iter()
            .any(|e| matches!(e, PlaceElem::Index(_)))
        {
            None
        } else {
            place.projection.iter().rev().find_map(|elem| {
                if let PlaceElem::ConstantIndex { offset, .. } = elem {
                    Some(*offset)
                } else {
                    None
                }
            })
        };
        // Extract the first Field projection to distinguish different fields
        let field = place.projection.iter().find_map(|elem| {
            if let ProjectionElem::Field(f, _) = elem {
                Some(f.as_u32())
            } else {
                None
            }
        });
        Self {
            instance_id,
            local: place.local,
            array_index,
            field,
        }
    }
}

impl std::convert::From<LockGuardId> for AliasId {
    fn from(lockguard_id: LockGuardId) -> Self {
        Self {
            instance_id: lockguard_id.instance_id,
            local: lockguard_id.local,
            array_index: None,
            field: None,
        }
    }
}

impl std::convert::From<CondVarId> for AliasId {
    fn from(condvar_id: CondVarId) -> Self {
        Self {
            instance_id: condvar_id.instance_id,
            local: condvar_id.local,
            array_index: None,
            field: None,
        }
    }
}

impl std::convert::From<ChannelId> for AliasId {
    fn from(channel_id: ChannelId) -> Self {
        Self {
            instance_id: channel_id.instance_id,
            local: channel_id.local,
            array_index: None,
            field: None,
        }
    }
}

pub struct AliasAnalysis<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    callgraph: &'a CallGraph<'tcx>,
    pts: FxHashMap<DefId, PointsToMap<'tcx>>,
}

impl<'a, 'tcx> AliasAnalysis<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, callgraph: &'a CallGraph<'tcx>) -> Self {
        Self {
            tcx,
            callgraph,
            pts: Default::default(),
        }
    }

    pub fn print_all_points_to_relations(&self) {
        println!("{}", self.format_points_to_report());
    }

    /// Ensure points-to sets are computed for all listed instances (pre-fill before standalone dumps).
    pub fn ensure_pts_for_instances(&mut self, instances: &[Instance<'tcx>]) {
        for instance in instances {
            if self.tcx.is_mir_available(instance.def_id()) {
                let body = self.tcx.instance_mir(instance.def);
                if body.source.promoted.is_none() {
                    self.get_or_insert_pts(instance.def_id(), body);
                }
            }
        }
    }

    pub fn format_points_to_report(&self) -> String {
        let mut out = String::new();
        out.push_str("\n=== Points-to Relations for All Functions ===\n");

        let mut all_defs: Vec<_> = self.pts.keys().collect();
        all_defs.sort_by_key(|def_id| self.tcx.def_path_str(**def_id));

        for def_id in all_defs {
            out.push_str(&self.format_points_to_relations_for(*def_id));
        }

        out.push_str("=== End of Points-to Relations ===\n\n");
        out
    }

    fn format_points_to_relations_for(&self, def_id: DefId) -> String {
        let mut out = String::new();
        if let Some(pts_map) = self.pts.get(&def_id) {
            out.push_str(&format!(
                "\nPoints-to relations for {:?}:\n",
                self.tcx.def_path_str(def_id)
            ));
            out.push_str("----------------------------------------\n");

            let mut entries: Vec<_> = pts_map.iter().collect();
            entries.sort_by(|(a, _), (b, _)| match (a, b) {
                (ConstraintNode::Place(_), ConstraintNode::Constant(_)) => std::cmp::Ordering::Less,
                (ConstraintNode::Constant(_), ConstraintNode::Place(_)) => {
                    std::cmp::Ordering::Greater
                }
                (ConstraintNode::Place(_), ConstraintNode::ConstantDeref(_)) => {
                    std::cmp::Ordering::Less
                }
                (ConstraintNode::ConstantDeref(_), ConstraintNode::Place(_)) => {
                    std::cmp::Ordering::Greater
                }
                (ConstraintNode::Place(_), ConstraintNode::Alloc(_)) => std::cmp::Ordering::Less,
                (ConstraintNode::Alloc(_), ConstraintNode::Place(_)) => std::cmp::Ordering::Greater,
                (ConstraintNode::Constant(_), ConstraintNode::ConstantDeref(_)) => {
                    std::cmp::Ordering::Less
                }
                (ConstraintNode::ConstantDeref(_), ConstraintNode::Constant(_)) => {
                    std::cmp::Ordering::Greater
                }
                (ConstraintNode::Constant(_), ConstraintNode::Alloc(_)) => std::cmp::Ordering::Less,
                (ConstraintNode::Alloc(_), ConstraintNode::Constant(_)) => {
                    std::cmp::Ordering::Greater
                }
                (ConstraintNode::ConstantDeref(_), ConstraintNode::Alloc(_)) => {
                    std::cmp::Ordering::Less
                }
                (ConstraintNode::Alloc(_), ConstraintNode::ConstantDeref(_)) => {
                    std::cmp::Ordering::Greater
                }

                (ConstraintNode::Place(p1), ConstraintNode::Place(p2)) => {
                    p1.local.cmp(&p2.local).then_with(|| {
                        format!("{:?}", p1.projection).cmp(&format!("{:?}", p2.projection))
                    })
                }
                (ConstraintNode::Constant(c1), ConstraintNode::Constant(c2)) => {
                    format!("{:?}", c1).cmp(&format!("{:?}", c2))
                }
                (ConstraintNode::ConstantDeref(c1), ConstraintNode::ConstantDeref(c2)) => {
                    format!("{:?}", c1).cmp(&format!("{:?}", c2))
                }
                (ConstraintNode::Alloc(p1), ConstraintNode::Alloc(p2)) => {
                    p1.local.cmp(&p2.local).then_with(|| {
                        format!("{:?}", p1.projection).cmp(&format!("{:?}", p2.projection))
                    })
                }
            });

            for (node, pointees) in entries {
                match node {
                    ConstraintNode::Place(place) => {
                        out.push_str(&format!("{}", place.local.as_u32()));
                        if !place.projection.is_empty() {
                            out.push_str(&format!("{:?}", place.projection));
                        }
                        out.push_str(" → ");

                        let targets: Vec<String> = pointees
                            .iter()
                            .map(|pointee| match pointee {
                                ConstraintNode::Alloc(p) => format!("Alloc({:?})", p),
                                ConstraintNode::Place(p) => format!("{:?}", p),
                                ConstraintNode::Constant(c) => format!("Const({:?})", c),
                                ConstraintNode::ConstantDeref(c) => {
                                    format!("ConstDeref({:?})", c)
                                }
                            })
                            .collect();

                        out.push_str(&format!("{{{}}}\n", targets.join(", ")));
                    }
                    ConstraintNode::Constant(c) => {
                        out.push_str(&format!("Const({:?}) → {:?}\n", c, pointees));
                    }
                    ConstraintNode::ConstantDeref(c) => {
                        out.push_str(&format!("ConstDeref({:?}) → {:?}\n", c, pointees));
                    }
                    ConstraintNode::Alloc(place) => {
                        out.push_str(&format!(
                            "Alloc({}{:?}) → {:?}\n",
                            place.local.as_u32(),
                            place.projection,
                            pointees
                        ));
                    }
                }
            }
            out.push_str("----------------------------------------\n\n");
        }
        out
    }

    pub fn print_points_to_relations(&self, def_id: DefId) {
        print!("{}", self.format_points_to_relations_for(def_id));
    }

    pub fn alias(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        let AliasId {
            instance_id: id1,
            local: local1,
            array_index: idx1,
            ..
        } = aid1;
        let AliasId {
            instance_id: id2,
            local: local2,
            array_index: idx2,
            ..
        } = aid2;

        if id1 == id2 && local1 == local2 {
            if let (Some(i), Some(j)) = (idx1, idx2) {
                return if i == j {
                    ApproximateAliasKind::Probably
                } else {
                    ApproximateAliasKind::Unlikely
                };
            }
            if idx1.is_none() && idx2.is_none() {
                return ApproximateAliasKind::Probably;
            }
        }

        let instance1 = self
            .callgraph
            .index_to_instance(id1)
            .map(CallGraphNode::instance);
        let instance2 = self
            .callgraph
            .index_to_instance(id2)
            .map(CallGraphNode::instance);

        match (instance1, instance2) {
            (Some(instance1), Some(instance2)) => {
                let node1 = ConstraintNode::Place(Place::from(local1).as_ref());
                let node2 = ConstraintNode::Place(Place::from(local2).as_ref());

                if instance1.def_id() == instance2.def_id() {
                    self.intraproc_alias(instance1, &node1, &node2)
                        .unwrap_or(ApproximateAliasKind::Unknown)
                } else {
                    self.interproc_alias(instance1, &node1, instance2, &node2)
                        .unwrap_or(ApproximateAliasKind::Unknown)
                }
            }
            _ => ApproximateAliasKind::Unknown,
        }
    }

    pub fn alias_atomic(&mut self, aid1: AliasId, aid2: AliasId) -> ApproximateAliasKind {
        let AliasId {
            instance_id: id1,
            local: local1,
            array_index: idx1,
            ..
        } = aid1;
        let AliasId {
            instance_id: id2,
            local: local2,
            array_index: idx2,
            ..
        } = aid2;

        if id1 == id2 && local1 == local2 {
            if let (Some(i), Some(j)) = (idx1, idx2) {
                return if i == j {
                    ApproximateAliasKind::Probably
                } else {
                    ApproximateAliasKind::Unlikely
                };
            }
            if idx1.is_none() && idx2.is_none() {
                return ApproximateAliasKind::Probably;
            }
        }

        let instance1 = self
            .callgraph
            .index_to_instance(id1)
            .map(CallGraphNode::instance);
        let instance2 = self
            .callgraph
            .index_to_instance(id2)
            .map(CallGraphNode::instance);

        match (instance1, instance2) {
            (Some(instance1), Some(instance2)) => {
                let node1 = ConstraintNode::Place(Place::from(local1).as_ref());
                let node2 = ConstraintNode::Place(Place::from(local2).as_ref());
                if instance1.def_id() == instance2.def_id() {
                    self.atomic_intraproc_alias(instance1, &node1, &node2)
                        .unwrap_or(ApproximateAliasKind::Unknown)
                } else {
                    self.new_interproc_alias(instance1, &node1, instance2, &node2)
                        .unwrap_or(ApproximateAliasKind::Unknown)
                }
            }
            _ => ApproximateAliasKind::Unknown,
        }
    }

    pub fn points_to(&mut self, pointer: AliasId, pointee: AliasId) -> ApproximateAliasKind {
        let AliasId {
            instance_id: id1,
            local: local1,
            ..
        } = pointer;
        let AliasId {
            instance_id: id2,
            local: local2,
            ..
        } = pointee;

        let instance1 = self
            .callgraph
            .index_to_instance(id1)
            .map(CallGraphNode::instance);
        let instance2 = self
            .callgraph
            .index_to_instance(id2)
            .map(CallGraphNode::instance);

        match (instance1, instance2) {
            (Some(instance1), Some(instance2)) => {
                let node1 = ConstraintNode::Place(Place::from(local1).as_ref());
                let node2 = ConstraintNode::Place(Place::from(local2).as_ref());
                if instance1.def_id() == instance2.def_id() {
                    self.intra_points_to(instance1, node1, node2)
                } else {
                    self.inter_points_to(instance1, node1, instance2, node2)
                }
            }
            _ => ApproximateAliasKind::Unknown,
        }
    }

    pub fn intra_points_to(
        &mut self,
        instance: &Instance<'tcx>,
        pointer: ConstraintNode<'tcx>,
        pointee: ConstraintNode<'tcx>,
    ) -> ApproximateAliasKind {
        let body = self.tcx.instance_mir(instance.def);
        let points_to_map = self.get_or_insert_pts(instance.def_id(), body).clone();
        let mut final_alias_kind = ApproximateAliasKind::Unknown;
        let set = match points_to_map.get(&pointer) {
            Some(set) => set,
            None => return ApproximateAliasKind::Unlikely,
        };
        for local_pointee in set {
            let alias_kind = self
                .intraproc_alias(instance, local_pointee, &pointee)
                .unwrap_or(ApproximateAliasKind::Unknown);
            if alias_kind > final_alias_kind {
                final_alias_kind = alias_kind;
            } else {
                if let Some(parent_pointer) = self.get_parent_node(&local_pointee) {
                    log::debug!(
                        "child pointer: {:?} and parent pointer: {:?}",
                        local_pointee,
                        parent_pointer
                    );
                    if let Some(sets) = points_to_map.get(&parent_pointer) {
                        for parent_node in sets {
                            let alias_kind = self
                                .intraproc_alias(instance, parent_node, &pointee)
                                .unwrap_or(ApproximateAliasKind::Unknown);
                            if alias_kind > final_alias_kind {
                                return ApproximateAliasKind::Possibly;
                            }
                        }
                    }
                }
            }
        }
        final_alias_kind
    }

    pub fn inter_points_to(
        &mut self,
        instance1: &Instance<'tcx>,
        pointer: ConstraintNode<'tcx>,
        instance2: &Instance<'tcx>,
        pointee: ConstraintNode<'tcx>,
    ) -> ApproximateAliasKind {
        let body1 = self.tcx.instance_mir(instance1.def);
        let points_to_map = self.get_or_insert_pts(instance1.def_id(), body1).clone();
        let mut final_alias_kind = ApproximateAliasKind::Unknown;
        let set = match points_to_map.get(&pointer) {
            Some(set) => set,
            None => return ApproximateAliasKind::Unlikely,
        };
        for local_pointee in set {
            let alias_kind = self
                .interproc_alias(instance1, local_pointee, instance2, &pointee)
                .unwrap_or(ApproximateAliasKind::Unknown);
            if alias_kind > final_alias_kind {
                final_alias_kind = alias_kind;
            }
        }
        final_alias_kind
    }

    pub fn get_or_insert_pts(&mut self, def_id: DefId, body: &Body<'tcx>) -> &PointsToMap<'tcx> {
        if self.pts.contains_key(&def_id) {
            self.pts.get(&def_id).unwrap()
        } else {
            let mut pointer_analysis = Andersen::new(body, self.tcx);
            pointer_analysis.analyze();
            let pts = pointer_analysis.finish();
            self.pts.entry(def_id).or_insert(pts)
        }
    }

    fn intraproc_alias(
        &mut self,
        instance: &Instance<'tcx>,
        node1: &ConstraintNode<'tcx>,
        node2: &ConstraintNode<'tcx>,
    ) -> Option<ApproximateAliasKind> {
        let body = self.tcx.instance_mir(instance.def);
        let points_to_map = self.get_or_insert_pts(instance.def_id(), body);

        if points_to_map
            .get(node1)?
            .intersection(points_to_map.get(node2)?)
            .next()
            .is_some()
        {
            Some(ApproximateAliasKind::Probably)
        } else {
            Some(ApproximateAliasKind::Unlikely)
        }
    }

    fn atomic_intraproc_alias(
        &mut self,
        instance: &Instance<'tcx>,
        pointer: &ConstraintNode<'tcx>,
        pointee: &ConstraintNode<'tcx>,
    ) -> Option<ApproximateAliasKind> {
        let body = self.tcx.instance_mir(instance.def);
        let points_to_map = self.get_or_insert_pts(instance.def_id(), body);

        fn get_local(node: &ConstraintNode<'_>) -> Option<Local> {
            match node {
                ConstraintNode::Place(place) => Some(place.local),
                ConstraintNode::Alloc(place) => Some(place.local),
                _ => None,
            }
        }

        let mut pointee_set = FxHashSet::default();
        let mut pointer_set = FxHashSet::default();

        if let Some(local) = get_local(pointee) {
            pointee_set.insert(local);
        }
        if let Some(local) = get_local(pointer) {
            pointer_set.insert(local);
        }

        for (node, pts) in points_to_map {
            if let Some(from_local) = get_local(node) {
                for target in pts {
                    if let Some(to_local) = get_local(target) {
                        if pointee_set.contains(&to_local) {
                            pointee_set.insert(from_local);
                        }
                        if pointer_set.contains(&to_local) {
                            pointer_set.insert(from_local);
                        }
                    }
                }
            }
        }

        log::debug!(
            "pointer_set: {:?}\n pointee_set: {:?}",
            pointer_set,
            pointee_set
        );

        if !pointer_set.is_disjoint(&pointee_set) {
            return Some(ApproximateAliasKind::Probably);
        }

        fn check_alias_recursive<'tcx>(
            node1: &ConstraintNode<'tcx>,
            node2: &ConstraintNode<'tcx>,
            points_to_map: &PointsToMap<'tcx>,
            depth: usize,
        ) -> bool {
            if depth > 20 {
                return false;
            }

            if let (Some(pts1), Some(pts2)) = (points_to_map.get(node1), points_to_map.get(node2)) {
                if pts1.contains(node2) || pts2.contains(node1) {
                    return true;
                }

                for p1 in pts1 {
                    if check_alias_recursive(p1, node2, points_to_map, depth + 1) {
                        return true;
                    }

                    for p2 in pts2 {
                        if check_alias_recursive(p1, p2, points_to_map, depth + 1) {
                            return true;
                        }
                    }
                }
            }
            false
        }

        if check_alias_recursive(pointer, pointee, points_to_map, 0) {
            Some(ApproximateAliasKind::Probably)
        } else {
            Some(ApproximateAliasKind::Unlikely)
        }
    }

    fn new_intraproc_points_to(
        &mut self,
        instance: &Instance<'tcx>,
        node1: &ConstraintNode<'tcx>,
        node2: &ConstraintNode<'tcx>,
    ) -> Option<ApproximateAliasKind> {
        let body = self.tcx.instance_mir(instance.def);
        let points_to_map = self.get_or_insert_pts(instance.def_id(), body);

        let pts1 = points_to_map.get(&node1)?;
        let pts2 = points_to_map.get(&node2)?;

        if !pts1.is_disjoint(pts2) {
            let allocs1: FxHashSet<_> = pts1
                .iter()
                .filter(|n| matches!(n, ConstraintNode::Alloc(_) | ConstraintNode::Place(_)))
                .collect();
            let allocs2: FxHashSet<_> = pts2
                .iter()
                .filter(|n| matches!(n, ConstraintNode::Alloc(_) | ConstraintNode::Place(_)))
                .collect();

            let common_allocs: FxHashSet<_> = allocs1.intersection(&allocs2).collect();

            if !common_allocs.is_empty() {
                return Some(ApproximateAliasKind::Probably);
            }
        }

        Some(ApproximateAliasKind::Unlikely)
    }

    fn interproc_alias(
        &mut self,
        instance1: &Instance<'tcx>,
        node1: &ConstraintNode<'tcx>,
        instance2: &Instance<'tcx>,
        node2: &ConstraintNode<'tcx>,
    ) -> Option<ApproximateAliasKind> {
        let body1 = self.tcx.instance_mir(instance1.def);
        let body2 = self.tcx.instance_mir(instance2.def);
        let points_to_map1 = self.get_or_insert_pts(instance1.def_id(), body1).clone();
        let points_to_map2 = self.get_or_insert_pts(instance2.def_id(), body2).clone();

        let pts1 = points_to_map1.get(node1)?;
        let pts2 = points_to_map2.get(node2)?;

        if point_to_same_constant(pts1, pts2) {
            return Some(ApproximateAliasKind::Probably);
        }

        if point_to_same_type_param(pts1, pts2, body1, body2) {
            return Some(ApproximateAliasKind::Possibly);
        }

        let mut defsite_upvars1 = None;
        if self.tcx.is_closure_like(instance1.def_id()) {
            let pts_paths = points_to_paths_to_param(node1.clone(), body1, &points_to_map1);
            for pts_path in pts_paths {
                let defsite_upvars = match self.closure_defsite_upvars(instance1, pts_path) {
                    Some(defsite_upvars) => defsite_upvars,
                    None => continue,
                };
                for (def_inst, upvar) in defsite_upvars.iter() {
                    if def_inst.def_id() == instance2.def_id() {
                        let alias_kind =
                            self.intra_points_to(def_inst, node2.clone(), upvar.clone());

                        if alias_kind > ApproximateAliasKind::Unlikely {
                            return Some(alias_kind);
                        }
                    }
                }

                defsite_upvars1 = Some(defsite_upvars);

                break;
            }
        }

        let mut defsite_upvars2 = None;
        if self.tcx.is_closure_like(instance2.def_id()) {
            let pts_paths = points_to_paths_to_param(node2.clone(), body2, &points_to_map2);
            for pts_path in pts_paths {
                let defsite_upvars = match self.closure_defsite_upvars(instance2, pts_path) {
                    Some(defsite_upvars) => defsite_upvars,
                    None => continue,
                };
                for (def_inst, upvar) in defsite_upvars.iter() {
                    if def_inst.def_id() == instance1.def_id() {
                        let alias_kind =
                            self.intra_points_to(def_inst, node1.clone(), upvar.clone());

                        if alias_kind > ApproximateAliasKind::Unlikely {
                            return Some(alias_kind);
                        }
                    }
                }

                defsite_upvars2 = Some(defsite_upvars);

                break;
            }
        }

        if let (Some(defsite_upvars1), Some(defsite_upvars2)) = (defsite_upvars1, defsite_upvars2) {
            for (instance1, node1) in defsite_upvars1 {
                for (instance2, node2) in &defsite_upvars2 {
                    if instance1.def_id() == instance2.def_id() {
                        let alias_kind = self
                            .intraproc_alias(instance1, &node1, node2)
                            .unwrap_or(ApproximateAliasKind::Unknown);
                        if alias_kind > ApproximateAliasKind::Unlikely {
                            return Some(alias_kind);
                        }
                    }
                }
            }
        }
        Some(ApproximateAliasKind::Unlikely)
    }

    fn new_interproc_alias(
        &mut self,
        instance1: &Instance<'tcx>,
        node1: &ConstraintNode<'tcx>,
        instance2: &Instance<'tcx>,
        node2: &ConstraintNode<'tcx>,
    ) -> Option<ApproximateAliasKind> {
        let body1 = self.tcx.instance_mir(instance1.def);
        let body2 = self.tcx.instance_mir(instance2.def);
        let points_to_map1 = self.get_or_insert_pts(instance1.def_id(), body1).clone();
        let points_to_map2 = self.get_or_insert_pts(instance2.def_id(), body2).clone();
        let pts1 = points_to_map1.get(node1)?;
        let pts2 = points_to_map2.get(node2)?;

        if point_to_same_constant(pts1, pts2) {
            return Some(ApproximateAliasKind::Probably);
        }

        if point_to_same_type_param(pts1, pts2, body1, body2) {
            return Some(ApproximateAliasKind::Possibly);
        }

        let mut defsite_upvars1 = None;
        if self.tcx.is_closure_like(instance1.def_id()) {
            let pts_paths = points_to_paths_to_param(node1.clone(), body1, &points_to_map1);
            for pts_path in pts_paths {
                let defsite_upvars = match self.closure_defsite_upvars(instance1, pts_path) {
                    Some(defsite_upvars) => defsite_upvars,
                    None => continue,
                };
                for (def_inst, upvar) in defsite_upvars.iter() {
                    if def_inst.def_id() == instance2.def_id() {
                        let alias_kind = self
                            .new_intraproc_points_to(def_inst, node2, upvar)
                            .unwrap_or(ApproximateAliasKind::Unknown);
                        if alias_kind > ApproximateAliasKind::Unlikely {
                            return Some(alias_kind);
                        }
                    }
                }

                defsite_upvars1 = Some(defsite_upvars);

                break;
            }
        }

        let mut defsite_upvars2 = None;
        if self.tcx.is_closure_like(instance2.def_id()) {
            let pts_paths = points_to_paths_to_param(node2.clone(), body2, &points_to_map2);
            for pts_path in pts_paths {
                let defsite_upvars = match self.closure_defsite_upvars(instance2, pts_path) {
                    Some(defsite_upvars) => defsite_upvars,
                    None => continue,
                };
                for (def_inst, upvar) in defsite_upvars.iter() {
                    if def_inst.def_id() == instance1.def_id() {
                        let alias_kind = self
                            .new_intraproc_points_to(def_inst, node1, upvar)
                            .unwrap_or(ApproximateAliasKind::Unknown);
                        if alias_kind > ApproximateAliasKind::Unlikely {
                            return Some(alias_kind);
                        }
                    }
                }

                defsite_upvars2 = Some(defsite_upvars);

                break;
            }
        }

        if let (Some(defsite_upvars1), Some(defsite_upvars2)) = (defsite_upvars1, defsite_upvars2) {
            for (instance1, node1) in defsite_upvars1 {
                for (instance2, node2) in &defsite_upvars2 {
                    if instance1.def_id() == instance2.def_id() {
                        let alias_kind = self
                            .new_intraproc_points_to(instance1, &node1, node2)
                            .unwrap_or(ApproximateAliasKind::Unknown);
                        if alias_kind > ApproximateAliasKind::Unlikely {
                            return Some(alias_kind);
                        }
                    }
                }
            }
        }
        Some(ApproximateAliasKind::Unlikely)
    }

    fn closure_defsite_upvars(
        &self,
        closure: &'a Instance<'tcx>,
        path: PointsToPath<'tcx>,
    ) -> Option<Vec<(&'a Instance<'tcx>, ConstraintNode<'tcx>)>> {
        let projection = path.last()?.0;
        let def_inst_args = closure_defsite_args(closure, self.callgraph);
        let def_inst_upvars = def_inst_args
            .into_iter()
            .map(|(def_inst, arg)| {
                (
                    def_inst,
                    ConstraintNode::Place(PlaceRef {
                        local: arg,
                        projection,
                    }),
                )
            })
            .collect::<Vec<_>>();
        if def_inst_upvars.is_empty() {
            None
        } else {
            Some(def_inst_upvars)
        }
    }

    /// Look up the raw points-to map for a given function by its DefId.
    pub fn points_to_map(&self, def_id: DefId) -> Option<&PointsToMap<'tcx>> {
        self.pts.get(&def_id)
    }

    fn get_parent_node(&self, node: &ConstraintNode<'tcx>) -> Option<ConstraintNode<'tcx>> {
        match node {
            ConstraintNode::Place(place) | ConstraintNode::Alloc(place) => {
                if !place.projection.is_empty() {
                    Some(ConstraintNode::Place(PlaceRef {
                        local: place.local,
                        projection: &[],
                    }))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

fn point_to_same_constant<'tcx>(
    pts1: &FxHashSet<ConstraintNode<'tcx>>,
    pts2: &FxHashSet<ConstraintNode<'tcx>>,
) -> bool {
    let constants2: FxHashSet<_> = pts2
        .iter()
        .filter(|node| matches!(node, &ConstraintNode::ConstantDeref(_)))
        .collect();
    pts1.iter()
        .filter(|node| matches!(node, &ConstraintNode::ConstantDeref(_)))
        .any(|c1| constants2.contains(c1))
}

#[inline]
fn is_parameter(local: Local, body: &Body<'_>) -> bool {
    body.args_iter().any(|arg| arg == local)
}

#[inline]
fn param_index(local: Local, body: &Body<'_>) -> Option<usize> {
    body.args_iter().position(|arg| arg == local)
}

fn point_to_same_type_param<'tcx>(
    pts1: &FxHashSet<ConstraintNode<'tcx>>,
    pts2: &FxHashSet<ConstraintNode<'tcx>>,
    body1: &Body<'tcx>,
    body2: &Body<'tcx>,
) -> bool {
    let parameter_places1: Vec<_> = pts1
        .iter()
        .filter_map(|node| match node {
            ConstraintNode::Alloc(place) | ConstraintNode::Place(place)
                if is_parameter(place.local, body1) =>
            {
                Some(*place)
            }
            _ => None,
        })
        .collect();
    let parameter_places2: Vec<_> = pts2
        .iter()
        .filter_map(|node| match node {
            ConstraintNode::Alloc(place) | ConstraintNode::Place(place)
                if is_parameter(place.local, body2) =>
            {
                Some(*place)
            }
            _ => None,
        })
        .collect();
    parameter_places1.iter().any(|place1| {
        parameter_places2.iter().any(|place2| {
            body1.local_decls[place1.local].ty == body2.local_decls[place2.local].ty
                && place1.projection == place2.projection
                && (body1.source.def_id() == body2.source.def_id()
                    || param_index(place1.local, body1) == param_index(place2.local, body2))
        })
    })
}

fn closure_defsite_args<'a, 'b: 'a, 'tcx>(
    closure_inst: &'b Instance<'tcx>,
    callgraph: &'a CallGraph<'tcx>,
) -> Vec<(&'a Instance<'tcx>, Local)> {
    let callee_id = callgraph.instance_to_index(closure_inst).unwrap();
    let callers = callgraph.callers(callee_id);
    callers.into_iter().fold(Vec::new(), |mut acc, caller_id| {
        let caller_inst = callgraph.index_to_instance(caller_id).unwrap().instance();
        acc.extend(
            callgraph
                .callsites(caller_id, callee_id)
                .unwrap_or_default()
                .iter()
                .filter_map(|cs_loc| {
                    if let CallSiteLocation::ClosureDef(local) = cs_loc {
                        Some((caller_inst, *local))
                    } else {
                        None
                    }
                }),
        );
        acc
    })
}

type PointsToPath<'tcx> = Vec<(&'tcx [PlaceElem<'tcx>], ConstraintNode<'tcx>)>;

fn points_to_paths_to_param<'tcx>(
    node: ConstraintNode<'tcx>,
    body: &'tcx Body<'tcx>,
    points_to_map: &PointsToMap<'tcx>,
) -> Vec<PointsToPath<'tcx>> {
    let mut result = Vec::new();
    let mut path = Vec::new();
    let mut visited = FxHashSet::default();
    dfs_paths_recur(
        &[],
        node,
        body,
        points_to_map,
        &mut visited,
        &mut path,
        &mut result,
    );
    result
}

fn dfs_paths_recur<'tcx>(
    prev_proj: &'tcx [PlaceElem<'tcx>],
    node: ConstraintNode<'tcx>,
    body: &'tcx Body<'tcx>,
    points_to_map: &PointsToMap<'tcx>,
    visited: &mut FxHashSet<ConstraintNode<'tcx>>,
    path: &mut PointsToPath<'tcx>,
    result: &mut Vec<PointsToPath<'tcx>>,
) {
    if !visited.insert(node.clone()) {
        return;
    }
    let place = match node {
        ConstraintNode::Alloc(place) | ConstraintNode::Place(place) => place,
        _ => return,
    };
    path.push((prev_proj, node.clone()));

    if is_parameter(place.local, body) {
        result.push(path.clone());
        path.pop();
        return;
    }
    let pts = match points_to_map.get(&node) {
        Some(pts) => pts,
        None => {
            path.pop();
            return;
        }
    };
    for pointee in pts {
        match pointee {
            ConstraintNode::Alloc(place1) | ConstraintNode::Place(place1)
                if !place1.projection.is_empty() =>
            {
                let node1 = ConstraintNode::Place(Place::from(place1.local).as_ref());
                dfs_paths_recur(
                    place1.projection,
                    node1,
                    body,
                    points_to_map,
                    visited,
                    path,
                    result,
                );
            }
            _ => {}
        }
    }
    path.pop();
}
