//! MIR control-flow preparation: back edges and per-block control places.

use crate::translate::net::PlaceId;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::{BasicBlock, Body, TerminatorKind};

/// Successor basic blocks from a terminator (skips cleanup/unreachable targets).
fn terminator_successors(
    body: &Body<'_>,
    bb: &rustc_middle::mir::BasicBlockData<'_>,
) -> Vec<BasicBlock> {
    let Some(term) = &bb.terminator else {
        return vec![];
    };
    let mut succs = Vec::new();
    let exclude = |t: BasicBlock| {
        let target_bb = &body.basic_blocks[t];
        target_bb.is_cleanup || target_bb.is_empty_unreachable()
    };
    match &term.kind {
        TerminatorKind::Goto { target, .. } => {
            if !exclude(*target) {
                succs.push(*target);
            }
        }
        TerminatorKind::SwitchInt { targets, .. } => {
            for t in targets.all_targets() {
                if !exclude(*t) {
                    succs.push(*t);
                }
            }
        }
        TerminatorKind::Call { target, .. } => {
            if let Some(t) = target {
                if !exclude(*t) {
                    succs.push(*t);
                }
            }
        }
        TerminatorKind::Assert { target, .. } => {
            if !exclude(*target) {
                succs.push(*target);
            }
        }
        TerminatorKind::Drop { target, .. } => {
            if !exclude(*target) {
                succs.push(*target);
            }
        }
        TerminatorKind::FalseEdge { real_target, .. } => {
            if !exclude(*real_target) {
                succs.push(*real_target);
            }
        }
        TerminatorKind::FalseUnwind { real_target, .. } => {
            if !exclude(*real_target) {
                succs.push(*real_target);
            }
        }
        TerminatorKind::Yield { resume, .. } => {
            if !exclude(*resume) {
                succs.push(*resume);
            }
        }
        TerminatorKind::InlineAsm { targets, .. } => {
            if let Some(t) = targets.first() {
                if !exclude(*t) {
                    succs.push(*t);
                }
            }
        }
        _ => {}
    }
    succs
}

/// DFS from `bb0` to classify back edges `(u, v)` where `v` is an ancestor of `u`.
pub fn compute_back_edges(body: &Body<'_>) -> FxHashSet<(BasicBlock, BasicBlock)> {
    let mut back_edges = FxHashSet::default();
    let mut in_stack = FxHashSet::default();
    let mut visited = FxHashSet::default();

    fn dfs(
        body: &Body<'_>,
        u: BasicBlock,
        in_stack: &mut FxHashSet<BasicBlock>,
        visited: &mut FxHashSet<BasicBlock>,
        back_edges: &mut FxHashSet<(BasicBlock, BasicBlock)>,
    ) {
        let bb = &body.basic_blocks[u];
        if bb.is_cleanup || bb.is_empty_unreachable() {
            return;
        }
        if visited.contains(&u) {
            return;
        }

        in_stack.insert(u);

        for v in terminator_successors(body, bb) {
            if in_stack.contains(&v) {
                back_edges.insert((u, v));
            } else if !visited.contains(&v) {
                dfs(body, v, in_stack, visited, back_edges);
            }
        }

        in_stack.remove(&u);
        visited.insert(u);
    }

    let entry = BasicBlock::from_u32(0);
    dfs(body, entry, &mut in_stack, &mut visited, &mut back_edges);

    back_edges
}

#[derive(Default)]
pub(super) struct BasicBlockGraph {
    pub start_places: FxHashMap<BasicBlock, PlaceId>,
    pub sequences: FxHashMap<BasicBlock, Vec<PlaceId>>,
}

impl BasicBlockGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register(&mut self, bb: BasicBlock, start: PlaceId) {
        self.start_places.insert(bb, start);
        self.sequences.insert(bb, vec![start]);
    }

    pub fn push(&mut self, bb: BasicBlock, place: PlaceId) {
        self.sequences.entry(bb).or_default().push(place);
    }

    pub fn start(&self, bb: BasicBlock) -> PlaceId {
        self.start_opt(bb)
            .expect("basic block start place should exist")
    }

    /// The start place when the block was registered; `None` for excluded
    /// (cleanup / unreachable) blocks.
    pub fn start_opt(&self, bb: BasicBlock) -> Option<PlaceId> {
        self.start_places.get(&bb).copied()
    }

    pub fn last(&self, bb: BasicBlock) -> PlaceId {
        self.last_opt(bb)
            .expect("basic block last node should exist")
    }

    /// The last place when the block was registered; `None` for excluded
    /// blocks.
    pub fn last_opt(&self, bb: BasicBlock) -> Option<PlaceId> {
        self.sequences
            .get(&bb)
            .and_then(|nodes| nodes.last())
            .copied()
    }
}

#[derive(Default)]
pub(super) struct SegState {
    pub seg_index: FxHashMap<usize, usize>,
    pub seg_place_of: FxHashMap<(usize, usize), PlaceId>,
    pub seqcst_place: Option<PlaceId>,
}

impl SegState {
    pub fn current_seg(&self, tid: usize) -> usize {
        *self.seg_index.get(&tid).unwrap_or(&0)
    }

    pub fn bump(&mut self, tid: usize) -> usize {
        let next = self.current_seg(tid) + 1;
        self.seg_index.insert(tid, next);
        next
    }
}
