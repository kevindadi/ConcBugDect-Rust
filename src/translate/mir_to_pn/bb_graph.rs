//! `BasicBlockGraph` and `SegState`: CFG shape and atomic-order segment state.

use crate::net::PlaceId;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::BasicBlock;

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
        *self
            .start_places
            .get(&bb)
            .expect("basic block start place should exist")
    }

    pub fn last(&self, bb: BasicBlock) -> PlaceId {
        *self
            .sequences
            .get(&bb)
            .and_then(|nodes| nodes.last())
            .expect("basic block last node should exist")
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
