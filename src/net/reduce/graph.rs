use crate::net::Net;
use crate::net::ids::{PlaceId, TransitionId};
use crate::net::incidence::Incidence;
use crate::net::index_vec::{Idx, IndexVec};
use crate::net::structure::{Place, Transition, TransitionType, Weight};

use super::ReductionTrace;

pub(crate) struct ReductionGraph {
    pub(crate) places: Vec<GraphPlace>,
    pub(crate) transitions: Vec<GraphTransition>,
    pub(crate) merge_counter: usize,
    pub(crate) has_capacity: bool,
    #[cfg(feature = "inhibitor")]
    pub(crate) has_inhibitor: bool,
    #[cfg(feature = "reset")]
    pub(crate) has_reset: bool,
}

pub(crate) struct GraphPlace {
    pub(crate) place: Place,
    pub(crate) originals: Vec<PlaceId>,
    pub(crate) incoming: Vec<usize>,
    pub(crate) outgoing: Vec<usize>,
    pub(crate) removed: bool,
}

pub(crate) struct GraphTransition {
    pub(crate) transition: Transition,
    pub(crate) originals: Vec<TransitionId>,
    pub(crate) inputs: Vec<(usize, Weight)>,
    pub(crate) outputs: Vec<(usize, Weight)>,
    pub(crate) removed: bool,
}

pub(crate) struct MaterializedNet {
    pub(crate) net: Net,
    pub(crate) trace: ReductionTrace,
}

impl ReductionGraph {
    pub(crate) fn from_net(net: &Net) -> Self {
        let mut places = Vec::with_capacity(net.places_len());
        for (place_id, place) in net.places.iter_enumerated() {
            places.push(GraphPlace {
                place: place.clone(),
                originals: vec![place_id],
                incoming: Vec::new(),
                outgoing: Vec::new(),
                removed: false,
            });
        }

        let mut transitions = Vec::with_capacity(net.transitions_len());
        for (transition_id, transition) in net.transitions.iter_enumerated() {
            transitions.push(GraphTransition {
                transition: transition.clone(),
                originals: vec![transition_id],
                inputs: Vec::new(),
                outputs: Vec::new(),
                removed: false,
            });
        }

        for (place_id, row) in net.pre.rows().iter_enumerated() {
            for (idx, weight) in row.iter().enumerate() {
                if *weight == 0 {
                    continue;
                }
                let transition_id = TransitionId::from_usize(idx);
                let p_idx = place_id.index();
                let t_idx = transition_id.index();
                places[p_idx].outgoing.push(t_idx);
                transitions[t_idx].inputs.push((p_idx, *weight));
            }
        }

        for (place_id, row) in net.post.rows().iter_enumerated() {
            for (idx, weight) in row.iter().enumerate() {
                if *weight == 0 {
                    continue;
                }
                let transition_id = TransitionId::from_usize(idx);
                let p_idx = place_id.index();
                let t_idx = transition_id.index();
                places[p_idx].incoming.push(t_idx);
                transitions[t_idx].outputs.push((p_idx, *weight));
            }
        }

        Self {
            places,
            transitions,
            merge_counter: 0,
            has_capacity: net.capacity.is_some(),
            #[cfg(feature = "inhibitor")]
            has_inhibitor: net.inhibitor.is_some(),
            #[cfg(feature = "reset")]
            has_reset: net.reset.is_some(),
        }
    }

    pub(crate) fn materialize(&self) -> MaterializedNet {
        let mut place_mapping: Vec<Option<PlaceId>> = vec![None; self.places.len()];
        let mut transition_mapping: Vec<Option<TransitionId>> = vec![None; self.transitions.len()];

        let mut new_places: IndexVec<PlaceId, Place> = IndexVec::new();
        for (idx, place) in self.places.iter().enumerate() {
            if place.removed {
                continue;
            }
            let new_id = new_places.push(place.place.clone());
            place_mapping[idx] = Some(new_id);
        }

        let mut new_transitions: IndexVec<TransitionId, Transition> = IndexVec::new();
        for (idx, transition) in self.transitions.iter().enumerate() {
            if transition.removed {
                continue;
            }
            let new_id = new_transitions.push(transition.transition.clone());
            transition_mapping[idx] = Some(new_id);
        }

        let mut pre = Incidence::new(new_places.len(), new_transitions.len(), 0u64);
        let mut post = Incidence::new(new_places.len(), new_transitions.len(), 0u64);

        for (t_idx, transition) in self.transitions.iter().enumerate() {
            let Some(new_t) = transition_mapping[t_idx] else {
                continue;
            };
            for (place_idx, weight) in &transition.inputs {
                if let Some(new_p) = place_mapping[*place_idx] {
                    pre.set(new_p, new_t, *weight);
                }
            }
            for (place_idx, weight) in &transition.outputs {
                if let Some(new_p) = place_mapping[*place_idx] {
                    post.set(new_p, new_t, *weight);
                }
            }
        }

        let capacity = if self.has_capacity {
            let mut caps: IndexVec<PlaceId, Weight> = IndexVec::new();
            for place in new_places.iter() {
                caps.push(place.capacity);
            }
            Some(caps)
        } else {
            None
        };

        #[allow(unused_mut)]
        let mut new_net = Net::new(
            new_places.clone(),
            new_transitions.clone(),
            pre,
            post,
            capacity,
            #[cfg(feature = "inhibitor")]
            None,
            #[cfg(feature = "reset")]
            None,
        );

        let mut place_trace_data = vec![Vec::new(); new_places.len()];
        for (idx, place) in self.places.iter().enumerate() {
            if let Some(new_id) = place_mapping[idx] {
                place_trace_data[new_id.index()] = place.originals.clone();
            }
        }
        let place_trace = IndexVec::from(place_trace_data);

        let mut transition_trace_data = vec![Vec::new(); new_transitions.len()];
        for (idx, transition) in self.transitions.iter().enumerate() {
            if let Some(new_id) = transition_mapping[idx] {
                transition_trace_data[new_id.index()] = transition.originals.clone();
            }
        }
        let transition_trace = IndexVec::from(transition_trace_data);

        MaterializedNet {
            net: new_net,
            trace: ReductionTrace {
                place_mapping: place_trace,
                transition_mapping: transition_trace,
            },
        }
    }

    pub(crate) fn add_transition(&mut self, transition: GraphTransition) -> usize {
        self.transitions.push(transition);
        self.transitions.len() - 1
    }

    pub(crate) fn remove_transition(&mut self, idx: usize) {
        if idx >= self.transitions.len() || self.transitions[idx].removed {
            return;
        }
        let inputs = self.transitions[idx].inputs.clone();
        let outputs = self.transitions[idx].outputs.clone();
        for (place_idx, _) in inputs {
            if let Some(place) = self.places.get_mut(place_idx) {
                place.outgoing.retain(|t| *t != idx);
            }
        }
        for (place_idx, _) in outputs {
            if let Some(place) = self.places.get_mut(place_idx) {
                place.incoming.retain(|t| *t != idx);
            }
        }
        self.transitions[idx].inputs.clear();
        self.transitions[idx].outputs.clear();
        self.transitions[idx].removed = true;
    }

    pub(crate) fn remove_place(&mut self, idx: usize) {
        if idx >= self.places.len() || self.places[idx].removed {
            return;
        }
        let incoming = self.places[idx].incoming.clone();
        let outgoing = self.places[idx].outgoing.clone();
        for transition_idx in incoming {
            if let Some(transition) = self.transitions.get_mut(transition_idx) {
                transition
                    .outputs
                    .retain(|(place_idx, _)| *place_idx != idx);
            }
        }
        for transition_idx in outgoing {
            if let Some(transition) = self.transitions.get_mut(transition_idx) {
                transition.inputs.retain(|(place_idx, _)| *place_idx != idx);
            }
        }
        self.places[idx].incoming.clear();
        self.places[idx].outgoing.clear();
        self.places[idx].removed = true;
    }

    pub(crate) fn clean_adjacency(&mut self) {
        for place in &mut self.places {
            place
                .incoming
                .retain(|idx| *idx < self.transitions.len() && !self.transitions[*idx].removed);
            place
                .outgoing
                .retain(|idx| *idx < self.transitions.len() && !self.transitions[*idx].removed);
        }
        for transition in &mut self.transitions {
            if transition.removed {
                continue;
            }
            transition
                .inputs
                .retain(|(idx, _)| *idx < self.places.len() && !self.places[*idx].removed);
            transition
                .outputs
                .retain(|(idx, _)| *idx < self.places.len() && !self.places[*idx].removed);
        }
    }
}

impl GraphTransition {
    pub(crate) fn new_with_type(
        name: String,
        transition_type: TransitionType,
        originals: Vec<TransitionId>,
        inputs: Vec<(usize, Weight)>,
        outputs: Vec<(usize, Weight)>,
    ) -> Self {
        Self {
            transition: Transition::new_with_transition_type(name, transition_type),
            originals,
            inputs,
            outputs,
            removed: false,
        }
    }
}
