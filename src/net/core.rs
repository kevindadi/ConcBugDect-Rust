//! Runtime: enabled sets, firing semantics, and conflict checks.
use std::fmt::{self, Write as FmtWrite};
use std::fs;
use std::path::Path;

use thiserror::Error;

use crate::net::ids::{PlaceId, TransitionId};
use crate::net::incidence::Incidence;
#[cfg(feature = "inhibitor")]
use crate::net::incidence::IncidenceBool;
use crate::net::index_vec::{Idx, IndexVec};
use crate::net::structure::{Marking, Place, Transition, Weight};

#[cfg(feature = "invariants")]
use num::bigint::BigInt;
#[cfg(feature = "invariants")]
use num::integer::Integer;
#[cfg(feature = "invariants")]
use num::rational::BigRational;
#[cfg(feature = "invariants")]
use num::traits::{One, Signed, Zero};

#[derive(Debug, Error)]
pub enum FireError {
    #[error("transition {0:?} is out of bounds")]
    OutOfBounds(TransitionId),
    #[error("transition {0:?} is not enabled under the supplied marking")]
    NotEnabled(TransitionId),
    #[error("transition {transition:?} conflicts on place {place:?}")]
    Conflict {
        transition: TransitionId,
        place: PlaceId,
    },
    #[error("capacity exceeded at place {place:?}: {after} > {capacity}")]
    Capacity {
        place: PlaceId,
        after: Weight,
        capacity: Weight,
    },
    #[error("no enabled transitions under the supplied marking")]
    Deadlock,
    #[error("fire_plan contains non-sequential step with {0} transitions")]
    NonSequentialStep(usize),
}

/// Petri net connectivity diagnostic report.
#[derive(Debug, Clone, Default)]
pub struct DiagnosticReport {
    /// Places with no incident arcs.
    pub isolated_places: Vec<(PlaceId, String)>,
    /// Transitions with no incident arcs.
    pub isolated_transitions: Vec<(TransitionId, String)>,
    /// Warning messages.
    pub warnings: Vec<String>,
    /// Total place count.
    pub total_places: usize,
    /// Total transition count.
    pub total_transitions: usize,
}

impl DiagnosticReport {
    /// Whether any issue was found.
    pub fn has_issues(&self) -> bool {
        !self.isolated_places.is_empty()
            || !self.isolated_transitions.is_empty()
            || !self.warnings.is_empty()
    }

    /// Write this report to a text file.
    pub fn save_to_file(&self, path: &str) -> std::io::Result<()> {
        use std::io::Write;
        let mut file = fs::File::create(path)?;

        writeln!(file, "=== Petri net connectivity diagnostics ===")?;
        writeln!(
            file,
            "Totals: {} places, {} transitions",
            self.total_places, self.total_transitions
        )?;
        writeln!(file)?;

        if !self.isolated_places.is_empty() {
            writeln!(file, "Isolated places ({}):", self.isolated_places.len())?;
            for (id, name) in &self.isolated_places {
                writeln!(file, "  [{}] {}", id.index(), name)?;
            }
            writeln!(file)?;
        }

        if !self.isolated_transitions.is_empty() {
            writeln!(
                file,
                "Isolated transitions ({}):",
                self.isolated_transitions.len()
            )?;
            for (id, name) in &self.isolated_transitions {
                writeln!(file, "  [{}] {}", id.index(), name)?;
            }
            writeln!(file)?;
        }

        if !self.warnings.is_empty() {
            writeln!(file, "Warnings ({}):", self.warnings.len())?;
            for warning in &self.warnings {
                writeln!(file, "  - {}", warning)?;
            }
        }

        Ok(())
    }
}

#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct Net {
    pub places: IndexVec<PlaceId, Place>,
    pub transitions: IndexVec<TransitionId, Transition>,
    pub pre: Incidence<u64>,
    pub post: Incidence<u64>,
    pub capacity: Option<IndexVec<PlaceId, Weight>>,
    #[cfg(feature = "inhibitor")]
    pub inhibitor: Option<IncidenceBool>,
    #[cfg(feature = "reset")]
    pub reset: Option<IncidenceBool>,
}

impl fmt::Debug for Net {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Net")
            .field("places", &self.places)
            .field("transitions", &self.transitions)
            .field("pre", &self.pre)
            .field("post", &self.post)
            .field("capacity", &self.capacity)
            .finish()
    }
}

impl Net {
    pub fn empty() -> Self {
        Self {
            places: IndexVec::new(),
            transitions: IndexVec::new(),
            pre: Incidence::new(0, 0, 0u64),
            post: Incidence::new(0, 0, 0u64),
            capacity: None,
            #[cfg(feature = "inhibitor")]
            inhibitor: None,
            #[cfg(feature = "reset")]
            reset: None,
        }
    }

    pub fn new(
        places: IndexVec<PlaceId, Place>,
        transitions: IndexVec<TransitionId, Transition>,
        pre: Incidence<u64>,
        post: Incidence<u64>,
        capacity: Option<IndexVec<PlaceId, Weight>>,
        #[cfg(feature = "inhibitor")] inhibitor: Option<IncidenceBool>,
        #[cfg(feature = "reset")] reset: Option<IncidenceBool>,
    ) -> Self {
        Self {
            places,
            transitions,
            pre,
            post,
            capacity,
            #[cfg(feature = "inhibitor")]
            inhibitor,
            #[cfg(feature = "reset")]
            reset,
        }
    }

    pub fn add_place(&mut self, place: Place) -> PlaceId {
        let capacity_value = place.capacity;
        let place_id = self.places.push(place);
        self.pre.push_place_with_default(0);
        self.post.push_place_with_default(0);

        if let Some(capacity_vec) = self.capacity.as_mut() {
            capacity_vec.push(capacity_value);
        }
        #[cfg(feature = "inhibitor")]
        if let Some(inhibitor) = self.inhibitor.as_mut() {
            inhibitor.push_place();
        }
        #[cfg(feature = "reset")]
        if let Some(reset) = self.reset.as_mut() {
            reset.push_place();
        }
        place_id
    }

    pub fn add_transition(&mut self, transition: Transition) -> TransitionId {
        let transition_id = self.transitions.push(transition);
        self.pre.push_transition_with_default(0);
        self.post.push_transition_with_default(0);
        #[cfg(feature = "inhibitor")]
        if let Some(inhibitor) = self.inhibitor.as_mut() {
            inhibitor.push_transition();
        }
        #[cfg(feature = "reset")]
        if let Some(reset) = self.reset.as_mut() {
            reset.push_transition();
        }
        transition_id
    }

    pub fn set_input_weight(&mut self, place: PlaceId, transition: TransitionId, weight: Weight) {
        self.pre.set(place, transition, weight);
    }

    pub fn set_output_weight(&mut self, place: PlaceId, transition: TransitionId, weight: Weight) {
        self.post.set(place, transition, weight);
    }

    /// Input arc: place → transition, weight typically 1.
    pub fn add_input_arc(&mut self, place: PlaceId, transition: TransitionId, weight: Weight) {
        if weight == 0 {
            return;
        }
        let entry = self.pre.get_mut(place, transition);
        *entry += weight;
    }

    /// Output arc: transition → place, weight typically 1.
    pub fn add_output_arc(&mut self, place: PlaceId, transition: TransitionId, weight: Weight) {
        if weight == 0 {
            return;
        }
        let entry = self.post.get_mut(place, transition);
        *entry += weight;
    }

    pub fn get_place(&self, place: PlaceId) -> Option<&Place> {
        self.places.get(place)
    }

    pub fn get_place_mut(&mut self, place: PlaceId) -> Option<&mut Place> {
        self.places.get_mut(place)
    }

    pub fn get_transition(&self, transition: TransitionId) -> Option<&Transition> {
        self.transitions.get(transition)
    }

    pub fn get_transition_mut(&mut self, transition: TransitionId) -> Option<&mut Transition> {
        self.transitions.get_mut(transition)
    }

    #[cfg(feature = "inhibitor")]
    pub fn set_inhibitor_arc(&mut self, place: PlaceId, transition: TransitionId, value: bool) {
        if self.inhibitor.is_none() {
            self.inhibitor = Some(IncidenceBool::new(
                self.pre.places(),
                self.pre.transitions(),
            ));
        }
        if let Some(matrix) = self.inhibitor.as_mut() {
            matrix.set(place, transition, value);
        }
    }

    #[cfg(feature = "reset")]
    pub fn set_reset_arc(&mut self, place: PlaceId, transition: TransitionId, value: bool) {
        if self.reset.is_none() {
            self.reset = Some(IncidenceBool::new(
                self.pre.places(),
                self.pre.transitions(),
            ));
        }
        if let Some(matrix) = self.reset.as_mut() {
            matrix.set(place, transition, value);
        }
    }

    pub fn places_len(&self) -> usize {
        self.places.len()
    }

    pub fn transitions_len(&self) -> usize {
        self.transitions.len()
    }

    pub fn initial_marking(&self) -> Marking {
        Marking(IndexVec::from(
            self.places.iter().map(|p| p.tokens).collect::<Vec<_>>(),
        ))
    }

    pub fn incidence(&self) -> (&Incidence<u64>, &Incidence<u64>) {
        (&self.pre, &self.post)
    }

    pub fn c_matrix(&self) -> Incidence<i64> {
        self.post.difference(&self.pre)
    }

    pub fn to_dot(&self) -> String {
        let mut dot = String::new();
        let _ = writeln!(&mut dot, "digraph PetriNet {{");
        let _ = writeln!(&mut dot, "    rankdir=LR;");
        let _ = writeln!(&mut dot, "    node [fontname=\"Helvetica\"];");

        for (place_id, place) in self.places.iter_enumerated() {
            let node_id = format!("place_{}", place_id.index());
            let label = format!(
                "{}\\n{:?}\\n{}/{}",
                escape_label(&place.name),
                place.place_type,
                place.tokens,
                place.capacity
            );
            let _ = writeln!(
                &mut dot,
                "    {} [label=\"{}\", shape=circle, style=filled, fillcolor=\"#e3f2fd\"];",
                node_id, label
            );
        }

        for (transition_id, transition) in self.transitions.iter_enumerated() {
            let node_id = format!("trans_{}", transition_id.index());
            let transition_ty = format!("{:?}", transition.transition_type);
            let label = format!(
                "{}\\n{}",
                escape_label(&transition.name),
                escape_label(&transition_ty)
            );
            let _ = writeln!(
                &mut dot,
                "    {} [label=\"{}\", shape=box, style=filled, fillcolor=\"#ffe0b2\"];",
                node_id, label
            );
        }

        for (place_id, row) in self.pre.rows().iter_enumerated() {
            let place_node = format!("place_{}", place_id.index());
            for (idx, weight) in row.iter().enumerate() {
                if *weight == 0 {
                    continue;
                }
                let transition_node = format!("trans_{}", idx);
                if *weight == 1 {
                    let _ = writeln!(&mut dot, "    {} -> {};", place_node, transition_node);
                } else {
                    let _ = writeln!(
                        &mut dot,
                        "    {} -> {} [label=\"{}\"];",
                        place_node, transition_node, weight
                    );
                }
            }
        }

        for (place_id, row) in self.post.rows().iter_enumerated() {
            let place_node = format!("place_{}", place_id.index());
            for (idx, weight) in row.iter().enumerate() {
                if *weight == 0 {
                    continue;
                }
                let transition_node = format!("trans_{}", idx);
                if *weight == 1 {
                    let _ = writeln!(&mut dot, "    {} -> {};", transition_node, place_node);
                } else {
                    let _ = writeln!(
                        &mut dot,
                        "    {} -> {} [label=\"{}\"];",
                        transition_node, place_node, weight
                    );
                }
            }
        }

        let _ = writeln!(&mut dot, "}}");
        dot
    }

    pub fn write_dot<P: AsRef<Path>>(&self, path: P) -> std::io::Result<()> {
        if let Some(parent) = path.as_ref().parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, self.to_dot())
    }

    /// Connectivity diagnostics: find isolated nodes and suspicious wiring.
    /// Returns isolated places, isolated transitions, and warning strings.
    pub fn diagnose_connectivity(&self) -> DiagnosticReport {
        let mut isolated_places = Vec::new();
        let mut isolated_transitions = Vec::new();
        let mut warnings = Vec::new();

        // Check arc incidence for each place.
        for (place_id, place) in self.places.iter_enumerated() {
            let has_outgoing = self.pre.rows()[place_id].iter().any(|w| *w > 0);
            let has_incoming = self.post.rows()[place_id].iter().any(|w| *w > 0);

            if !has_incoming && !has_outgoing {
                isolated_places.push((place_id, place.name.clone()));
            } else if !has_incoming && place.tokens == 0 {
                if !matches!(
                    place.place_type,
                    crate::net::structure::PlaceType::FunctionStart
                ) || !place.name.ends_with("main_start")
                {
                    warnings.push(format!(
                        "Place '{}' (id={}) has no input arcs and initial marking 0 (never activated)",
                        place.name,
                        place_id.index()
                    ));
                }
            } else if !has_outgoing {
                if !matches!(
                    place.place_type,
                    crate::net::structure::PlaceType::FunctionEnd
                ) || !place.name.ends_with("main_end")
                {
                    warnings.push(format!(
                        "Place '{}' (id={}) has no output arcs (sink); verify this is intended",
                        place.name,
                        place_id.index()
                    ));
                }
            }
        }

        // Check arc incidence for each transition.
        for (trans_id, trans) in self.transitions.iter_enumerated() {
            let has_preset = self
                .pre
                .rows()
                .iter()
                .any(|row| row.get(trans_id.index()).map_or(false, |w| *w > 0));
            let has_postset = self
                .post
                .rows()
                .iter()
                .any(|row| row.get(trans_id.index()).map_or(false, |w| *w > 0));

            if !has_preset && !has_postset {
                isolated_transitions.push((trans_id, trans.name.clone()));
            } else if !has_preset {
                warnings.push(format!(
                    "Transition '{}' (id={}) has no preset places (never fireable)",
                    trans.name,
                    trans_id.index()
                ));
            } else if !has_postset {
                warnings.push(format!(
                    "Transition '{}' (id={}) has no postset places; verify this is intended",
                    trans.name,
                    trans_id.index()
                ));
            }
        }

        DiagnosticReport {
            isolated_places,
            isolated_transitions,
            warnings,
            total_places: self.places_len(),
            total_transitions: self.transitions_len(),
        }
    }

    /// Print diagnostics to the log.
    pub fn log_diagnostics(&self) {
        let report = self.diagnose_connectivity();

        if report.has_issues() {
            log::warn!("=== Petri net connectivity diagnostics ===");
            log::warn!(
                "Totals: {} places, {} transitions",
                report.total_places,
                report.total_transitions
            );

            if !report.isolated_places.is_empty() {
                log::warn!("Found {} isolated places:", report.isolated_places.len());
                for (id, name) in &report.isolated_places {
                    log::warn!("  - [{}] {}", id.index(), name);
                }
            }

            if !report.isolated_transitions.is_empty() {
                log::warn!(
                    "Found {} isolated transitions:",
                    report.isolated_transitions.len()
                );
                for (id, name) in &report.isolated_transitions {
                    log::warn!("  - [{}] {}", id.index(), name);
                }
            }

            if !report.warnings.is_empty() {
                log::warn!("Other warnings ({}):", report.warnings.len());
                for warning in &report.warnings {
                    log::warn!("  - {}", warning);
                }
            }
            log::warn!("=== End diagnostics ===");
        } else {
            log::info!("Petri net connectivity OK (no isolated nodes)");
        }
    }

    pub fn enabled_transitions(&self, marking: &Marking) -> Vec<TransitionId> {
        self.transitions
            .iter()
            .enumerate()
            .filter_map(|(idx, _)| {
                let transition = TransitionId::from_usize(idx);
                if self.is_transition_enabled(transition, marking) {
                    Some(transition)
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn fire_transition(
        &self,
        marking: &Marking,
        transition: TransitionId,
    ) -> Result<Marking, FireError> {
        if transition.index() >= self.transitions_len() {
            return Err(FireError::OutOfBounds(transition));
        }
        if !self.is_transition_enabled(transition, marking) {
            return Err(FireError::NotEnabled(transition));
        }

        let mut next = marking.clone();

        for (place, _) in self.places.iter_enumerated() {
            let weight = *self.pre.get(place, transition);
            if weight > 0 {
                let tokens = next.tokens_mut(place);
                *tokens = tokens
                    .checked_sub(weight)
                    .expect("enabled transition must have sufficient tokens");
            }
        }

        for (place, _) in self.places.iter_enumerated() {
            let weight = *self.post.get(place, transition);
            if weight > 0 {
                let tokens = next.tokens_mut(place);
                let after = *tokens + weight;
                let capacity = self
                    .capacity
                    .as_ref()
                    .map(|caps| caps[place])
                    .unwrap_or(self.places[place].capacity);
                *tokens = after.min(capacity);
            }
        }

        #[cfg(feature = "reset")]
        if let Some(reset) = self.reset.as_ref() {
            for (place, _) in self.places.iter_enumerated() {
                if reset.get(place, transition) {
                    *next.tokens_mut(place) = 0;
                }
            }
        }

        Ok(next)
    }

    fn is_transition_enabled(&self, transition: TransitionId, marking: &Marking) -> bool {
        if transition.index() >= self.transitions_len() {
            return false;
        }
        for (place, row) in self.pre.rows().iter_enumerated() {
            let weight = row[transition.index()];
            #[cfg(feature = "inhibitor")]
            if self.is_inhibitor_arc(place, transition) {
                if marking.tokens(place) >= weight {
                    return false;
                }
                continue;
            }
            if marking.tokens(place) < weight {
                return false;
            }
        }
        true
    }

    #[cfg(feature = "inhibitor")]
    fn is_inhibitor_arc(&self, place: PlaceId, transition: TransitionId) -> bool {
        self.inhibitor
            .as_ref()
            .map(|matrix| matrix.get(place, transition))
            .unwrap_or(false)
    }

    #[cfg(not(feature = "inhibitor"))]
    #[allow(unused)]
    fn is_inhibitor_arc(&self, _place: PlaceId, _transition: TransitionId) -> bool {
        false
    }
}

impl Default for Net {
    fn default() -> Self {
        Self::empty()
    }
}

fn escape_label(input: &str) -> String {
    let mut escaped = String::with_capacity(input.len());
    for ch in input.chars() {
        match ch {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            _ => escaped.push(ch),
        }
    }
    escaped
}

#[cfg(feature = "invariants")]
impl Net {
    pub fn transition_invariants(&self) -> Vec<Vec<BigInt>> {
        let matrix = self.c_matrix();
        let rows = matrix.rows();
        let mut data = Vec::with_capacity(rows.len());
        for row in rows.iter() {
            let mut vec = Vec::with_capacity(row.len());
            for value in row.iter() {
                vec.push(BigInt::from(*value));
            }
            data.push(vec);
        }
        compute_nullspace(&data, self.transitions_len())
    }

    pub fn place_invariants(&self) -> Vec<Vec<BigInt>> {
        let matrix = self.c_matrix();
        let places = self.places_len();
        let transitions = self.transitions_len();
        let mut transposed = vec![vec![BigInt::from(0); places]; transitions];
        for (place, row) in matrix.rows().iter_enumerated() {
            for (transition_idx, value) in row.iter().enumerate() {
                transposed[transition_idx][place.index()] = BigInt::from(*value);
            }
        }
        compute_nullspace(&transposed, places)
    }
}

#[cfg(feature = "invariants")]
fn compute_nullspace(matrix: &[Vec<BigInt>], cols: usize) -> Vec<Vec<BigInt>> {
    if cols == 0 {
        return Vec::new();
    }

    let rows = matrix.len();
    if rows == 0 {
        return (0..cols)
            .map(|free_col| {
                let mut vector = vec![BigInt::from(0); cols];
                vector[free_col] = BigInt::from(1);
                vector
            })
            .collect();
    }

    let mut rref = matrix
        .iter()
        .map(|row| {
            (0..cols)
                .map(|idx| row.get(idx).cloned().unwrap_or_else(BigInt::zero).into())
                .collect::<Vec<BigRational>>()
        })
        .collect::<Vec<_>>();

    let mut pivot_cols = Vec::new();
    let mut pivot_row = 0usize;

    for col in 0..cols {
        if pivot_row >= rows {
            break;
        }
        let mut pivot = None;
        for row in pivot_row..rows {
            if !rref[row][col].is_zero() {
                pivot = Some(row);
                break;
            }
        }
        let Some(row_idx) = pivot else {
            continue;
        };

        if row_idx != pivot_row {
            rref.swap(row_idx, pivot_row);
        }

        let pivot_value = rref[pivot_row][col].clone();
        for value in rref[pivot_row].iter_mut() {
            *value /= pivot_value.clone();
        }

        for row in 0..rows {
            if row == pivot_row {
                continue;
            }
            let factor = rref[row][col].clone();
            if factor.is_zero() {
                continue;
            }
            for inner_col in col..cols {
                let adjustment = rref[pivot_row][inner_col].clone() * factor.clone();
                rref[row][inner_col] -= adjustment;
            }
        }

        pivot_cols.push(col);
        pivot_row += 1;
    }

    let mut pivot_flags = vec![false; cols];
    for &col in &pivot_cols {
        pivot_flags[col] = true;
    }

    let free_cols = (0..cols)
        .filter(|&col| !pivot_flags[col])
        .collect::<Vec<_>>();

    if free_cols.is_empty() {
        return Vec::new();
    }

    let mut basis = Vec::new();

    for &free_col in &free_cols {
        let mut vector = vec![BigRational::from_integer(BigInt::zero()); cols];
        vector[free_col] = BigRational::one();
        for (pivot_index, &pivot_col) in pivot_cols.iter().enumerate() {
            let coeff = rref[pivot_index][free_col].clone();
            if !coeff.is_zero() {
                vector[pivot_col] = -coeff;
            }
        }
        basis.push(rational_vector_to_integer(vector));
    }

    basis
        .into_iter()
        .map(normalize_integer_vector)
        .collect::<Vec<_>>()
}

#[cfg(feature = "invariants")]
fn rational_vector_to_integer(vector: Vec<BigRational>) -> Vec<BigInt> {
    let mut lcm = BigInt::one();
    for value in &vector {
        let denom = value.denom();
        if denom.is_zero() {
            continue;
        }
        lcm = lcm.lcm(denom);
    }

    vector
        .into_iter()
        .map(|value| {
            let numer = value.numer().clone();
            let denom = value.denom().clone();
            if denom.is_zero() {
                BigInt::zero()
            } else {
                let scale = &lcm / denom;
                numer * scale
            }
        })
        .collect()
}

#[cfg(feature = "invariants")]
fn normalize_integer_vector(mut vector: Vec<BigInt>) -> Vec<BigInt> {
    let mut gcd = BigInt::zero();
    for value in &vector {
        if value.is_zero() {
            continue;
        }
        let abs = value.abs();
        gcd = if gcd.is_zero() { abs } else { gcd.gcd(&abs) };
    }

    if !gcd.is_zero() && gcd != BigInt::one() {
        for value in &mut vector {
            *value /= gcd.clone();
        }
    }

    vector
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::net::structure::PlaceType;
    #[test]
    fn add_place_and_transition_updates_incidence() {
        let mut net = Net::empty();
        let p = net.add_place(Place::new("p", 1, 5, PlaceType::BasicBlock, String::new()));
        let t = net.add_transition(Transition::new("t"));

        net.set_input_weight(p, t, 1);
        net.set_output_weight(p, t, 1);

        assert_eq!(net.places_len(), 1);
        assert_eq!(net.transitions_len(), 1);
        assert_eq!(*net.pre.get(p, t), 1);
        assert_eq!(*net.post.get(p, t), 1);
    }

    #[test]
    fn diagnostics_accept_main_entry_and_exit_but_warn_other_disconnected_function_places() {
        let mut net = Net::empty();
        let main_start = net.add_place(Place::new(
            "inter::main_start",
            1,
            1,
            PlaceType::FunctionStart,
            String::new(),
        ));
        let main_end = net.add_place(Place::new(
            "inter::main_end",
            0,
            1,
            PlaceType::FunctionEnd,
            String::new(),
        ));
        let helper_start = net.add_place(Place::new(
            "inter::helper_start",
            0,
            1,
            PlaceType::FunctionStart,
            String::new(),
        ));
        let helper_end = net.add_place(Place::new(
            "inter::helper_end",
            0,
            1,
            PlaceType::FunctionEnd,
            String::new(),
        ));
        let enter_main = net.add_transition(Transition::new("enter_main"));
        let leave_main = net.add_transition(Transition::new("leave_main"));
        let enter_helper = net.add_transition(Transition::new("enter_helper"));
        let leave_helper = net.add_transition(Transition::new("leave_helper"));

        net.add_input_arc(main_start, enter_main, 1);
        net.add_output_arc(main_end, leave_main, 1);
        net.add_input_arc(helper_start, enter_helper, 1);
        net.add_output_arc(helper_end, leave_helper, 1);

        let report = net.diagnose_connectivity();
        let warnings = report.warnings.join("\n");

        assert!(!warnings.contains("inter::main_start"));
        assert!(!warnings.contains("inter::main_end"));
        assert!(warnings.contains("inter::helper_start"));
        assert!(warnings.contains("inter::helper_end"));
    }

    #[cfg(feature = "invariants")]
    #[test]
    fn invariants_simple_cycle() {
        let mut net = Net::empty();
        let p0 = net.add_place(Place::new(
            "p0",
            1,
            10,
            PlaceType::BasicBlock,
            String::new(),
        ));
        let p1 = net.add_place(Place::new(
            "p1",
            0,
            10,
            PlaceType::BasicBlock,
            String::new(),
        ));
        let t0 = net.add_transition(Transition::new("t0"));
        let t1 = net.add_transition(Transition::new("t1"));

        net.set_input_weight(p0, t0, 1);
        net.set_output_weight(p1, t0, 1);
        net.set_input_weight(p1, t1, 1);
        net.set_output_weight(p0, t1, 1);

        let p_invariants = net.place_invariants();
        let t_invariants = net.transition_invariants();

        assert!(p_invariants.iter().any(|vec| {
            vec.iter().map(|value| value.abs()).collect::<Vec<_>>()
                == vec![BigInt::from(1), BigInt::from(1)]
        }));
        assert!(t_invariants.iter().any(|vec| {
            vec.iter().map(|value| value.abs()).collect::<Vec<_>>()
                == vec![BigInt::from(1), BigInt::from(1)]
        }));
    }
}
