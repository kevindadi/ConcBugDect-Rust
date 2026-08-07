//! # Petri net core (Place/Transition Net)
//!
//! Let `P` be the finite set of places and `T` the finite set of transitions, with cardinalities `|P|` and `|T|`.
//! Define input/output incidence matrices `Pre, Post ∈ ℕ^{|P|×|T|}` and effect matrix `C = Post - Pre`.
//! For any marking `M ∈ ℕ^{|P|}`:
//!
//! * A transition `t ∈ T` is **enabled** iff:
//!   1. ∀p ∈ P: M[p] ≥ Pre[p, t];
//!   2. If inhibitor arcs are enabled (`feature = "inhibitor"`), then for every inhibitor arc `(p, t)` we require
//!      M[p] < θ[p, t], where θ[p, t] is given by Pre[p, t];
//! * After firing, marking satisfies `M' = M + C[:, t]` subject to reset arcs: if `(p, t)` is a reset arc (`feature = "reset"`),
//!   then after firing we force `M'[p] = 0`.
//!
//! ## Example
//!
//! ```
//! use RustPTA::net::*;
//!
//! let mut net = Net::empty();
//! let p0 = net.add_place(Place::new_with_tokens_and_capacity("p0", 1, 1));
//! let p1 = net.add_place(Place::new_with_tokens_and_capacity("p1", 0, 1));
//! let t0 = net.add_transition(Transition::new("t0"));
//!
//! net.set_input_weight(p0, t0, 1);
//! net.set_output_weight(p1, t0, 1);
//!
//! let marking = net.initial_marking();
//! assert_eq!(net.enabled_transitions(&marking), vec![t0]);
//! let next = net.fire_transition(&marking, t0).unwrap();
//! assert_eq!(next.tokens(p0), 0);
//! assert_eq!(next.tokens(p1), 1);
//! ```
//!

pub mod core;
pub mod ids;
pub mod incidence;
pub mod index_vec;
pub mod io;
pub mod reduce;
pub mod structure;

pub use core::{DiagnosticReport, FireError, Net};
pub use ids::{PlaceId, TransitionId};
pub use incidence::{Incidence, IncidenceBool};
pub use index_vec::{Idx, IndexVec};
pub use structure::{Arc, ArcDirection, Marking, Place, Transition, TransitionType, Weight};
