//! Resource-place construction. Calls `net` and does not name `unipn`.
//! `lock_binder` handles locks only; `bind_resources` handles the places and
//! `PlaceBinding` for locks/atomics/unsafe/condvars.

mod bind;
pub(crate) mod lock_binder;
mod predicates;
mod shadow;

pub use bind::PlaceBinding;
pub(crate) use bind::{add_lock_place, install_custom_lock_groups};
