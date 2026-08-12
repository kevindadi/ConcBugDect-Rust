//! Translation macros.
//!
//! - `transition_name!`: unified transition/place naming.
//! - `bb_place!`: create BasicBlock places.
//! - `add_fallthrough_transition!`: fallthrough transition + arcs.
//! - `add_terminal_transition!`: terminal transition + arcs.
//! - `add_wait_ret_subnet!`: wait place + ret transition subnet.

/// Build `{name}_{bb_idx}_{kind}` transition/place names.
/// Optional suffix: `transition_name!(name, bb_idx, kind, suffix)`.
#[macro_export]
macro_rules! transition_name {
    ($name:expr, $bb_idx:expr, $kind:expr) => {
        format!("{}_{}_{}", $name, $bb_idx.index(), $kind)
    };
    ($name:expr, $bb_idx:expr, $kind:expr, $suffix:expr) => {
        format!("{}_{}_{}{}", $name, $bb_idx.index(), $kind, $suffix)
    };
}

/// Create a BasicBlock place (`tokens = 0`, `capacity = 1`).
#[macro_export]
macro_rules! bb_place {
    ($net:expr, $name:expr, $span:expr) => {{
        let place = unipn::pt::PtPlace::new(
            $name,
            0,
            1,
            unipn::pt::PlaceType::BasicBlock,
            $span.into(),
        );
        $net.add_place(place)
    }};
}

/// Fallthrough transition wiring `last(bb_idx) -> t -> target`.
/// Returns `TransitionId`.
#[macro_export]
macro_rules! add_fallthrough_transition {
    ($self:expr, $bb_idx:expr, $name:expr, $kind:expr, $trans_type:expr, $target:expr) => {{
        let t_name = $crate::transition_name!($name, $bb_idx, $kind);
        let t = unipn::pt::PtTransition::new_with_transition_type(t_name, $trans_type);
        let t_id = $self.net.add_transition(t);
        $self
            .net
            .add_input_arc($self.bb_graph.last($bb_idx), t_id, 1);
        $self
            .net
            .add_output_arc($self.bb_graph.start(*$target), t_id, 1);
        t_id
    }};
}

/// Terminal transition wiring `last(bb_idx) -> t -> entry_exit.1`.
/// Returns `TransitionId`.
#[macro_export]
macro_rules! add_terminal_transition {
    ($self:expr, $bb_idx:expr, $name:expr, $kind:expr, $trans_type:expr) => {{
        let t_name = $crate::transition_name!($name, $bb_idx, $kind);
        let t = unipn::pt::PtTransition::new_with_transition_type(t_name, $trans_type);
        let t_id = $self.net.add_transition(t);
        $self
            .net
            .add_input_arc($self.bb_graph.last($bb_idx), t_id, 1);
        $self.net.add_output_arc($self.entry_exit.1, t_id, 1);
        t_id
    }};
}

/// Wait place + ret subnet (`wait -> bb_end`, `wait -> ret`).
/// Args: `self`, `name`, `bb_idx`, `kind_wait`, `kind_ret`, `trans_type`, `span`, `bb_end` (`TransitionId`).
/// Returns `(PlaceId, TransitionId)`.
#[macro_export]
macro_rules! add_wait_ret_subnet {
    ($self:expr, $name:expr, $bb_idx:expr, $kind_wait:expr, $kind_ret:expr, $trans_type:expr, $span:expr, $bb_end:expr) => {{
        let wait_name = $crate::transition_name!($name, $bb_idx, $kind_wait);
        let wait_place = $crate::bb_place!($self.net, wait_name, $span);
        let ret_name = $crate::transition_name!($name, $bb_idx, $kind_ret);
        let ret_t = unipn::pt::PtTransition::new_with_transition_type(ret_name, $trans_type);
        let ret_id = $self.net.add_transition(ret_t);
        $self.net.add_output_arc(wait_place, $bb_end, 1);
        $self.net.add_input_arc(wait_place, ret_id, 1);
        (wait_place, ret_id)
    }};
}
