//! Naming sugar only; construction goes through `NetBuilder` methods.
//!
//! `transition_name!` builds `{name}_{bb}_{kind}` labels. The other macros
//! only place the arcs the caller already chose; they do not decide control flow.

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

/// Create a BasicBlock place (`tokens = 0`, unbounded capacity).
///
/// Execution-position places must be unbounded: a function body (and every BB
/// place in it) is shared by all of its call sites, so two concurrent calls
/// deposit two tokens in the same place. Capacity 1 would silently *drop* the
/// second token (`produce_outputs_clamped`), stranding one caller forever;
/// an unbounded place queues the invocations instead.
#[macro_export]
macro_rules! bb_place {
    ($net:expr, $name:expr, $span:expr) => {{
        $net.add_place(
            $name,
            0,
            usize::MAX,
            unipn::PlaceClass::Control(unipn::ControlSub::BasicBlock),
            $span,
        )
    }};
}

/// Fallthrough transition wiring `last(bb_idx) -> t -> target`.
/// Returns `TransitionId`.
#[macro_export]
macro_rules! add_fallthrough_transition {
    ($self:expr, $bb_idx:expr, $name:expr, $kind:expr, $trans_type:expr, $target:expr) => {{
        let t_name = $crate::transition_name!($name, $bb_idx, $kind);
        let span = $self.bb_span($bb_idx);
        let t_id = $self.new_transition(t_name, $trans_type, $bb_idx, span);
        $self.net.arc_in($self.bb_graph.last($bb_idx), t_id, 1);
        $self.net.arc_out($self.bb_graph.start(*$target), t_id, 1);
        t_id
    }};
}

/// Terminal transition wiring `last(bb_idx) -> t -> frame_exit`, the current
/// frame's *own* function-end place (`entry_exit.1` only for `main`).
/// Returns `TransitionId`.
#[macro_export]
macro_rules! add_terminal_transition {
    ($self:expr, $bb_idx:expr, $name:expr, $kind:expr, $trans_type:expr) => {{
        let t_name = $crate::transition_name!($name, $bb_idx, $kind);
        let span = $self.bb_span($bb_idx);
        let t_id = $self.new_transition(t_name, $trans_type, $bb_idx, span);
        $self.net.arc_in($self.bb_graph.last($bb_idx), t_id, 1);
        $self.net.arc_out($self.frame_exit, t_id, 1);
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
        let wait_place = $crate::bb_place!($self.net, wait_name, $span.clone());
        let ret_name = $crate::transition_name!($name, $bb_idx, $kind_ret);
        let ret_id = $self.new_transition(ret_name, $trans_type, $bb_idx, $span);
        $self.net.arc_out(wait_place, $bb_end, 1);
        $self.net.arc_in(wait_place, ret_id, 1);
        (wait_place, ret_id)
    }};
}
