//! Async-related bug hooks.
//!
//! A) holding-lock-across-await — paths where `lock(m)` happens before `unlock(m)` but cross `await_pending`.
//! B) cancel-safety leaks — after abort, resource places fail to return to their idle marking.

use crate::transition::AsyncTransitionKind;

/// Placeholder: detect locks held across `.await`.
#[allow(dead_code)]
pub fn detect_holding_lock_across_await(
    _kinds: &[AsyncTransitionKind],
) -> Option<Vec<(usize, usize)>> {
    None
}

/// Placeholder: resource leaks after cancellation.
#[allow(dead_code)]
pub fn detect_cancel_safety_resource_leak(
    _abort_task_id: usize,
    _resource_places: &[(usize, u64)],
) -> Option<Vec<usize>> {
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn holding_lock_across_await_stub_returns_none() {
        assert!(detect_holding_lock_across_await(&[]).is_none());
    }

    #[test]
    fn cancel_safety_stub_returns_none() {
        assert!(detect_cancel_safety_resource_leak(0, &[]).is_none());
    }
}
