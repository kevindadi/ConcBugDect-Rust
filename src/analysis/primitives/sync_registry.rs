//! Names of synchronization operations, used to classify calls.
//! An empty table falls back to the regex lists in `PnConfig`.
//! It does not decide which functions are translated.

use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum SyncEffect {
    Acquire,
    Release,
    Wait,
    Notify,
    Join,
    Spawn,
    Summary,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum SyncResource {
    Mutex,
    Rwlock,
    Condvar,
    Thread,
    Atomic,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct SyncSummary {
    pub places: usize,
    pub transitions: usize,
    pub kind: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct SyncOp {
    pub patterns: Vec<String>,
    pub effect: SyncEffect,
    #[serde(default)]
    pub resource: Option<SyncResource>,
    #[serde(default)]
    pub summary: Option<SyncSummary>,
}

impl SyncOp {
    pub fn matches(&self, path: &str) -> bool {
        self.patterns
            .iter()
            .any(|pattern| path_matches(pattern, path))
    }
}

#[derive(Clone, Debug, Default)]
pub struct SyncRegistry {
    ops: Vec<SyncOp>,
    /// `true` when callers must use the legacy regex lists.
    regex_fallback: bool,
}

impl SyncRegistry {
    pub fn from_config(sync: &SyncConfig) -> Self {
        let ops = sync.effective_ops();
        Self {
            regex_fallback: ops.is_empty(),
            ops,
        }
    }

    pub fn uses_table(&self) -> bool {
        !self.regex_fallback
    }

    pub fn lookup<'a>(&'a self, path: &str) -> Option<&'a SyncOp> {
        if self.regex_fallback {
            return None;
        }
        self.ops.iter().find(|op| op.matches(path))
    }
}

/// `pattern` matches `path` when the pattern's path segments appear in order
/// and the final segment (the method) is equal. A `{impl#N}` segment stands
/// in for the pattern's type name, so `core::sync::atomic::{impl#5}::load`
/// matches `AtomicPtr::load`. Monomorphized paths such as `Mutex::<i32>::lock`
/// still match. A substring is not enough to skip translation.
pub fn path_matches(pattern: &str, path: &str) -> bool {
    if pattern_is_regex(pattern) {
        return regex::Regex::new(pattern)
            .map(|re| re.is_match(path))
            .unwrap_or(false);
    }
    let pattern_segs = segments(pattern);
    let path_segs = segments(path);
    if pattern_segs.is_empty() || path_segs.is_empty() {
        return false;
    }
    if pattern_segs.last() != path_segs.last() {
        return false;
    }
    if pattern_segs.len() == 1 {
        return true;
    }
    let type_name = pattern_segs[pattern_segs.len() - 2];
    let type_at = path_segs[..path_segs.len() - 1]
        .iter()
        .rposition(|seg| *seg == type_name || seg.ends_with(type_name) || is_impl_segment(seg));
    let Some(type_at) = type_at else {
        return false;
    };
    let prefix = &pattern_segs[..pattern_segs.len() - 2];
    let mut next = 0;
    for seg in &path_segs[..type_at] {
        if next < prefix.len() && (*seg == prefix[next] || seg.contains(prefix[next])) {
            next += 1;
        }
    }
    next == prefix.len()
}

fn is_impl_segment(seg: &str) -> bool {
    let Some(rest) = seg.strip_prefix("{impl#") else {
        return false;
    };
    let Some(rest) = rest.strip_suffix('}') else {
        return false;
    };
    !rest.is_empty() && rest.bytes().all(|byte| byte.is_ascii_digit())
}

fn pattern_is_regex(pattern: &str) -> bool {
    pattern.chars().any(|ch| ".*[]()|+?\\".contains(ch))
}

fn segments(path: &str) -> Vec<&str> {
    path.split("::")
        .map(|part| part.split('<').next().unwrap_or(part).trim())
        .filter(|part| !part.is_empty())
        .collect()
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SyncConfig {
    /// Explicit operations. Omitted in TOML, this field is the built-in table.
    /// An empty list recognizes nothing.
    #[serde(default = "builtin_sync_ops")]
    pub op: Vec<SyncOp>,
}

impl Default for SyncConfig {
    fn default() -> Self {
        Self {
            op: builtin_sync_ops(),
        }
    }
}

impl SyncConfig {
    pub fn effective_ops(&self) -> Vec<SyncOp> {
        self.op.clone()
    }
}

fn op(patterns: &[&str], effect: SyncEffect, resource: SyncResource) -> SyncOp {
    SyncOp {
        patterns: patterns.iter().map(|s| (*s).to_string()).collect(),
        effect,
        resource: Some(resource),
        summary: None,
    }
}

fn summary_op(patterns: &[&str], kind: &str) -> SyncOp {
    SyncOp {
        patterns: patterns.iter().map(|s| (*s).to_string()).collect(),
        effect: SyncEffect::Summary,
        resource: None,
        summary: Some(SyncSummary {
            places: 1,
            transitions: 1,
            kind: kind.to_string(),
        }),
    }
}

pub fn builtin_sync_ops() -> Vec<SyncOp> {
    use SyncEffect::*;
    use SyncResource::*;
    vec![
        op(
            &[
                "std::sync::Mutex::lock",
                "std::sync::Mutex::try_lock",
                r"std::sync::poison::mutex.*::lock$",
                r"std::sync::poison::mutex.*::try_lock$",
            ],
            Acquire,
            Mutex,
        ),
        op(
            &["parking_lot::Mutex::lock", "parking_lot::Mutex::try_lock"],
            Acquire,
            Mutex,
        ),
        op(
            &["spin::Mutex::lock", "spin::Mutex::try_lock"],
            Acquire,
            Mutex,
        ),
        op(
            &["lock_api::Mutex::lock", "lock_api::Mutex::try_lock"],
            Acquire,
            Mutex,
        ),
        op(
            &[
                "std::sync::RwLock::read",
                "std::sync::RwLock::write",
                "std::sync::RwLock::try_read",
                "std::sync::RwLock::try_write",
                r"std::sync::poison::rwlock.*::read$",
                r"std::sync::poison::rwlock.*::write$",
                r"std::sync::poison::rwlock.*::try_read$",
                r"std::sync::poison::rwlock.*::try_write$",
            ],
            Acquire,
            Rwlock,
        ),
        op(
            &[
                "parking_lot::RwLock::read",
                "parking_lot::RwLock::write",
                "spin::RwLock::read",
                "spin::RwLock::write",
            ],
            Acquire,
            Rwlock,
        ),
        op(
            &[
                "std::sync::Condvar::wait",
                "std::sync::Condvar::wait_while",
                "std::sync::Condvar::wait_timeout",
                "std::sync::Condvar::wait_timeout_while",
                r"std::sync::poison::condvar.*::wait",
            ],
            Wait,
            Condvar,
        ),
        op(
            &[
                "parking_lot::Condvar::wait",
                "parking_lot::Condvar::wait_while",
            ],
            Wait,
            Condvar,
        ),
        op(
            &[
                "std::sync::Condvar::notify_one",
                "std::sync::Condvar::notify_all",
                r"std::sync::poison::condvar.*::notify_one$",
                r"std::sync::poison::condvar.*::notify_all$",
            ],
            Notify,
            Condvar,
        ),
        op(
            &[
                "parking_lot::Condvar::notify_one",
                "parking_lot::Condvar::notify_all",
            ],
            Notify,
            Condvar,
        ),
        op(
            &[
                "std::thread::spawn",
                "std::thread::Builder::spawn",
                "std::thread::scope",
                "rayon::spawn",
                "tokio::spawn",
                "tokio::task::spawn",
                "async_std::task::spawn",
            ],
            Spawn,
            Thread,
        ),
        op(
            &[
                "std::thread::Scope::spawn",
                "crossbeam::thread::Scope::spawn",
                "rayon::Scope::spawn",
            ],
            Spawn,
            Thread,
        ),
        op(
            &[
                "std::thread::JoinHandle::join",
                "std::thread::JoinHandle::try_join",
                r"std::thread::join_handle.*::join$",
                r"std::thread::join_handle.*::try_join$",
                "tokio::task::JoinHandle::poll",
                "async_std::task::JoinHandle::poll",
            ],
            Join,
            Thread,
        ),
        op(
            &[
                "std::thread::Scope::join",
                "crossbeam::thread::Scope::join",
                "rayon::Scope::join",
                "rayon::join",
                "rayon_core::join",
            ],
            Join,
            Thread,
        ),
        op(
            &[
                "std::sync::atomic::AtomicBool::load",
                "std::sync::atomic::AtomicUsize::load",
                "std::sync::atomic::AtomicU8::load",
                "std::sync::atomic::AtomicU32::load",
                "std::sync::atomic::AtomicU64::load",
                "std::sync::atomic::AtomicI64::load",
                "std::sync::atomic::AtomicPtr::load",
                "core::sync::atomic::AtomicBool::load",
                "core::sync::atomic::AtomicUsize::load",
                "core::sync::atomic::AtomicU8::load",
                "core::sync::atomic::AtomicI64::load",
                "core::sync::atomic::AtomicPtr::load",
            ],
            Acquire,
            Atomic,
        ),
        op(
            &[
                "std::sync::atomic::AtomicBool::store",
                "std::sync::atomic::AtomicUsize::store",
                "std::sync::atomic::AtomicU8::store",
                "std::sync::atomic::AtomicI64::store",
                "std::sync::atomic::AtomicPtr::store",
                "core::sync::atomic::AtomicBool::store",
                "core::sync::atomic::AtomicUsize::store",
                "core::sync::atomic::AtomicU8::store",
                "core::sync::atomic::AtomicI64::store",
                "core::sync::atomic::AtomicPtr::store",
            ],
            Release,
            Atomic,
        ),
        op(
            &[
                "std::sync::atomic::AtomicUsize::compare_exchange",
                "std::sync::atomic::AtomicUsize::compare_exchange_weak",
                "std::sync::atomic::AtomicUsize::swap",
                "std::sync::atomic::AtomicUsize::fetch_add",
                "std::sync::atomic::AtomicI64::compare_exchange",
                "std::sync::atomic::AtomicI64::compare_exchange_weak",
                "std::sync::atomic::AtomicI64::swap",
                "std::sync::atomic::AtomicI64::fetch_add",
                "std::sync::atomic::AtomicBool::compare_exchange",
                "std::sync::atomic::AtomicBool::compare_exchange_weak",
                "std::sync::atomic::AtomicBool::swap",
                "core::sync::atomic::AtomicUsize::compare_exchange",
                "core::sync::atomic::AtomicUsize::compare_exchange_weak",
                "core::sync::atomic::AtomicUsize::fetch_add",
                "core::sync::atomic::AtomicI64::compare_exchange",
                "core::sync::atomic::AtomicI64::compare_exchange_weak",
                "core::sync::atomic::AtomicI64::swap",
                "core::sync::atomic::AtomicI64::fetch_add",
                "core::sync::atomic::AtomicBool::compare_exchange",
                "core::sync::atomic::AtomicBool::compare_exchange_weak",
                "core::sync::atomic::AtomicPtr::compare_exchange",
                "core::sync::atomic::AtomicPtr::swap",
            ],
            Acquire,
            Atomic,
        ),
        // ConcIR skeleton sync helpers: summarized as atomic sync transitions
        // rather than descending into internal Mutex/Condvar implementation details.
        summary_op(
            &[
                "cir_trace::Semaphore::acquire",
                "cir_trace::Semaphore::acquire_sid",
                "CountingSemaphore::acquire",
            ],
            "sem_acquire",
        ),
        summary_op(
            &[
                "cir_trace::Semaphore::release",
                "cir_trace::Semaphore::release_sid",
                "CountingSemaphore::release",
            ],
            "sem_release",
        ),
        summary_op(
            &[
                "cir_trace::Channel::send",
                "cir_trace::Channel::send_sid",
                "MpscChannel::send",
                "std::sync::mpsc::Sender::send",
                "std::sync::mpsc::SyncSender::send",
            ],
            "channel_send",
        ),
        summary_op(
            &[
                "cir_trace::Channel::recv",
                "cir_trace::Channel::recv_sid",
                "MpscChannel::recv",
                "std::sync::mpsc::Receiver::recv",
            ],
            "channel_recv",
        ),
        // ConcIR silent runtime / data helpers: non-sync operations skipped
        // without descending into internal UnsafeCell or trace buffer code.
        summary_op(
            &[
                "cir_trace::record",
                "cir_trace::ev",
                "cir_trace::finish",
                "cir_trace::scope",
                "cir_trace::tag_str",
                "cir_trace::set_tag",
                "cir_trace::SyncVar::new",
                "cir_trace::SyncVar::read",
                "cir_trace::SyncVar::write",
                "cir_trace::Semaphore::new",
                "cir_trace::Channel::new",
                "MpscChannel::new",
                "CountingSemaphore::new",
            ],
            "silent",
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_lookup_matches_monomorphized_paths() {
        let reg = SyncRegistry::from_config(&SyncConfig::default());
        let lock = reg
            .lookup("std::sync::mutex::Mutex::<i32>::lock")
            .expect("std mutex lock");
        assert_eq!(lock.effect, SyncEffect::Acquire);
        assert_eq!(lock.resource, Some(SyncResource::Mutex));

        let weak = reg
            .lookup("core::sync::atomic::AtomicUsize::compare_exchange_weak")
            .expect("weak cas");
        assert_eq!(weak.resource, Some(SyncResource::Atomic));

        let spawn = reg.lookup("std::thread::spawn").expect("spawn");
        assert_eq!(spawn.effect, SyncEffect::Spawn);
        assert_eq!(spawn.resource, Some(SyncResource::Thread));

        assert!(reg.lookup("std::vec::Vec::<u8>::push").is_none());
        let wait = reg
            .lookup("std::sync::poison::condvar::{impl#0}::wait")
            .expect("poison condvar wait");
        assert_eq!(wait.effect, SyncEffect::Wait);
        let join = reg
            .lookup("std::thread::join_handle::{impl#2}::join")
            .expect("join handle");
        assert_eq!(join.effect, SyncEffect::Join);

        let load = reg
            .lookup("core::sync::atomic::{impl#5}::load")
            .expect("impl load");
        assert_eq!(load.effect, SyncEffect::Acquire);
        assert_eq!(load.resource, Some(SyncResource::Atomic));
        let store = reg
            .lookup("core::sync::atomic::{impl#5}::store")
            .expect("impl store");
        assert_eq!(store.effect, SyncEffect::Release);
        assert_eq!(store.resource, Some(SyncResource::Atomic));
        let swap = reg
            .lookup("core::sync::atomic::{impl#5}::swap")
            .expect("impl swap");
        assert_eq!(swap.resource, Some(SyncResource::Atomic));

        let empty = SyncRegistry::from_config(&SyncConfig { op: Vec::new() });
        assert!(!empty.uses_table());
        assert!(empty.lookup("std::sync::Mutex::lock").is_none());
    }

    #[test]
    fn registry_recognizes_concir_skeleton_helpers() {
        let reg = SyncRegistry::from_config(&SyncConfig::default());

        let sem_acq = reg
            .lookup("cir_generated::cir_trace::{impl#0}::acquire_sid")
            .expect("Semaphore::acquire_sid");
        assert_eq!(sem_acq.effect, SyncEffect::Summary);
        assert_eq!(
            sem_acq.summary.as_ref().map(|s| s.kind.as_str()),
            Some("sem_acquire")
        );

        let sem_rel = reg
            .lookup("cir_generated::cir_trace::Semaphore::release")
            .expect("Semaphore::release");
        assert_eq!(sem_rel.effect, SyncEffect::Summary);
        assert_eq!(
            sem_rel.summary.as_ref().map(|s| s.kind.as_str()),
            Some("sem_release")
        );

        let ch_send = reg
            .lookup("cir_generated::cir_trace::Channel::<i64>::send_sid")
            .expect("Channel::send_sid");
        assert_eq!(ch_send.effect, SyncEffect::Summary);
        assert_eq!(
            ch_send.summary.as_ref().map(|s| s.kind.as_str()),
            Some("channel_send")
        );

        let ch_recv = reg
            .lookup("cir_generated::cir_trace::{impl#1}::recv")
            .expect("Channel::recv");
        assert_eq!(ch_recv.effect, SyncEffect::Summary);
        assert_eq!(
            ch_recv.summary.as_ref().map(|s| s.kind.as_str()),
            Some("channel_recv")
        );

        for silent_path in [
            "cir_generated::cir_trace::record",
            "cir_generated::cir_trace::finish",
            "cir_generated::cir_trace::SyncVar::<i64>::read",
            "cir_generated::cir_trace::{impl#2}::write",
        ] {
            let op = reg.lookup(silent_path).expect(silent_path);
            assert_eq!(op.effect, SyncEffect::Summary);
            assert_eq!(op.summary.as_ref().map(|s| s.kind.as_str()), Some("silent"));
        }

        let i64_load = reg
            .lookup("core::sync::atomic::AtomicI64::load")
            .expect("AtomicI64::load");
        assert_eq!(i64_load.resource, Some(SyncResource::Atomic));

        let mpsc_send = reg
            .lookup("cir_generated::MpscChannel::<i64>::send")
            .expect("MpscChannel::send");
        assert_eq!(mpsc_send.effect, SyncEffect::Summary);
        assert_eq!(
            mpsc_send.summary.as_ref().map(|s| s.kind.as_str()),
            Some("channel_send")
        );

        let mpsc_recv = reg
            .lookup("cir_generated::MpscChannel::<i64>::recv")
            .expect("MpscChannel::recv");
        assert_eq!(mpsc_recv.effect, SyncEffect::Summary);
        assert_eq!(
            mpsc_recv.summary.as_ref().map(|s| s.kind.as_str()),
            Some("channel_recv")
        );

        let cs_acq = reg
            .lookup("cir_generated::CountingSemaphore::acquire")
            .expect("CountingSemaphore::acquire");
        assert_eq!(
            cs_acq.summary.as_ref().map(|s| s.kind.as_str()),
            Some("sem_acquire")
        );
    }
}
