//! Synchronization API recognition.
//!
//! [`KeyApiRegex`] decides which calls are locks, condition variables, and
//! atomics. It does not build Petri-net places or transitions.

use crate::analysis::primitives::atomic::AtomicApi;
use crate::analysis::primitives::sync_registry::{SyncEffect, SyncRegistry, SyncResource};
use crate::config::PnConfig;

/// Token capacity of an `RwLock` resource place. A read lock consumes one
/// token (so up to `RWLOCK_CAPACITY` concurrent readers); a write lock is
/// exclusive and must consume *all* tokens.
pub const RWLOCK_CAPACITY: usize = 10;

pub struct KeyApiRegex {
    pub sync: SyncRegistry,
}

impl KeyApiRegex {
    pub fn new(config: &PnConfig) -> Self {
        Self {
            sync: SyncRegistry::from_config(&config.sync),
        }
    }

    fn table_op(&self, path: &str) -> Option<&crate::analysis::primitives::sync_registry::SyncOp> {
        self.sync.lookup(path)
    }

    pub fn matches_condvar_wait(&self, path: &str) -> bool {
        self.table_op(path).is_some_and(|op| {
            op.effect == SyncEffect::Wait && op.resource == Some(SyncResource::Condvar)
        })
    }

    pub fn matches_condvar_notify(&self, path: &str) -> bool {
        self.table_op(path).is_some_and(|op| {
            op.effect == SyncEffect::Notify && op.resource == Some(SyncResource::Condvar)
        })
    }

    /// Atomic API recognized for this call. The registry decides which
    /// functions are atomic; the method name selects load / store /
    /// read-modify-write. Other `Atomic*` methods in `core`/`std::sync::atomic`
    /// share that effect even when the table does not name the type.
    pub fn atomic_api(&self, path: &str) -> Option<AtomicApi> {
        if let Some(op) = self.table_op(path) {
            if op.resource != Some(SyncResource::Atomic) {
                return None;
            }
            return atomic_api_from_method(path);
        }
        if path.contains("::sync::atomic::") {
            return atomic_api_from_method(path);
        }
        None
    }
}

fn atomic_api_from_method(path: &str) -> Option<AtomicApi> {
    let last = path.rsplit("::").next().unwrap_or(path);
    let last = last.split('<').next().unwrap_or(last);
    match last {
        "load" => Some(AtomicApi::Read),
        "store" => Some(AtomicApi::Write),
        "compare_exchange"
        | "compare_exchange_weak"
        | "fetch_add"
        | "fetch_sub"
        | "fetch_and"
        | "fetch_or"
        | "fetch_xor"
        | "swap" => Some(AtomicApi::ReadWrite),
        _ => None,
    }
}
