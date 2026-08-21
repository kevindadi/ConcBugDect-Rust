use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize, Default)]
#[serde(rename_all = "lowercase")]
pub enum ReportLevel {
    #[default]
    Developer,
    Research,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct PnConfig {
    /// State-space exploration cap. `None` means unbounded (risk of OOM on large crates).
    #[serde(default = "default_state_limit")]
    pub state_limit: Option<usize>,
    /// Translate only functions reachable from the entry point (entry-directed mode); shrinks nets on large crates.
    #[serde(default = "default_true")]
    pub entry_reachable: bool,
    /// Reduce the Petri net before state-graph construction.
    #[serde(default = "default_reduce_net")]
    pub reduce_net: bool,
    /// Break CFG back edges at MIR level (remove simple cycles).
    #[serde(default = "default_true")]
    pub break_cfg_cycles: bool,
    /// Enable partial-order reduction (POR) to skip redundant interleavings of independent transitions.
    #[serde(default)]
    pub por_enabled: bool,
    /// Also translate functions that use locks / atomics / semaphores / condition variables and their callees (fewer missed interleavings).
    #[serde(default = "default_true")]
    pub translate_concurrent_roots: bool,
    #[serde(default = "default_thread_spawn")]
    pub thread_spawn: Vec<String>,
    #[serde(default = "default_thread_join")]
    pub thread_join: Vec<String>,
    #[serde(default = "default_scope_spawn")]
    pub scope_spawn: Vec<String>,
    #[serde(default = "default_scope_join")]
    pub scope_join: Vec<String>,
    #[serde(default = "default_async_spawn")]
    pub async_spawn: Vec<String>,
    #[serde(default = "default_async_join")]
    pub async_join: Vec<String>,
    #[serde(default = "default_condvar_notify")]
    pub condvar_notify: Vec<String>,
    #[serde(default = "default_condvar_wait")]
    pub condvar_wait: Vec<String>,
    #[serde(default = "default_channel_send")]
    pub channel_send: Vec<String>,
    #[serde(default = "default_channel_recv")]
    pub channel_recv: Vec<String>,
    #[serde(default = "default_atomic_load")]
    pub atomic_load: Vec<String>,
    #[serde(default = "default_atomic_store")]
    pub atomic_store: Vec<String>,
    /// Unknown-alias policy: conservative (sound) treats Unknown as Possibly; optimistic treats Unknown as Unlikely.
    #[serde(default = "default_alias_unknown_policy")]
    pub alias_unknown_policy: AliasUnknownPolicy,
    /// Call-site sensitivity depth (k-CFA) for the pointer-analysis engine.
    /// `0` = context-insensitive; `1` (default) keeps the last call site.
    #[serde(default = "default_pta_k")]
    pub pta_k: usize,
    #[serde(default)]
    pub report_level: ReportLevel,
}

/// Policy for pointer-analysis results that are Unknown.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize, Default)]
#[serde(rename_all = "lowercase")]
pub enum AliasUnknownPolicy {
    /// Conservative (sound): Unknown ⇒ Possibly (add arcs); fewer false negatives, possibly more false positives.
    #[default]
    Conservative,
    /// Optimistic: Unknown ⇒ Unlikely (omit arcs); fewer false positives, possibly more false negatives.
    Optimistic,
}

impl Default for PnConfig {
    fn default() -> Self {
        Self {
            state_limit: default_state_limit(),
            entry_reachable: true,
            reduce_net: default_reduce_net(),
            break_cfg_cycles: default_true(),
            por_enabled: false,
            translate_concurrent_roots: default_true(),
            thread_spawn: default_thread_spawn(),
            thread_join: default_thread_join(),
            scope_spawn: default_scope_spawn(),
            scope_join: default_scope_join(),
            async_spawn: default_async_spawn(),
            async_join: default_async_join(),
            condvar_notify: default_condvar_notify(),
            condvar_wait: default_condvar_wait(),
            channel_send: default_channel_send(),
            channel_recv: default_channel_recv(),
            atomic_load: default_atomic_load(),
            atomic_store: default_atomic_store(),
            alias_unknown_policy: default_alias_unknown_policy(),
            pta_k: default_pta_k(),
            report_level: ReportLevel::Developer,
        }
    }
}

fn default_alias_unknown_policy() -> AliasUnknownPolicy {
    AliasUnknownPolicy::Conservative
}

fn default_pta_k() -> usize {
    1
}

impl PnConfig {
    pub fn load_from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let path = path.as_ref();
        if !path.exists() {
            return Ok(Self::default());
        }
        let content = fs::read_to_string(path)
            .with_context(|| format!("Failed to read config file: {:?}", path))?;
        let config: PnConfig = toml::from_str(&content)
            .with_context(|| format!("Failed to parse config file: {:?}", path))?;
        Ok(config)
    }
}

fn default_state_limit() -> Option<usize> {
    Some(50_000)
}

fn default_true() -> bool {
    true
}

fn default_reduce_net() -> bool {
    true
}

// Default values matching original hardcoded patterns
fn default_thread_spawn() -> Vec<String> {
    vec![
        r"std::thread[:a-zA-Z0-9_#\{\}]*::spawn".to_string(),
        r"rayon::spawn".to_string(),
    ]
}

fn default_thread_join() -> Vec<String> {
    vec![
        r"std::thread[:a-zA-Z0-9_#\{\}]*::join".to_string(),
        r"std::thread::JoinHandle::try_join".to_string(),
    ]
}

fn default_scope_spawn() -> Vec<String> {
    vec![
        r"std::thread::scoped[:a-zA-Z0-9_#\{\}]*::spawn".to_string(),
        r"std::thread::scope::Scope::spawn".to_string(),
        r"crossbeam::scope::Scope::spawn".to_string(),
        r"rayon::scope::Scope::spawn".to_string(),
    ]
}

fn default_scope_join() -> Vec<String> {
    vec![
        r"std::thread::scoped[:a-zA-Z0-9_#\{\}]*::join".to_string(),
        r"std::thread::scope::Scope::join".to_string(),
        r"crossbeam::scope::Scope::join".to_string(),
        r"rayon::scope::Scope::join".to_string(),
    ]
}

fn default_async_spawn() -> Vec<String> {
    vec![
        r"tokio[:a-zA-Z0-9_#\{\}]*::spawn".to_string(),
        r"async_std[:a-zA-Z0-9_#\{\}]*::spawn".to_string(),
        r"smol[:a-zA-Z0-9_#\{\}]*::spawn".to_string(),
    ]
}

fn default_async_join() -> Vec<String> {
    vec![
        // `.await` on a `JoinHandle` lowers to polling the handle future, so the
        // join site surfaces as the handle's `Future::poll` in MIR.
        r"tokio::task::JoinHandle[:a-zA-Z0-9_#\{\}]*::poll".to_string(),
        r"async_std::task::JoinHandle[:a-zA-Z0-9_#\{\}]*::poll".to_string(),
    ]
}

fn default_condvar_notify() -> Vec<String> {
    vec![
        // std::sync::Condvar::notify_one / notify_all (public API).
        // std delegates to the internal `poison::condvar::{impl}::notify_*` impl,
        // which is what actually shows up in MIR.
        r"std::sync::(?:Condvar|poison::condvar)[:a-zA-Z0-9_#\{\}]*::notify".to_string(),
    ]
}

fn default_condvar_wait() -> Vec<String> {
    vec![
        // std::sync::Condvar::wait / wait_while / wait_timeout* (public API).
        // std delegates to the internal `poison::condvar::{impl}::wait*` impl,
        // which is what actually shows up in MIR.
        r"std::sync::(?:Condvar|poison::condvar)[:a-zA-Z0-9_#\{\}]*::wait".to_string(),
    ]
}

fn default_channel_send() -> Vec<String> {
    vec![r"mpsc[:a-zA-Z0-9_#\{\}]*::send".to_string()]
}

fn default_channel_recv() -> Vec<String> {
    vec![r"mpsc[:a-zA-Z0-9_#\{\}]*::recv".to_string()]
}

fn default_atomic_load() -> Vec<String> {
    vec![r"atomic[:a-zA-Z0-9]*::load".to_string()]
}

fn default_atomic_store() -> Vec<String> {
    vec![r"atomic[:a-zA-Z0-9]*::store".to_string()]
}
