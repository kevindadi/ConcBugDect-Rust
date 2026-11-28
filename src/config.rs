use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;

use crate::analysis::primitives::sync_registry::SyncConfig;

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
    /// What a cut back edge means.
    ///
    /// - `cut` (main-mode default): the edge is dropped; the loop body runs at
    ///   most once and the cut target may become a structural sink.
    /// - `summary`: the edge is dropped *and* a loop-summary transition
    ///   re-enters the target `loop_summary_k` times (bounded unroll, default
    ///   k=1), so a back-edge target is no longer a dead control sink.
    ///
    /// `None` keeps the per-entry-mode default: `cut` for a binary crate,
    /// `summary` for a library crate (`EntryMode::LibraryRoots`), where the
    /// loop-sink false candidates were the dominant false-positive source.
    /// An explicit value in `spn.toml` (or `--loop-semantics`) always wins.
    #[serde(default)]
    pub loop_semantics: Option<LoopSemantics>,
    /// How many times a loop-summary transition may re-enter its cut back-edge
    /// target. Implemented as the number of tokens on the summary's
    /// budget place, so the loop body runs at most `1 + k` times (`k = 0`
    /// leaves the summary disabled and is equivalent to `cut` plus the
    /// terminal fallback). Only meaningful under `loop_semantics = summary`;
    /// the default `1` is that one-step unroll.
    #[serde(default = "default_loop_summary_k")]
    pub loop_summary_k: usize,
    /// Enable partial-order reduction (POR) to skip redundant interleavings of independent transitions.
    #[serde(default)]
    pub por_enabled: bool,
    /// Also translate functions that use locks / atomics / semaphores / condition variables and their callees (fewer missed interleavings).
    #[serde(default = "default_true")]
    pub translate_concurrent_roots: bool,
    /// Encode `Mutex<bool>` condvar loop guards (`while !*g { g = cv.wait(g); }`
    /// paired with `*g = true`) as two complementary capacity-1 places
    /// `data.<var>.false` (initial 1) and `data.<var>.true` (initial 0).
    #[serde(default = "default_true")]
    pub bool_guard_abstraction: bool,
    /// Lock-object type patterns for *guard-less custom locks*
    /// (parking_lot's `RawMutex`/`RawRwLock`, `parking_lot_core::WordLock`,
    /// and user types listed here). A function is treated as a custom lock
    /// operation when its def path, its trait path, or its signature contains
    /// one of these substrings and its method name is a known lock/unlock
    /// name. Only methods defined in the analysed crate (local instances) are
    /// modelled, so this list never changes how std / parking_lot *users*
    /// are translated.
    #[serde(default = "default_custom_lock_types")]
    pub custom_lock_types: Vec<String>,
    /// Unknown-alias policy: conservative (sound) treats Unknown as Possibly; optimistic treats Unknown as Unlikely.
    #[serde(default = "default_alias_unknown_policy")]
    pub alias_unknown_policy: AliasUnknownPolicy,
    /// Call-site sensitivity depth (k-CFA) for the pointer-analysis engine.
    /// `0` = context-insensitive; `1` (default) keeps the last call site.
    #[serde(default = "default_pta_k")]
    pub pta_k: usize,
    /// Maximum number of library roots that may *start* in one
    /// slice. Shared-resource grouping can merge dozens of roots into one
    /// product state space that truncates before any root reaches a wait;
    /// oversized groups are split into slices of at most this many roots while
    /// keeping every directly synchronizing root pair together in at least one
    /// slice. `None` disables the split (the previous grouping).
    #[serde(default = "default_slice_max_roots")]
    pub slice_max_roots: Option<usize>,
    /// Total state budget across all library slices. `None` lets
    /// every slice use the full `state_limit` (the previous behaviour,
    /// so a run can hold `slice_count * state_limit` states); a value bounds
    /// the merged graph to that many states, exploring slices in partition
    /// order until the budget is spent. Slices after the budget are reported
    /// as unexplored rather than silently dropped.
    #[serde(default)]
    pub slice_state_budget: Option<usize>,
    #[serde(default)]
    pub report_level: ReportLevel,
    /// Which condition-variable library the *scenario* analysis
    /// models. `std` is the historical behaviour (`std::sync::Condvar` and
    /// `#[pn_condvar]` only); `parking_lot` additionally recognises
    /// `parking_lot::Condvar`; `all` enables both. The field is serde- and
    /// CLI-settable but absent from the shipped `spn.toml`, so the default
    /// path is byte-identical to the previous nets.
    #[serde(default)]
    pub condvar_model: CondvarModel,
    /// Synchronization effects. Names in this table identify operations.
    /// They do not drop functions from translation. The built-in table is the
    /// only path; an empty `op` list recognizes nothing.
    #[serde(default)]
    pub sync: SyncConfig,
    /// `alias` (default) is one place per atomic equivalence class.
    /// `legacy` is the previous order-dependent place sharing.
    /// Verified: `legacy` and `alias` differ on 3 crates
    /// (`left_right_client`, `parking_lot_client`, `scc_client`).
    /// The six JSON files are identical on the 28 bench crates and the other
    /// 5 real crates, and the deadlock candidate counts are unchanged.
    /// On left-right, `legacy` has 5 more atomic events; on scc, 60 fewer;
    /// on parking_lot, 8 events change only the `AliasId` local.
    #[serde(default = "default_legacy_switch")]
    pub resource_atomic_partition: PartitionSwitch,
    /// `original` (default) is the lock union-find that built r34-golden.
    /// `ported` matches `original` on all 28 bench crates and 8 real crates.
    /// `typed` is the experimental type filter and stays off by default:
    /// on flume it moves the candidate count from 5 to 7.
    #[serde(default = "default_lock_grouper")]
    pub resource_lock_grouper: LockGrouper,
}

/// Experiment switch for atomic grouping. Default keeps the alias partition.
/// Unsafe grouping has no switch: legacy matched alias on every measured crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize, Default)]
#[serde(rename_all = "lowercase")]
pub enum PartitionSwitch {
    #[default]
    Alias,
    Legacy,
}

impl PartitionSwitch {
    pub fn parse(text: &str) -> Option<Self> {
        match text {
            "alias" => Some(Self::Alias),
            "legacy" => Some(Self::Legacy),
            _ => None,
        }
    }
}

/// Which lock union-find builds the mutex/rwlock places.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize, Default)]
#[serde(rename_all = "lowercase")]
pub enum LockGrouper {
    #[default]
    Original,
    Ported,
    Typed,
}

impl LockGrouper {
    pub fn parse(text: &str) -> Option<Self> {
        match text {
            "original" => Some(Self::Original),
            "ported" => Some(Self::Ported),
            "typed" => Some(Self::Typed),
            _ => None,
        }
    }
}

fn default_legacy_switch() -> PartitionSwitch {
    PartitionSwitch::Alias
}

fn default_lock_grouper() -> LockGrouper {
    LockGrouper::Original
}

/// Scenario-level condition-variable model switch.
///
/// The three values select the *recognised families*, not one library on top
/// of another:
///
/// - `std` (default): `std::sync::Condvar` / `#[pn_condvar]`, exactly the
///   previous behaviour.
/// - `parking_lot`: `parking_lot::Condvar` (with its `&mut MutexGuard`
///   argument shape) instead of the std family.
/// - `all`: both families.
///
/// Opening the switch (any value other than `std`) also enables the waiter
/// counter ordering guard (task B): `wait` produces a waiting token
/// at its entry transition, the notify *normal* branch requires and consumes
/// one, and the lost twin stays unconditional. `std` keeps the legacy
/// single-slot mailbox with its initial token, which is why the teaching bench
/// is byte-identical by default.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum CondvarModel {
    #[default]
    Std,
    ParkingLot,
    All,
}

/// The waiter-counter ordering guard, as arc weights.
///
/// The translator reads every guard number from this plan, so the unit test
/// that pins "notify before wait can only take the lost branch" and the
/// emitted arcs are driven by the same values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CondvarGuardPlan {
    /// Initial tokens on the condvar mailbox place (capacity 1). The legacy
    /// model starts at 1 (the first wait may return without a notify); the
    /// guard removes that permission.
    pub initial_mailbox_tokens: usize,
    /// Weight a `wait` entry (`bb_end`) produces on the waiting counter.
    pub wait_entry_waiting_weight: usize,
    /// Weight the notify *normal* branch consumes from the waiting counter.
    pub notify_normal_waiting_weight: usize,
}

impl CondvarModel {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Std => "std",
            Self::ParkingLot => "parking_lot",
            Self::All => "all",
        }
    }

    /// Whether `std::sync::Condvar` (and the configured std API patterns) is
    /// part of the modelled families.
    pub fn recognizes_std(self) -> bool {
        matches!(self, Self::Std | Self::All)
    }

    /// Whether `parking_lot::Condvar` is part of the modelled families.
    pub fn recognizes_parking_lot(self) -> bool {
        matches!(self, Self::ParkingLot | Self::All)
    }

    /// The ordering guard is a scenario-level semantic change: it only turns
    /// on when the switch is opened, so the default `std` path stays
    /// byte-identical.
    pub fn ordering_guard(self) -> bool {
        !matches!(self, Self::Std)
    }

    pub fn guard_plan(self) -> CondvarGuardPlan {
        if self.ordering_guard() {
            CondvarGuardPlan {
                initial_mailbox_tokens: 0,
                wait_entry_waiting_weight: 1,
                notify_normal_waiting_weight: 1,
            }
        } else {
            CondvarGuardPlan {
                initial_mailbox_tokens: 1,
                wait_entry_waiting_weight: 0,
                notify_normal_waiting_weight: 0,
            }
        }
    }
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

/// Loop semantics of a cut CFG back edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum LoopSemantics {
    /// Existing behaviour: the back edge is simply dropped.
    Cut,
    /// Drop the back edge and add a loop-summary transition from the
    /// edge's source to its target (bounded unroll `loop_summary_k`, default 1).
    Summary,
}

impl Default for LoopSemantics {
    fn default() -> Self {
        Self::Cut
    }
}

impl LoopSemantics {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Cut => "cut",
            Self::Summary => "summary",
        }
    }
}

impl Default for PnConfig {
    fn default() -> Self {
        Self {
            state_limit: default_state_limit(),
            entry_reachable: true,
            reduce_net: default_reduce_net(),
            break_cfg_cycles: default_true(),
            loop_semantics: None,
            loop_summary_k: default_loop_summary_k(),
            por_enabled: false,
            translate_concurrent_roots: default_true(),
            bool_guard_abstraction: default_true(),
            custom_lock_types: default_custom_lock_types(),
            alias_unknown_policy: default_alias_unknown_policy(),
            pta_k: default_pta_k(),
            slice_max_roots: default_slice_max_roots(),
            slice_state_budget: None,
            report_level: ReportLevel::Developer,
            condvar_model: CondvarModel::Std,
            sync: SyncConfig::default(),
            resource_atomic_partition: default_legacy_switch(),
            resource_lock_grouper: default_lock_grouper(),
        }
    }
}

fn default_alias_unknown_policy() -> AliasUnknownPolicy {
    AliasUnknownPolicy::Conservative
}

fn default_pta_k() -> usize {
    1
}

/// Keep at most four roots per slice. Small enough that a slice's
/// product state space is explorable, large enough that a synchronizing pair
/// (or a short wait-for chain) still starts together.
fn default_slice_max_roots() -> Option<usize> {
    Some(4)
}

/// One re-entry (that one-step unroll) unless configured.
fn default_loop_summary_k() -> usize {
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

/// Guard-less custom locks. Matched against a function's def path,
/// trait path, and signature: parking_lot's `RawMutex` / `RawRwLock` and
/// parking_lot_core's `WordLock` are the shipped defaults; a user type is
/// added by listing its name here.
fn default_custom_lock_types() -> Vec<String> {
    vec![
        "RawMutex".to_string(),
        "RawRwLock".to_string(),
        "WordLock".to_string(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shipped_pn_toml_leaves_loop_semantics_unset() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/spn.toml");
        let loaded = PnConfig::load_from_file(path).expect("spn.toml must parse");
        assert_eq!(loaded.loop_semantics, None);
    }

    #[test]
    fn custom_lock_types_are_configurable() {
        // Shipped config inherits the defaults: the list is additive and its
        // absence in `spn.toml` must not disable the recognition.
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/spn.toml");
        let loaded = PnConfig::load_from_file(path).expect("spn.toml must parse");
        assert_eq!(
            loaded.custom_lock_types,
            vec![
                "RawMutex".to_string(),
                "RawRwLock".to_string(),
                "WordLock".to_string()
            ]
        );
        // A fixture-local `spn.toml` may add a user type...
        let parsed: PnConfig = toml::from_str("custom_lock_types = [\"MyMutex\"]").unwrap();
        assert_eq!(parsed.custom_lock_types, vec!["MyMutex".to_string()]);
        // ...and an empty list turns the recognition off.
        let parsed: PnConfig = toml::from_str("custom_lock_types = []").unwrap();
        assert!(parsed.custom_lock_types.is_empty());
    }

    #[test]
    fn loop_summary_k_defaults_to_one_and_is_configurable() {
        // Absent from `spn.toml` and from the built-in defaults: one re-entry
        // (the cut semantics).
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/spn.toml");
        let loaded = PnConfig::load_from_file(path).expect("spn.toml must parse");
        assert_eq!(loaded.loop_summary_k, 1);
        assert_eq!(PnConfig::default().loop_summary_k, 1);
        // A fixture-local config can widen the unroll budget.
        let parsed: PnConfig = toml::from_str("loop_summary_k = 2").unwrap();
        assert_eq!(parsed.loop_summary_k, 2);
        assert_eq!(parsed.loop_semantics, None);
        // The two knobs combine as documented.
        let parsed: PnConfig =
            toml::from_str("loop_semantics = \"summary\"\nloop_summary_k = 3").unwrap();
        assert_eq!(parsed.loop_semantics, Some(LoopSemantics::Summary));
        assert_eq!(parsed.loop_summary_k, 3);
    }

    #[test]
    fn loop_semantics_is_config_file_loadable() {
        let parsed: PnConfig = toml::from_str("loop_semantics = \"summary\"").unwrap();
        assert_eq!(parsed.loop_semantics, Some(LoopSemantics::Summary));
        let parsed: PnConfig = toml::from_str("loop_semantics = \"cut\"").unwrap();
        assert_eq!(parsed.loop_semantics, Some(LoopSemantics::Cut));
        // The serialized spelling is the documented "cut" / "summary".
        let rendered = toml::to_string(&PnConfig {
            loop_semantics: Some(LoopSemantics::Summary),
            ..PnConfig::default()
        })
        .unwrap();
        assert!(rendered.contains("loop_semantics = \"summary\""));
    }

    // condvar model switch and waiter-counter guard ────────────

    /// A tiny marking model of the condvar protocol, driven by the same
    /// `CondvarGuardPlan` numbers the translator uses. The mailbox keeps the
    /// existing capacity-1 semantics (a produced token on a full mailbox is
    /// lost — the notify-clamp conservatism).
    #[derive(Clone, Copy, Debug)]
    struct GuardMarking {
        mailbox: usize,
        waiting: usize,
    }

    impl GuardMarking {
        const MAILBOX_CAPACITY: usize = 1;

        fn initial(plan: CondvarGuardPlan) -> Self {
            Self {
                mailbox: plan.initial_mailbox_tokens,
                waiting: 0,
            }
        }

        /// `wait` entry (`bb_end`).
        fn wait_entry(&mut self, plan: CondvarGuardPlan) {
            self.waiting += plan.wait_entry_waiting_weight;
        }

        /// The normal notify branch consumes its waiting weight and produces
        /// the wakeup permission (clamped at the mailbox capacity).
        fn can_notify_normal(&self, plan: CondvarGuardPlan) -> bool {
            self.waiting >= plan.notify_normal_waiting_weight
        }

        fn notify_normal(&mut self, plan: CondvarGuardPlan) {
            assert!(self.can_notify_normal(plan));
            self.waiting -= plan.notify_normal_waiting_weight;
            self.mailbox = (self.mailbox + 1).min(Self::MAILBOX_CAPACITY);
        }

        /// The H1 lost twin is unconditional (kept for deadlock recall).
        fn can_notify_lost(&self) -> bool {
            true
        }

        fn notify_lost(&mut self) {}

        /// `wait` return (`bb_ret`) consumes one wakeup permission.
        fn can_wait_return(&self) -> bool {
            self.mailbox > 0
        }

        fn wait_return(&mut self) {
            assert!(self.can_wait_return());
            self.mailbox -= 1;
        }
    }

    /// Task B pin, written before the translator wiring: when the
    /// switch is open, `notify` *before* any `wait` cannot take the normal
    /// branch — only the unconditional lost twin remains — so the wakeup is
    /// genuinely lost and a later wait parks forever.
    #[test]
    fn notify_before_wait_can_only_take_the_lost_branch() {
        let plan = CondvarModel::ParkingLot.guard_plan();
        let mut marking = GuardMarking::initial(plan);

        // No waiter yet: the normal branch is disabled, the lost twin is not.
        assert!(!marking.can_notify_normal(plan));
        assert!(marking.can_notify_lost());

        // The only legal notify-before-wait trace drops the wakeup.
        marking.notify_lost();

        // The consumer then parks; nothing can release it.
        marking.wait_entry(plan);
        assert!(!marking.can_wait_return());

        // Only a *later* notify, with a waiter present, can still deliver.
        assert!(marking.can_notify_normal(plan));
        marking.notify_normal(plan);
        assert!(marking.can_wait_return());
        marking.wait_return();
        assert_eq!(marking.mailbox, 0);
        // The waiter's token was consumed by the delivery: a second notify
        // with no parked waiter is lost again.
        assert!(!marking.can_notify_normal(plan));
    }

    /// The wait-then-notify order still delivers exactly one wakeup.
    #[test]
    fn wait_before_notify_takes_the_normal_branch() {
        let plan = CondvarModel::ParkingLot.guard_plan();
        let mut marking = GuardMarking::initial(plan);
        marking.wait_entry(plan);
        assert!(marking.can_notify_normal(plan));
        marking.notify_normal(plan);
        assert!(marking.can_wait_return());
    }

    /// Default `std` keeps the legacy single-slot mailbox: an initial token,
    /// no waiting-counter arcs, so the teaching bench nets cannot move.
    #[test]
    fn std_model_keeps_the_legacy_mailbox() {
        let plan = CondvarModel::Std.guard_plan();
        assert_eq!(plan.initial_mailbox_tokens, 1);
        assert_eq!(plan.wait_entry_waiting_weight, 0);
        assert_eq!(plan.notify_normal_waiting_weight, 0);
        assert!(!CondvarModel::Std.ordering_guard());

        let mut marking = GuardMarking::initial(plan);
        // The legacy model lets the first wait return without any notify.
        marking.wait_entry(plan);
        assert!(marking.can_wait_return());
    }

    #[test]
    fn condvar_model_defaults_to_std_and_is_configurable() {
        assert_eq!(CondvarModel::default(), CondvarModel::Std);
        assert_eq!(PnConfig::default().condvar_model, CondvarModel::Std);
        // The shipped spn.toml does not set it, so loading it keeps `std`.
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/spn.toml");
        let loaded = PnConfig::load_from_file(path).expect("spn.toml must parse");
        assert_eq!(loaded.condvar_model, CondvarModel::Std);
        // A scenario-local config can open the switch.
        let parsed: PnConfig = toml::from_str("condvar_model = \"parking_lot\"").unwrap();
        assert_eq!(parsed.condvar_model, CondvarModel::ParkingLot);
        let parsed: PnConfig = toml::from_str("condvar_model = \"all\"").unwrap();
        assert_eq!(parsed.condvar_model, CondvarModel::All);
        assert!(parsed.condvar_model.ordering_guard());
        assert_eq!(CondvarModel::All.as_str(), "all");
    }

    #[test]
    fn condvar_families_are_selected_by_the_model() {
        assert!(CondvarModel::Std.recognizes_std());
        assert!(!CondvarModel::Std.recognizes_parking_lot());
        assert!(!CondvarModel::ParkingLot.recognizes_std());
        assert!(CondvarModel::ParkingLot.recognizes_parking_lot());
        assert!(CondvarModel::All.recognizes_std());
        assert!(CondvarModel::All.recognizes_parking_lot());
    }

    #[test]
    fn bool_guard_abstraction_defaults_to_true_and_is_configurable() {
        assert!(PnConfig::default().bool_guard_abstraction);
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/spn.toml");
        let loaded = PnConfig::load_from_file(path).expect("spn.toml must parse");
        assert!(loaded.bool_guard_abstraction);

        let parsed: PnConfig = toml::from_str("bool_guard_abstraction = false").unwrap();
        assert!(!parsed.bool_guard_abstraction);
    }
}
