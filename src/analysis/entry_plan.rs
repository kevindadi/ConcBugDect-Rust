//! Which functions are translated, which of them are entries, and the
//! reachable set. Place creation stays on `PetriNet`.

use std::collections::{BTreeMap, BTreeSet};

use petgraph::visit::IntoNodeReferences;
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use serde::{Deserialize, Serialize};

use crate::analysis::callgraph::{CallGraph, InstanceId};
use crate::options::Options;

/// Why a function instance was selected as a concurrent root.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum RootReason {
    #[serde(rename = "lockguard")]
    Lockguard,
    #[serde(rename = "condvar")]
    Condvar,
    #[serde(rename = "atomic")]
    Atomic,
    #[serde(rename = "custom_lock")]
    CustomLock,
}

/// Whether a local item is exported. Non-local defs are not exported by this crate.
pub fn is_local_exported(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(local_def_id) = def_id.as_local() else {
        return false;
    };
    tcx.effective_visibilities(()).is_exported(local_def_id)
}

/// Whether `def_id` is a local exported `FnDef` with MIR available.
pub fn is_exported_fn_def(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !is_local_exported(tcx, def_id) {
        return false;
    }
    if !matches!(
        tcx.def_kind(def_id),
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
    ) {
        return false;
    }
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    matches!(
        tcx.type_of(def_id).skip_binder().kind(),
        rustc_middle::ty::TyKind::FnDef(..)
    )
}

/// Where the net's initial execution tokens come from.
///
/// A binary crate keeps the original semantics: only `main` starts with a
/// token. A library crate has no `entry_fn`, so the analysis reads "every
/// synchronization entry point of the library may be called concurrently by
/// an arbitrary thread": each translated concurrent root (a function whose
/// own MIR uses a lock/atomic/condvar, the same set
/// `translate_concurrent_roots` widens translation to) gets one initial token
/// on its `_start` place. This is the library's real interleaving upper
/// bound and is strictly more conservative than picking a single entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntryMode {
    /// A `main`/entry function exists; only it is initially marked.
    Main,
    /// The crate has no entry function; every concurrent root is initially
    /// marked.
    LibraryRoots,
}

impl EntryMode {
    pub fn as_str(self) -> &'static str {
        match self {
            EntryMode::Main => "main",
            EntryMode::LibraryRoots => "library-roots",
        }
    }
}

/// One reason a harvested instance is a concurrent root.
#[derive(Clone, Copy, Debug)]
pub struct RootMark {
    pub instance: InstanceId,
    pub reason: RootReason,
    pub is_private: bool,
}

pub struct EntryPlan {
    pub mode: EntryMode,
    /// Library-mode concurrent roots. Empty in `Main` mode.
    pub roots: FxHashSet<InstanceId>,
    /// `None` when `entry_reachable` is off, or when a library crate has no
    /// concurrent-root bound (`translate_concurrent_roots` disabled).
    pub reachable: Option<FxHashSet<InstanceId>>,
    /// Library mode fell back to every sync root because the exported set
    /// and the reverse-reachable set were disjoint. Always false for `Main`.
    pub fallback_used: bool,
    /// Exported instances used to count public marks. Empty in `Main` mode.
    pub exported: FxHashSet<InstanceId>,
    /// Sync roots that are not exported, when the public-entry set is used.
    pub private_skipped: usize,
}

/// Facts read from the call graph and the resource plan. No choice is made here.
pub struct EntryFacts<'a> {
    pub has_entry_fn: bool,
    pub exported: FxHashSet<InstanceId>,
    pub sync_roots: &'a FxHashSet<InstanceId>,
    /// `callgraph.reverse_reachable_from_roots(sync_roots)`.
    pub reverse_reachable: FxHashSet<InstanceId>,
    /// `callgraph.reachable_from_entry(main)`. Empty when there is no main.
    pub main_reachable: FxHashSet<InstanceId>,
}

/// Pure choice. Reachability is filled in afterwards with one graph walk.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntryDecision {
    pub mode: EntryMode,
    pub roots: FxHashSet<InstanceId>,
    pub fallback_used: bool,
    pub exported: FxHashSet<InstanceId>,
    pub private_skipped: usize,
}

/// Pure function: no `TyCtxt`, no `Coverage`, no logs.
pub fn decide(facts: &EntryFacts) -> EntryDecision {
    if facts.has_entry_fn {
        return EntryDecision {
            mode: EntryMode::Main,
            roots: FxHashSet::default(),
            fallback_used: false,
            exported: FxHashSet::default(),
            private_skipped: 0,
        };
    }
    // Same insertion order as the old `exported.iter().filter(reverse)`.
    let public_entries: FxHashSet<InstanceId> = facts
        .exported
        .iter()
        .copied()
        .filter(|id| facts.reverse_reachable.contains(id))
        .collect();
    if public_entries.is_empty() {
        EntryDecision {
            mode: EntryMode::LibraryRoots,
            roots: facts.sync_roots.iter().copied().collect(),
            fallback_used: true,
            exported: facts.exported.clone(),
            private_skipped: 0,
        }
    } else {
        let private_skipped = facts
            .sync_roots
            .iter()
            .filter(|id| !facts.exported.contains(id))
            .count();
        EntryDecision {
            mode: EntryMode::LibraryRoots,
            roots: public_entries,
            fallback_used: false,
            exported: facts.exported.clone(),
            private_skipped,
        }
    }
}

/// Facts the caller writes into `translation-coverage.json`.
///
/// `marks` are the concurrent-root records. `by_reason` counts each reason
/// once per instance, the same way the coverage file does.
pub struct EntryCoverage {
    pub mode: EntryMode,
    pub by_reason: BTreeMap<RootReason, usize>,
    pub private_skipped: usize,
    pub fallback_used: bool,
    pub exported: usize,
    pub marks: Vec<RootMark>,
}

pub struct EntryPlanner<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub options: &'a Options,
    pub callgraph: &'a CallGraph<'tcx>,
}

fn reason_counts(marks: &[RootMark]) -> BTreeMap<RootReason, usize> {
    let mut per_instance: BTreeMap<usize, BTreeSet<RootReason>> = BTreeMap::new();
    for mark in marks {
        per_instance
            .entry(mark.instance.index())
            .or_default()
            .insert(mark.reason);
    }
    let mut counts = BTreeMap::new();
    for reasons in per_instance.values() {
        for reason in reasons {
            *counts.entry(*reason).or_default() += 1;
        }
    }
    counts
}

impl<'a, 'tcx> EntryPlanner<'a, 'tcx> {
    pub fn plan(
        &self,
        sync_roots: &FxHashSet<InstanceId>,
        marks: &[RootMark],
    ) -> (EntryPlan, EntryCoverage) {
        let (facts, recorded) = self.gather(sync_roots, marks);
        let decision = decide(&facts);
        if !facts.has_entry_fn {
            if decision.fallback_used {
                log::warn!(
                    "library entry: E ∩ R is empty (exported functions={}, sync roots={}); falling back to all {} sync root(s)",
                    facts.exported.len(),
                    facts.sync_roots.len(),
                    facts.sync_roots.len()
                );
            }
            log::info!(
                "no `entry_fn`: library-root initial marking over {} entry function(s) (sync roots={}, fallback={})",
                decision.roots.len(),
                facts.sync_roots.len(),
                decision.fallback_used
            );
        }
        let reachable = self.reachable_for(&decision, &facts);
        let plan = EntryPlan {
            mode: decision.mode,
            roots: decision.roots,
            reachable,
            fallback_used: decision.fallback_used,
            exported: decision.exported,
            private_skipped: decision.private_skipped,
        };
        log::info!(
            "entry-plan: mode={} roots={} exported={} reachable={} fallback={} priv={}",
            plan.mode.as_str(),
            plan.roots.len(),
            plan.exported.len(),
            plan.reachable.as_ref().map(|set| set.len()).unwrap_or(0),
            plan.fallback_used,
            plan.private_skipped,
        );
        let coverage = EntryCoverage {
            mode: plan.mode,
            by_reason: reason_counts(&recorded),
            private_skipped: plan.private_skipped,
            fallback_used: plan.fallback_used,
            exported: plan.exported.len(),
            marks: recorded,
        };
        (plan, coverage)
    }

    /// The old fetches, in the same cases: a main crate does not use sync
    /// roots unless entry reachability will union them in; a library crate
    /// always does. The set itself comes from the resource plan.
    fn gather<'b>(
        &self,
        sync_roots: &'b FxHashSet<InstanceId>,
        marks: &[RootMark],
    ) -> (EntryFacts<'b>, Vec<RootMark>) {
        let main_func = self.tcx.entry_fn(()).map(|(id, _)| id);
        let has_entry_fn = main_func.is_some();
        if has_entry_fn {
            let main_reachable = if self.options.config.entry_reachable {
                self.callgraph
                    .reachable_from_entry(self.tcx, main_func.unwrap())
            } else {
                FxHashSet::default()
            };
            let recorded = if self.options.config.entry_reachable
                && self.options.config.translate_concurrent_roots
            {
                marks.to_vec()
            } else {
                Vec::new()
            };
            return (
                EntryFacts {
                    has_entry_fn,
                    exported: FxHashSet::default(),
                    sync_roots,
                    reverse_reachable: FxHashSet::default(),
                    main_reachable,
                },
                recorded,
            );
        }
        let exported = self.exported_functions();
        let recorded = marks.to_vec();
        let reverse_reachable = self
            .callgraph
            .reverse_reachable_from_roots(sync_roots.iter().copied());
        (
            EntryFacts {
                has_entry_fn,
                exported,
                sync_roots,
                reverse_reachable,
                main_reachable: FxHashSet::default(),
            },
            recorded,
        )
    }

    /// The old graph walk. Uses sets already stored on `facts` so the sync-root
    /// scan is not repeated.
    fn reachable_for(
        &self,
        decision: &EntryDecision,
        facts: &EntryFacts,
    ) -> Option<FxHashSet<InstanceId>> {
        if !self.options.config.entry_reachable {
            return None;
        }
        if decision.mode == EntryMode::Main {
            let mut reachable = facts.main_reachable.clone();
            if self.options.config.translate_concurrent_roots {
                let reachable_from_concurrent = self
                    .callgraph
                    .reachable_from_roots(facts.sync_roots.iter().copied());
                reachable.extend(reachable_from_concurrent);
            }
            return Some(reachable);
        }
        // Library crate: no `main`, so the concurrent roots are the
        // entries — the same set that receives the initial tokens. With
        // `translate_concurrent_roots` disabled there is no root notion
        // to bound the net, so keep the old behavior of translating
        // every function.
        if !self.options.config.translate_concurrent_roots {
            return None;
        }
        Some(
            self.callgraph
                .reachable_from_roots(decision.roots.clone().into_iter()),
        )
    }

    pub(crate) fn exported_functions(&self) -> FxHashSet<InstanceId> {
        let mut exported_defs: FxHashSet<DefId> = FxHashSet::default();
        for (local_def_id, _) in self.tcx.effective_visibilities(()).iter() {
            let def_id = local_def_id.to_def_id();
            if is_exported_fn_def(self.tcx, def_id) {
                exported_defs.insert(def_id);
            }
        }
        let mut exported_instances = FxHashSet::default();
        for (instance_id, node) in self.callgraph.graph.node_references() {
            let def_id = node.instance().def_id();
            if exported_defs.contains(&def_id) || is_exported_fn_def(self.tcx, def_id) {
                exported_instances.insert(instance_id);
            }
        }
        exported_instances
    }
}

#[cfg(test)]
mod tests {
    use petgraph::graph::NodeIndex;
    use rustc_data_structures::fx::FxHashSet;

    use super::{EntryDecision, EntryFacts, EntryMode, InstanceId, decide};

    fn id(n: usize) -> InstanceId {
        NodeIndex::new(n)
    }

    fn set(ids: &[usize]) -> FxHashSet<InstanceId> {
        ids.iter().copied().map(id).collect()
    }

    fn set_in_order(ids: &[usize]) -> FxHashSet<InstanceId> {
        let mut out = FxHashSet::default();
        for n in ids {
            out.insert(id(*n));
        }
        out
    }

    fn decide_case(
        has_entry_fn: bool,
        exported: &[usize],
        sync_roots: &[usize],
        reverse_reachable: &[usize],
    ) -> EntryDecision {
        let exported = set(exported);
        let sync_roots = set(sync_roots);
        let reverse_reachable = set(reverse_reachable);
        decide(&EntryFacts {
            has_entry_fn,
            exported,
            sync_roots: &sync_roots,
            reverse_reachable,
            main_reachable: FxHashSet::default(),
        })
    }

    fn assert_decision(
        decision: &EntryDecision,
        mode: EntryMode,
        roots: &[usize],
        fallback: bool,
        exported: &[usize],
        skipped: usize,
    ) {
        assert_eq!(decision.mode, mode);
        assert_eq!(decision.roots, set(roots));
        assert_eq!(decision.fallback_used, fallback);
        assert_eq!(decision.exported, set(exported));
        assert_eq!(decision.private_skipped, skipped);
    }

    #[test]
    fn main_mode_ignores_exported_and_roots() {
        let decision = decide_case(true, &[1, 2, 9], &[1, 4], &[1, 2]);
        assert_decision(&decision, EntryMode::Main, &[], false, &[], 0);
    }

    #[test]
    fn library_mode_intersects_exported_with_reverse_reachable() {
        // 9 is exported but not reverse-reachable, so it stays out of roots.
        // 3 is reverse-reachable but not exported, so it stays out too.
        let decision = decide_case(false, &[1, 2, 9], &[1, 2, 4], &[1, 2, 3]);
        assert_decision(
            &decision,
            EntryMode::LibraryRoots,
            &[1, 2],
            false,
            &[1, 2, 9],
            1,
        );
        assert!(!decision.roots.contains(&id(9)));
        assert!(!decision.roots.contains(&id(3)));
        assert!(!decision.roots.contains(&id(4)));
    }

    #[test]
    fn library_mode_falls_back_when_intersection_is_empty() {
        let decision = decide_case(false, &[1], &[2, 3], &[2]);
        assert_decision(&decision, EntryMode::LibraryRoots, &[2, 3], true, &[1], 0);
    }

    #[test]
    fn library_mode_falls_back_when_exported_is_empty() {
        let decision = decide_case(false, &[], &[1, 2], &[1]);
        assert_decision(&decision, EntryMode::LibraryRoots, &[1, 2], true, &[], 0);
    }

    #[test]
    fn library_mode_falls_back_when_sync_roots_is_empty() {
        let decision = decide_case(false, &[1], &[], &[]);
        assert_decision(&decision, EntryMode::LibraryRoots, &[], true, &[1], 0);
    }

    #[test]
    fn private_skipped_counts_roots_outside_exported() {
        // 2 is exported and reverse-reachable but not a sync root. 5 and 6 are
        // sync roots outside exported. 8 is exported and not reverse-reachable.
        let decision = decide_case(false, &[1, 2, 8], &[1, 5, 6], &[1, 2]);
        assert_decision(
            &decision,
            EntryMode::LibraryRoots,
            &[1, 2],
            false,
            &[1, 2, 8],
            2,
        );
        assert!(!decision.roots.contains(&id(8)));
    }

    #[test]
    fn decide_is_deterministic_for_permuted_inputs() {
        let exported_a = set_in_order(&[1, 2, 9]);
        let roots_a = set_in_order(&[1, 4, 5]);
        let reverse_a = set_in_order(&[1, 2, 3]);
        let exported_b = set_in_order(&[9, 2, 1]);
        let roots_b = set_in_order(&[5, 1, 4]);
        let reverse_b = set_in_order(&[3, 1, 2]);
        let a = decide(&EntryFacts {
            has_entry_fn: false,
            exported: exported_a,
            sync_roots: &roots_a,
            reverse_reachable: reverse_a,
            main_reachable: FxHashSet::default(),
        });
        let b = decide(&EntryFacts {
            has_entry_fn: false,
            exported: exported_b,
            sync_roots: &roots_b,
            reverse_reachable: reverse_b,
            main_reachable: FxHashSet::default(),
        });
        assert_eq!(a.mode, b.mode);
        assert_eq!(a.fallback_used, b.fallback_used);
        assert_eq!(a.private_skipped, b.private_skipped);
        assert_eq!(a.roots, b.roots);
        assert_eq!(a.exported, b.exported);
    }

    #[test]
    fn main_mode_never_falls_back() {
        let decision = decide_case(true, &[1], &[2, 3], &[4]);
        assert_decision(&decision, EntryMode::Main, &[], false, &[], 0);
    }
}
