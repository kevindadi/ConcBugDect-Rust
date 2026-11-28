//! Compare a proposed partition with the places the current binders built.
//!
//! The comparison is a set of member keys. It does not create places and it
//! does not change the net.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use rustc_data_structures::fx::FxHashMap;
use serde_json::{Value, json};

use crate::analysis::memory::pointsto::AliasId;
use crate::analysis::primitives::blocking::LockGuardId;

use super::{SiteKind, SyncSite};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemberDiff {
    pub kind: String,
    pub old: Vec<String>,
    pub new: Vec<String>,
}

pub(crate) fn guard_key(guard: &LockGuardId) -> String {
    format!(
        "{}:{}:{}",
        guard.instance_id.index(),
        guard.local.as_u32(),
        guard.field.unwrap_or(u32::MAX)
    )
}

pub(crate) fn alias_key(alias: &AliasId) -> String {
    format!(
        "{}:{}:{}:{}",
        alias.instance_id.index(),
        alias.local.as_u32(),
        alias.field.unwrap_or(u32::MAX),
        alias.array_index.unwrap_or(u64::MAX)
    )
}

pub(crate) fn site_key(site: &SyncSite<'_>) -> String {
    match site.kind {
        SiteKind::Mutex | SiteKind::RwLock => site
            .origin
            .guard()
            .map(|guard| guard_key(&guard))
            .unwrap_or_else(|| alias_key(&site.object)),
        _ => alias_key(&site.object),
    }
}

/// Groups whose member sets differ. Identical sets are dropped, so an empty
/// result means the proposed partition names the same classes.
pub(crate) fn diff_sets(
    kind: &str,
    old: &[BTreeSet<String>],
    new: &[BTreeSet<String>],
) -> Vec<MemberDiff> {
    let old_only: Vec<&BTreeSet<String>> = old.iter().filter(|set| !new.contains(set)).collect();
    let new_only: Vec<&BTreeSet<String>> = new.iter().filter(|set| !old.contains(set)).collect();
    let mut diffs = Vec::new();
    let n = old_only.len().max(new_only.len());
    for i in 0..n {
        diffs.push(MemberDiff {
            kind: kind.to_string(),
            old: old_only
                .get(i)
                .map(|set| set.iter().cloned().collect())
                .unwrap_or_default(),
            new: new_only
                .get(i)
                .map(|set| set.iter().cloned().collect())
                .unwrap_or_default(),
        });
    }
    diffs
}

pub(crate) fn sets_from_groups(groups: &[Vec<LockGuardId>]) -> Vec<BTreeSet<String>> {
    groups
        .iter()
        .map(|group| group.iter().map(guard_key).collect())
        .filter(|set: &BTreeSet<String>| !set.is_empty())
        .collect()
}

pub(crate) fn invert_groups(map: &FxHashMap<AliasId, u32>) -> Vec<BTreeSet<String>> {
    let mut by_group: FxHashMap<u32, BTreeSet<String>> = FxHashMap::default();
    for (alias, group) in map {
        by_group.entry(*group).or_default().insert(alias_key(alias));
    }
    by_group.into_values().collect()
}

pub(crate) fn class_sets(sites: &[SyncSite<'_>], classes: &[Vec<usize>]) -> Vec<BTreeSet<String>> {
    classes
        .iter()
        .map(|class| class.iter().map(|&index| site_key(&sites[index])).collect())
        .filter(|set: &BTreeSet<String>| !set.is_empty())
        .collect()
}

pub(crate) fn write_map(path: &Path, slots: &Value, diffs: &[MemberDiff]) -> std::io::Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let body = json!({
        "slots": slots,
        "shadow": diffs.iter().map(|diff| json!({
            "kind": diff.kind,
            "old": diff.old,
            "new": diff.new,
        })).collect::<Vec<_>>(),
    });
    fs::write(
        path,
        serde_json::to_string_pretty(&body).unwrap_or_default(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(items: &[&str]) -> BTreeSet<String> {
        items.iter().map(|item| (*item).to_string()).collect()
    }

    #[test]
    fn identical_sets_have_no_diff() {
        let sets = vec![set(&["a", "b"]), set(&["c"])];
        assert!(diff_sets("mutex", &sets, &sets).is_empty());
    }

    #[test]
    fn a_split_reports_the_old_set_and_the_new_pieces() {
        let old = vec![set(&["a", "b"])];
        let new = vec![set(&["a"]), set(&["b"])];
        let diffs = diff_sets("mutex", &old, &new);
        assert_eq!(diffs.len(), 2);
        assert_eq!(diffs[0].kind, "mutex");
    }
}
