//! Resource-map shadow. Runs only for `--spn-dump-resource-map`.

use super::bind::{custom_class_sets, custom_lock_sets};
use crate::analysis::memory::pointsto::AliasId;
use crate::analysis::primitives::blocking::{LockGuardId, LockGuardMap};
use crate::translate::construct::PetriNet;
use crate::translate::net::PlaceId;
use rustc_data_structures::fx::FxHashMap;
use std::collections::BTreeSet;

impl<'analysis, 'tcx> PetriNet<'analysis, 'tcx> {
    /// Compare the unified partition with the places just built. The net is
    /// already finished; this only logs and, with `--spn-dump-resource-map`,
    /// writes `resources-map.json`.
    pub(crate) fn emit_resource_shadow(&mut self) {
        use std::collections::BTreeSet;

        use crate::analysis::sync::SiteKind;
        use crate::analysis::sync::partition::partition_indices;
        use crate::analysis::sync::shadow::{
            alias_key, class_sets, diff_sets, invert_groups, write_map,
        };

        self.fill_resource_map();
        let mut sites = self.plan.sites.clone();
        // Lock-guard classes were compared in `record_lock_shadow`, which uses
        // the same union-find and the same guard order as place construction.
        sites.retain(|site| site.origin.guard().is_none());

        let policy = self.options.config.alias_unknown_policy;
        let classes = {
            let alias = self.alias.get_mut();
            partition_indices(&sites, alias, policy)
        };

        let mut diffs = std::mem::take(&mut self.resource_shadow);
        diffs.extend(diff_sets(
            "atomic",
            &invert_atomic_places(self.resources.atomic_places()),
            &kind_sets(&sites, &classes, SiteKind::Atomic),
        ));
        diffs.extend(diff_sets(
            "unsafe",
            &invert_groups(self.resources.unsafe_groups()),
            &kind_sets(&sites, &classes, SiteKind::Unsafe),
        ));
        diffs.extend(diff_sets(
            "condvar",
            &invert_place_map(self.resources.condvars(), |id| alias_key(&id)),
            &kind_sets(&sites, &classes, SiteKind::Condvar),
        ));
        diffs.extend(diff_sets(
            "custom-lock",
            &custom_lock_sets(&self.resources),
            &custom_class_sets(&sites, &classes),
        ));

        let mut counts = FxHashMap::default();
        for diff in &diffs {
            *counts.entry(diff.kind.clone()).or_insert(0usize) += 1;
        }
        log::info!(
            "resource-shadow diffs={} lock={} atomic={} unsafe={} condvar={} custom={}",
            diffs.len(),
            counts.get("lock").copied().unwrap_or(0),
            counts.get("atomic").copied().unwrap_or(0),
            counts.get("unsafe").copied().unwrap_or(0),
            counts.get("condvar").copied().unwrap_or(0),
            counts.get("custom-lock").copied().unwrap_or(0),
        );
        for diff in diffs.iter().take(8) {
            log::info!(
                "resource-shadow {} old={} new={}",
                diff.kind,
                diff.old.len(),
                diff.new.len()
            );
        }

        if self.options.dump_options.dump_resource_map {
            let slots = slot_json(&sites, &classes);
            let path = self
                .options
                .analysis_output_dir()
                .join("resources-map.json");
            if let Err(err) = write_map(&path, &slots, &diffs) {
                log::error!("failed to write {}: {err}", path.display());
            } else {
                log::info!("resource map: {}", path.display());
            }
        }
        self.resource_shadow = diffs;

        fn kind_sets(
            sites: &[crate::analysis::sync::SyncSite<'_>],
            classes: &[Vec<usize>],
            kind: SiteKind,
        ) -> Vec<BTreeSet<String>> {
            let selected: Vec<Vec<usize>> = classes
                .iter()
                .filter(|class| {
                    sites[class[0]].kind == kind && sites[class[0]].origin.custom().is_none()
                })
                .cloned()
                .collect();
            class_sets(sites, &selected)
        }
    }

    pub(crate) fn record_lock_shadow(
        &mut self,
        guards: &FxHashMap<crate::analysis::callgraph::InstanceId, LockGuardMap<'tcx>>,
        lock_objects: &FxHashMap<LockGuardId, AliasId>,
    ) {
        use std::cell::RefCell;

        use crate::analysis::sync::guard_protected_ty;
        use crate::analysis::sync::partition::group_lock_guards;
        use crate::analysis::sync::shadow::{diff_sets, sets_from_groups};
        use crate::analysis::sync::type_compatible;

        let mut info = FxHashMap::default();
        for map in guards.values() {
            info.extend(map.clone());
        }
        let lockid_vec: Vec<LockGuardId> = info.clone().into_keys().collect();
        let policy = self.options.config.alias_unknown_policy;
        let new_groups = {
            let alias = RefCell::new(self.alias.get_mut());
            let typed = group_lock_guards(
                &lockid_vec,
                |guard| {
                    lock_objects
                        .get(guard)
                        .copied()
                        .unwrap_or_else(|| (*guard).into())
                },
                |left, right| {
                    alias
                        .borrow_mut()
                        .alias_lock_group_with_fallback(left, right)
                },
                policy,
                |left, right| {
                    type_compatible(
                        guard_protected_ty(&info[left].lockguard_ty),
                        guard_protected_ty(&info[right].lockguard_ty),
                    )
                },
            );
            typed.into_values().collect::<Vec<_>>()
        };
        let diffs = diff_sets(
            "lock",
            &sets_from_groups(self.resource_binder.groups()),
            &sets_from_groups(&new_groups),
        );
        self.resource_shadow.extend(diffs);
    }
}

fn slot_json(
    sites: &[crate::analysis::sync::SyncSite<'_>],
    classes: &[Vec<usize>],
) -> serde_json::Value {
    let slots: Vec<_> = classes
        .iter()
        .enumerate()
        .map(|(slot, class)| {
            let kind = sites[class[0]].kind.as_str();
            let members: Vec<_> = class
                .iter()
                .map(|index| {
                    let site = &sites[*index];
                    serde_json::json!({
                        "instance": site.instance.index(),
                        "local": site.local.as_u32(),
                        "kind": site.kind.as_str(),
                        "role": site.role.as_str(),
                        "ty": format!("{:?}", site.ty),
                        "span": site.span,
                    })
                })
                .collect();
            serde_json::json!({
                "slot": slot,
                "kind": kind,
                "members": members,
            })
        })
        .collect();
    serde_json::Value::Array(slots)
}

pub(crate) fn invert_place_map<T: Copy>(
    map: &FxHashMap<T, PlaceId>,
    key: impl Fn(T) -> String,
) -> Vec<BTreeSet<String>> {
    let mut by_place: FxHashMap<PlaceId, BTreeSet<String>> = FxHashMap::default();
    for (id, place) in map {
        by_place.entry(*place).or_default().insert(key(*id));
    }
    by_place.into_values().collect()
}

pub(crate) fn invert_atomic_places(
    map: &FxHashMap<AliasId, Vec<PlaceId>>,
) -> Vec<BTreeSet<String>> {
    let mut by_place: FxHashMap<PlaceId, BTreeSet<String>> = FxHashMap::default();
    for (alias, places) in map {
        for place in places {
            by_place
                .entry(*place)
                .or_default()
                .insert(crate::analysis::sync::shadow::alias_key(alias));
        }
    }
    by_place.into_values().collect()
}
