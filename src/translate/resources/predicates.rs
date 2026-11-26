//! Boolean predicate places for `Mutex<bool>` wait loops.

use crate::analysis::api_patterns::KeyApiRegex;
use crate::translate::construct::PetriNet;
use crate::translate::net::{PlaceClass, PlaceId};
use crate::util::format_name;
use petgraph::visit::IntoNodeReferences;
use rustc_data_structures::fx::FxHashSet;

impl<'analysis, 'tcx> PetriNet<'analysis, 'tcx> {
    /// Create `data.<var>.false` (initial 1, cap 1) and
    /// `data.<var>.true` (initial 0, cap 1) places for `Mutex<bool>` resources
    /// that participate in both a `*g = true` write under lock and a
    /// single-guard `while !*g { cv.wait(g) }` wait loop.
    pub(crate) fn construct_bool_guard_predicates(&mut self, key_api_regex: &KeyApiRegex) {
        if self.lock_info.is_empty() {
            return;
        }
        let reachable = self.reachable_instance_ids();
        let mut locks_with_true_write: FxHashSet<PlaceId> = FxHashSet::default();
        let mut locks_with_wait_loop: FxHashSet<PlaceId> = FxHashSet::default();

        for (node, caller) in self.callgraph.graph.node_references() {
            if let Some(ref set) = reachable {
                if !set.contains(&node) {
                    continue;
                }
            }
            let def_id = caller.instance().def_id();
            if !self.tcx.is_mir_available(def_id) || !self.crate_filter_match(&format_name(def_id))
            {
                continue;
            }
            let body = self.tcx.instance_mir(caller.instance().def);
            if body.source.promoted.is_some() {
                continue;
            }

            for (_bb, gid) in
                crate::translate::lower::guards::predicates::find_bool_guard_true_writes(
                    node,
                    body,
                    self.tcx,
                    &self.lock_info,
                )
            {
                if let Some(&lock_node) = self.resources.locks().get(&gid.get_alias_id()) {
                    locks_with_true_write.insert(lock_node);
                }
            }

            for wait_loop in crate::translate::lower::guards::predicates::find_bool_guard_wait_loops(
                node,
                body,
                self.tcx,
                &self.lock_info,
                key_api_regex,
            ) {
                if let Some(&lock_node) = self
                    .resources
                    .locks()
                    .get(&wait_loop.guard_id.get_alias_id())
                {
                    locks_with_wait_loop.insert(lock_node);
                }
            }
        }

        let mut matched_locks: Vec<PlaceId> = locks_with_wait_loop
            .intersection(&locks_with_true_write)
            .copied()
            .collect();
        matched_locks.sort_by_key(|p| p.index());

        for lock_node in matched_locks {
            let lock_name = self
                .net
                .place_name(lock_node)
                .unwrap_or_else(|| format!("Mutex_{}", lock_node.index()));
            let false_place = self.net.place(
                PlaceClass::Resource(()),
                format!("data.{}.false", lock_name),
                1,
            );
            self.net.set_tokens(false_place, 1);
            let true_place = self.net.place(
                PlaceClass::Resource(()),
                format!("data.{}.true", lock_name),
                1,
            );
            self.resources
                .bool_predicates_mut()
                .insert(lock_node, (false_place, true_place));
            log::debug!(
                "[bool-guard] created data.{}.false ({:?}) and data.{}.true ({:?}) for {:?}",
                lock_name,
                false_place,
                lock_name,
                true_place,
                lock_node
            );
        }
    }
}
