//! Async translation context: tracks task lifecycle while building the Petri net.

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rust_petri_net_analysis::net::{Net, PlaceId};

use crate::translate::async_ppn::TaskLifecyclePlaces;
use crate::translate::async_ppn::{TaskId, add_task_lifecycle_places, add_worker_place};

/// Stateful helper used during Petri-net construction for async tasks.
#[derive(Default)]
pub struct AsyncTranslateContext {
    pub worker_place: Option<PlaceId>,
    pub worker_count: u64,
    pub spawn_to_task: FxHashMap<DefId, TaskId>,
    pub task_lifecycle: FxHashMap<usize, TaskLifecyclePlaces>,
    next_task_id: usize,
}

impl AsyncTranslateContext {
    pub fn new(worker_count: u64) -> Self {
        Self {
            worker_place: None,
            worker_count,
            spawn_to_task: FxHashMap::default(),
            task_lifecycle: FxHashMap::default(),
            next_task_id: 0,
        }
    }

    pub fn alloc_task_id(&mut self) -> TaskId {
        let id = TaskId::new(self.next_task_id);
        self.next_task_id += 1;
        id
    }

    pub fn register_spawn(&mut self, spawn_def_id: DefId, task_id: TaskId) {
        self.spawn_to_task.insert(spawn_def_id, task_id);
    }

    pub fn get_task_for_spawn(&self, spawn_def_id: DefId) -> Option<TaskId> {
        self.spawn_to_task.get(&spawn_def_id).copied()
    }

    pub fn ensure_worker_place(&mut self, net: &mut Net) -> PlaceId {
        if let Some(p) = self.worker_place {
            return p;
        }
        let p = add_worker_place(net, self.worker_count);
        self.worker_place = Some(p);
        p
    }

    /// Register lifecycle places for a task without await sites.
    pub fn add_task_simple(&mut self, net: &mut Net, task_id: TaskId) -> TaskLifecyclePlaces {
        let tp = add_task_lifecycle_places(net, task_id, &[], false);
        self.task_lifecycle.insert(task_id.index(), tp.clone());
        tp
    }

    pub fn get_task_places(&self, task_id: TaskId) -> Option<&TaskLifecyclePlaces> {
        self.task_lifecycle.get(&task_id.index())
    }
}
