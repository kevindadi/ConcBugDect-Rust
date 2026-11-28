//! The only translation module that talks to `unipn`.
//! Lowering and resource construction call this facade.

pub(crate) mod provenance;
mod registry;
pub mod subnets;

pub use provenance::{TransOrigin, TranslationProvenance};

pub use registry::{CustomLockEntry, FunctionRegistry, ResourceRegistry};

use std::marker::PhantomData;

pub use unipn::ArcDir;
use unipn::pt::{PtPlaceKind, PtTransitionKind};

pub use unipn::analysis::pt::reachability::StateGraph;
pub use unipn::pt::{
    AliasId, AtomicOrdering, DiagnosticReport, PlaceType, TransitionType, UnsafeOp,
};
pub use unipn::{ControlSub, Marking, PlaceId, TransitionId};

/// P/T place class (`unipn::PlaceClass<()>`).
pub type PlaceClass = PlaceType;

/// Classification of shared-resource places inferred from P/T structure and
/// place naming conventions (since `unipn::pt::PlaceType` is `PlaceClass<()>`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ResourceKind {
    Mutex,
    RwLock,
    Condvar,
    Atomic,
    Thread,
}

/// Infer the [`ResourceKind`] of a P/T resource place from its incident
/// transitions and place naming conventions.
pub fn infer_resource_kind(net: &Net, place: PlaceId) -> Option<ResourceKind> {
    let p = net.place(place)?;
    if !matches!(p.kind.place_type, unipn::PlaceClass::Resource(())) {
        return None;
    }
    if p.name.starts_with("data.") {
        return None;
    }

    let mut saw_unlock_unit = false;
    let mut saw_wait = false;
    for arc in net.arcs_at(place) {
        let Some(t) = net.transition(arc.transition) else {
            continue;
        };
        match &t.kind.transition_type {
            TransitionType::RwLockRead(idx)
            | TransitionType::RwLockWrite(idx)
            | TransitionType::DropRead(idx)
            | TransitionType::DropWrite(idx)
                if *idx == place.index() =>
            {
                return Some(ResourceKind::RwLock);
            }
            TransitionType::Lock(idx) if *idx == place.index() => {
                return Some(ResourceKind::Mutex);
            }
            TransitionType::Notify(idx) if *idx == place.index() => {
                return Some(ResourceKind::Condvar);
            }
            TransitionType::AtomicLoad(..)
            | TransitionType::AtomicStore(..)
            | TransitionType::AtomicCmpXchg(..) => {
                return Some(ResourceKind::Atomic);
            }
            TransitionType::Unlock(idx) if *idx == place.index() => {
                if arc.weight > 1 || p.kind.capacity.is_some_and(|c| c > 1) {
                    return Some(ResourceKind::RwLock);
                }
                saw_unlock_unit = true;
            }
            TransitionType::Wait => {
                saw_wait = true;
            }
            _ => {}
        }
    }

    let name = p.name.as_str();
    if name.starts_with("RwLock_") || name.starts_with("RwLock:") {
        return Some(ResourceKind::RwLock);
    }
    if name.starts_with("Mutex_") || name.starts_with("Mutex:") {
        return Some(ResourceKind::Mutex);
    }
    if name.starts_with("Condvar:")
        || name.starts_with("Condvar_")
        || name.starts_with("Waiting:")
    {
        return Some(ResourceKind::Condvar);
    }
    if name.starts_with("Atomic(")
        || name.starts_with("Atomic_")
        || name.starts_with("atomic(")
        || name == "SeqCst_Global"
    {
        return Some(ResourceKind::Atomic);
    }
    if name.starts_with("Thread_") || name.starts_with("thread_") {
        return Some(ResourceKind::Thread);
    }
    if saw_unlock_unit {
        return Some(ResourceKind::Mutex);
    }
    if saw_wait {
        return Some(ResourceKind::Condvar);
    }
    if p.kind.capacity.is_some_and(|c| c > 1) {
        return Some(ResourceKind::RwLock);
    }
    None
}

/// Finished P/T net (`unipn::pt::PtNet`).
pub type Net = unipn::pt::PtNet;

/// A transition's P/T kind. The lifetime ties the value to the crate being
/// lowered; the payload itself does not borrow `TyCtxt`.
pub struct TransitionKind<'tcx> {
    ty: TransitionType,
    origin: Option<provenance::TransOrigin>,
    _tcx: PhantomData<&'tcx ()>,
}

impl<'tcx> TransitionKind<'tcx> {
    pub fn new(ty: TransitionType) -> Self {
        Self {
            ty,
            origin: None,
            _tcx: PhantomData,
        }
    }

    pub fn with_origin(ty: TransitionType, origin: provenance::TransOrigin) -> Self {
        Self {
            ty,
            origin: Some(origin),
            _tcx: PhantomData,
        }
    }
}

/// P/T builder plus, from step 2, the provenance table.
///
/// `place` / `marked_place` are the short constructors (empty span). Production
/// places that also carry a span use [`Self::add_place`], which keeps tokens,
/// capacity, and span together.
pub struct NetBuilder<'tcx> {
    inner: unipn::pt::PtBuilder,
    provenance: provenance::TranslationProvenance,
    cir_channels: std::collections::BTreeMap<String, PlaceId>,
    _tcx: PhantomData<&'tcx ()>,
}

impl<'tcx> NetBuilder<'tcx> {
    pub fn new() -> Self {
        Self {
            inner: unipn::pt::PtBuilder::empty(),
            provenance: provenance::TranslationProvenance::default(),
            cir_channels: std::collections::BTreeMap::new(),
            _tcx: PhantomData,
        }
    }

    /// Shared message-buffer place (`initial_tokens = 0`) pairing `cir_sync::channel_send`
    /// and `cir_sync::channel_recv` transitions on the same channel field.
    pub fn cir_channel_place(&mut self, key: &str) -> PlaceId {
        if let Some(&pid) = self.cir_channels.get(key) {
            return pid;
        }
        let pid = self.add_place(
            format!("Channel:{key}"),
            0,
            usize::MAX,
            PlaceClass::Resource(()),
            String::new(),
        );
        self.cir_channels.insert(key.to_string(), pid);
        pid
    }

    /// Empty place. `capacity == usize::MAX` means unbounded.
    pub fn place(&mut self, kind: PlaceClass, name: impl Into<String>, capacity: usize) -> PlaceId {
        self.add_place(name, 0, capacity, kind, String::new())
    }

    /// Place with `tokens`, unbounded capacity, empty span.
    pub fn marked_place(
        &mut self,
        kind: PlaceClass,
        name: impl Into<String>,
        tokens: usize,
    ) -> PlaceId {
        self.add_place(name, tokens, usize::MAX, kind, String::new())
    }

    /// Full place constructor. `usize::MAX` capacity means unbounded.
    pub fn add_place(
        &mut self,
        name: impl Into<String>,
        tokens: usize,
        capacity: usize,
        kind: PlaceClass,
        span: impl Into<String>,
    ) -> PlaceId {
        self.inner.add_marked_place(
            name.into(),
            pt_place_kind(kind, span.into(), capacity),
            tokens,
        )
    }

    pub fn transition(
        &mut self,
        kind: TransitionKind<'tcx>,
        name: impl Into<String>,
    ) -> TransitionId {
        let id = self
            .inner
            .add_transition(name.into(), PtTransitionKind::new(kind.ty));
        if let Some(origin) = kind.origin {
            let recorded = self.provenance.origins.iter().count();
            debug_assert_eq!(recorded, id.index());
            self.provenance.origins.push(origin);
        }
        id
    }

    pub fn provenance(&self) -> &provenance::TranslationProvenance {
        &self.provenance
    }

    pub fn provenance_mut(&mut self) -> &mut provenance::TranslationProvenance {
        &mut self.provenance
    }

    pub fn arc_in(&mut self, place: PlaceId, transition: TransitionId, weight: usize) {
        self.inner.add_input_arc(place, transition, weight);
    }

    pub fn arc_out(&mut self, place: PlaceId, transition: TransitionId, weight: usize) {
        self.inner.add_output_arc(place, transition, weight);
    }

    pub fn set_transition_kind(&mut self, transition: TransitionId, kind: TransitionKind<'tcx>) {
        if let Some(slot) = self.inner.transition_kind_mut(transition) {
            slot.transition_type = kind.ty;
        }
    }

    pub fn set_place_kind(&mut self, place: PlaceId, kind: PlaceClass) {
        if let Some(slot) = self.inner.place_kind_mut(place) {
            slot.place_type = kind;
        }
    }

    /// The one `place_kind_mut` site in lowering writes capacity, not the class.
    /// `None` (unbounded) and any bound below `min` become `Some(min)`.
    pub fn ensure_capacity(&mut self, place: PlaceId, min: usize) {
        if let Some(slot) = self.inner.place_kind_mut(place)
            && slot.capacity.map_or(true, |capacity| capacity < min)
        {
            slot.capacity = Some(min);
        }
    }

    pub fn set_tokens(&mut self, place: PlaceId, tokens: usize) {
        self.inner.set_initial_tokens(place, tokens);
    }

    /// Both an input and an output arc of weight 1 touch `place`.
    /// Replaces the test that walked `arcs_for`.
    pub fn fans_out(&self, place: PlaceId) -> bool {
        let mut takes = false;
        let mut restores = false;
        for arc in self.inner.net().arcs_at(place) {
            if arc.weight != 1 {
                continue;
            }
            match arc.direction {
                ArcDir::Input => takes = true,
                ArcDir::Output => restores = true,
                ArcDir::Read | ArcDir::Inhibitor | ArcDir::Reset => {}
            }
        }
        takes && restores
    }

    pub fn place_kind(&self, place: PlaceId) -> Option<&PlaceClass> {
        self.inner
            .net()
            .place(place)
            .map(|place| &place.kind.place_type)
    }

    pub fn place_name(&self, place: PlaceId) -> Option<String> {
        self.inner
            .net()
            .place(place)
            .map(|place| place.name.clone())
    }

    /// Input arcs leave `place` toward a transition and consume its token.
    pub fn has_consumer(&self, place: PlaceId) -> bool {
        self.inner
            .net()
            .arcs_at(place)
            .any(|arc| arc.direction == ArcDir::Input)
    }

    /// Transitions that consume `place`, in arc insertion order.
    pub fn consumer_transitions(&self, place: PlaceId) -> Vec<TransitionId> {
        self.inner
            .net()
            .arcs_at(place)
            .filter(|arc| arc.direction == ArcDir::Input)
            .map(|arc| arc.transition)
            .collect()
    }

    pub fn transition_count(&self) -> usize {
        self.inner.num_transitions()
    }

    /// Pre-reduction snapshot for the deadlock report. Everything else uses [`finish`].
    pub fn snapshot(&self) -> (Net, Marking) {
        self.inner.snapshot()
    }

    pub fn finish(self) -> (Net, Marking) {
        self.inner.build()
    }

    pub fn log_diagnostics(&self) {
        self.inner.log_diagnostics();
    }

    pub fn diagnose_connectivity(&self) -> DiagnosticReport {
        self.inner.diagnose_connectivity()
    }
}

/// Builds a P/T place kind. `usize::MAX` capacity is the old spelling of
/// unbounded (`None`).
fn pt_place_kind(kind: PlaceClass, span: String, capacity: usize) -> PtPlaceKind {
    PtPlaceKind {
        place_type: kind,
        span,
        capacity: (capacity != usize::MAX).then_some(capacity),
    }
}

/// Unbounded basic-block control place. Shared by the guard-wiring and loop tests.
#[cfg(test)]
pub(crate) fn control_place(net: &mut NetBuilder<'_>, name: &str, tokens: usize) -> PlaceId {
    net.marked_place(
        PlaceClass::Control(ControlSub::BasicBlock),
        name.to_string(),
        tokens,
    )
}

/// Unbounded function-end control place with no initial token.
#[cfg(test)]
pub(crate) fn function_end(net: &mut NetBuilder<'_>, name: &str) -> PlaceId {
    net.place(
        PlaceClass::Control(ControlSub::FunctionEnd),
        name.to_string(),
        usize::MAX,
    )
}

impl<'analysis, 'tcx> crate::translate::construct::PetriNet<'analysis, 'tcx> {
    pub(crate) fn create_resource_place(
        &mut self,
        name: String,
        initial: usize,
        capacity: usize,
        span: String,
    ) -> PlaceId {
        self.net
            .add_place(name, initial, capacity, PlaceClass::Resource(()), span)
    }

    /// Function `_start`/`_end` places are execution positions, not resources:
    /// every call site (and every thread) shares them, so they must be
    /// unbounded or a concurrent call's token would be dropped at capacity 1.
    pub(crate) fn create_function_places(
        &mut self,
        func_name: String,
        with_token: bool,
    ) -> (PlaceId, PlaceId) {
        let start_name = format!("{}_start", func_name);
        let start = if with_token {
            self.net.marked_place(
                PlaceClass::Control(ControlSub::FunctionStart),
                start_name,
                1,
            )
        } else {
            self.net.place(
                PlaceClass::Control(ControlSub::FunctionStart),
                start_name,
                usize::MAX,
            )
        };
        let end = self.net.place(
            PlaceClass::Control(ControlSub::FunctionEnd),
            format!("{}_end", func_name),
            usize::MAX,
        );

        (start, end)
    }

    pub fn get_or_insert_node(&mut self, def_id: rustc_hir::def_id::DefId) -> (PlaceId, PlaceId) {
        self.functions.get_or_insert(def_id, || {
            let func_name = self.tcx.def_path_str(def_id);
            let func_start = self.net.place(
                PlaceClass::Control(ControlSub::FunctionStart),
                format!("{}_start", func_name),
                usize::MAX,
            );
            let func_end = self.net.place(
                PlaceClass::Control(ControlSub::FunctionEnd),
                format!("{}_end", func_name),
                usize::MAX,
            );
            (func_start, func_end)
        })
    }
}

#[cfg(test)]
mod facade_tests {
    use super::{
        ArcDir, ControlSub, NetBuilder, PlaceClass, TransOrigin, TransitionKind, TransitionType,
    };
    use rustc_span::DUMMY_SP;

    #[test]
    fn facade_builds_a_net_without_tyctxt() {
        let mut net = NetBuilder::new();
        let span = format!("{DUMMY_SP:?}");
        let kind = || {
            TransitionKind::with_origin(
                TransitionType::Normal,
                TransOrigin {
                    fn_def_path: String::new(),
                    bb: 0,
                    span: span.clone(),
                },
            )
        };
        let lock = net.place(PlaceClass::Control(ControlSub::BasicBlock), "lock", 1);
        net.set_tokens(lock, 1);
        let thread_a = net.place(
            PlaceClass::Control(ControlSub::FunctionStart),
            "thread_a",
            usize::MAX,
        );
        let thread_b = net.place(
            PlaceClass::Control(ControlSub::FunctionStart),
            "thread_b",
            usize::MAX,
        );
        net.set_tokens(thread_a, 1);
        net.set_tokens(thread_b, 1);

        let acq_a = net.transition(kind(), "acq_a");
        net.arc_in(thread_a, acq_a, 1);
        net.arc_in(lock, acq_a, 1);
        let rel_a = net.transition(kind(), "rel_a");
        net.arc_in(thread_a, rel_a, 1);
        net.arc_out(lock, rel_a, 1);

        let acq_b = net.transition(kind(), "acq_b");
        net.arc_in(thread_b, acq_b, 1);
        net.arc_in(lock, acq_b, 1);
        let rel_b = net.transition(kind(), "rel_b");
        net.arc_in(thread_b, rel_b, 1);
        net.arc_out(lock, rel_b, 1);

        assert_eq!(
            net.provenance().origins.iter().count(),
            net.transition_count()
        );
        let (built, marking) = net.finish();
        assert_eq!(marking.tokens(lock), 1);
        assert_eq!(built.num_places(), 3);
        assert_eq!(built.num_transitions(), 4);
        for acquire in [acq_a, acq_b] {
            assert!(
                built
                    .arcs_of(acquire, ArcDir::Input)
                    .any(|arc| arc.place == lock && arc.weight == 1)
            );
        }
        for release in [rel_a, rel_b] {
            assert!(
                built
                    .arcs_of(release, ArcDir::Output)
                    .any(|arc| arc.place == lock && arc.weight == 1)
            );
        }
    }
}
