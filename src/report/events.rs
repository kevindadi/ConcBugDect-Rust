//! Writes `events.json`: original-net transitions that are observable sync events.
//! Each site gets a stable `site_id` for replay.
//! It does not schedule those events.

use std::fs;
use std::path::Path;

use serde_json::{Value, json};
use unipn::net::{ArcDir, PlaceId};
use unipn::pt::{PtNet, TransitionType};

use crate::translate::lower::facts::TranslationProvenance;

/// Identifies the JSON shape; bumped when a field changes meaning.
pub const EVENT_SCHEMA: &str = "pn-event-sites/1";

/// The event classes a replay can observe.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EventKind {
    Lock,
    RwLockRead,
    RwLockWrite,
    Unlock,
    DropRead,
    DropWrite,
    Wait,
    Notify,
    Spawn,
    Join,
    AtomicLoad,
    AtomicStore,
    AtomicCmpXchg,
}

impl EventKind {
    /// Classify a net transition type, or `None` when it is not an event.
    pub fn classify(transition_type: &TransitionType) -> Option<EventKind> {
        Some(match transition_type {
            TransitionType::Lock(_) => EventKind::Lock,
            TransitionType::RwLockRead(_) => EventKind::RwLockRead,
            TransitionType::RwLockWrite(_) => EventKind::RwLockWrite,
            TransitionType::Unlock(_) => EventKind::Unlock,
            TransitionType::DropRead(_) => EventKind::DropRead,
            TransitionType::DropWrite(_) => EventKind::DropWrite,
            TransitionType::Wait => EventKind::Wait,
            TransitionType::Notify(_) => EventKind::Notify,
            TransitionType::Spawn(_) => EventKind::Spawn,
            TransitionType::Join(_) => EventKind::Join,
            TransitionType::AtomicLoad(..) => EventKind::AtomicLoad,
            TransitionType::AtomicStore(..) => EventKind::AtomicStore,
            TransitionType::AtomicCmpXchg(..) => EventKind::AtomicCmpXchg,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            EventKind::Lock => "Lock",
            EventKind::RwLockRead => "RwLockRead",
            EventKind::RwLockWrite => "RwLockWrite",
            EventKind::Unlock => "Unlock",
            EventKind::DropRead => "DropRead",
            EventKind::DropWrite => "DropWrite",
            EventKind::Wait => "Wait",
            EventKind::Notify => "Notify",
            EventKind::Spawn => "Spawn",
            EventKind::Join => "Join",
            EventKind::AtomicLoad => "AtomicLoad",
            EventKind::AtomicStore => "AtomicStore",
            EventKind::AtomicCmpXchg => "AtomicCmpXchg",
        }
    }

    /// Whether the replay conductor sets a gate on this event. Atomics are
    /// recorded only: the net assigns them no queue semantics.
    pub fn gated(self) -> bool {
        !matches!(
            self,
            EventKind::AtomicLoad | EventKind::AtomicStore | EventKind::AtomicCmpXchg
        )
    }
}

/// One event-class transition of the original net.
#[derive(Clone, Debug)]
pub struct EventSite {
    pub site_id: usize,
    pub transition_id: unipn::TransitionId,
    pub kind: EventKind,
    pub resource: String,
}

/// The event sites of a net, ordered by transition id; `site_id` is the
/// ordinal in that order.
///
/// Deterministic: the scan is a single index-order pass over the net.
pub fn event_sites(net: &PtNet) -> Vec<EventSite> {
    let mut sites = Vec::new();
    for index in 0..net.num_transitions() {
        let transition = unipn::TransitionId::from(index);
        let Some(kind) = net
            .transition(transition)
            .and_then(|t| EventKind::classify(&t.kind.transition_type))
        else {
            continue;
        };
        sites.push(EventSite {
            site_id: sites.len(),
            transition_id: transition,
            kind,
            resource: resource_name(net, transition),
        });
    }
    sites
}

/// The resource place a transition touches: the place id in the transition
/// type's payload when it carries one, else the first resource-class input arc
/// (this is how `Wait` finds its condition variable). `Spawn`/`Join` name the
/// spawned/joined function instead, and atomics render their alias.
pub fn resource_name(net: &PtNet, transition: unipn::TransitionId) -> String {
    let Some(kind) = net.transition(transition).map(|t| &t.kind.transition_type) else {
        return String::new();
    };
    match kind {
        TransitionType::Spawn(name) | TransitionType::Join(name) => name.clone(),
        TransitionType::AtomicLoad(alias, _, span, _)
        | TransitionType::AtomicStore(alias, _, span, _)
        | TransitionType::AtomicCmpXchg(alias, _, _, span, _) => {
            format!("atomic({alias:?} {span})")
        }
        _ => {
            let payload_place = match kind {
                TransitionType::Lock(place)
                | TransitionType::RwLockRead(place)
                | TransitionType::RwLockWrite(place)
                | TransitionType::Unlock(place)
                | TransitionType::DropRead(place)
                | TransitionType::DropWrite(place)
                | TransitionType::Notify(place) => Some(PlaceId::from(*place)),
                _ => None,
            };
            if let Some(place) = payload_place {
                if let Some(p) = net.place(place) {
                    return p.name.clone();
                }
            }
            // `Wait` carries no payload; its condition variable is the
            // resource-class input arc the translation wired to the wait.
            net.arcs_of(transition, ArcDir::Input)
                .find(|arc| net.is_resource(arc.place))
                .and_then(|arc| net.place(arc.place))
                .map(|p| p.name.clone())
                .unwrap_or_default()
        }
    }
}

/// Build the `events.json` value.
pub fn build_events(crate_name: &str, net: &PtNet, provenance: &TranslationProvenance) -> Value {
    let sites: Vec<Value> = event_sites(net)
        .iter()
        .map(|site| {
            let origin = provenance.origin(site.transition_id);
            let (function, bb, span) = match origin {
                Some(origin) => (
                    origin.fn_def_path.clone(),
                    Value::from(origin.bb),
                    origin.span.clone(),
                ),
                None => {
                    log::error!(
                        "event sites: transition {} has no provenance record",
                        site.transition_id.index()
                    );
                    (String::new(), Value::Null, String::new())
                }
            };
            let mut entry = json!({
                "site_id": site.site_id,
                "transition_id": site.transition_id.index(),
                "kind": site.kind.name(),
                "fn": function,
                "bb": bb,
                "span": span,
                "resource": site.resource,
                "gated": site.kind.gated(),
            });
            if !site.kind.gated() {
                entry["note"] = Value::from("recorded only; atomics are not gated");
            }
            entry
        })
        .collect();

    json!({
        "schema": EVENT_SCHEMA,
        "crate": crate_name,
        "sites": sites,
    })
}

/// Write `dir/events.json`, creating `dir` if needed; returns the site count.
pub fn write_events(
    crate_name: &str,
    net: &PtNet,
    provenance: &TranslationProvenance,
    dir: &Path,
) -> std::io::Result<usize> {
    let report = build_events(crate_name, net, provenance);
    let count = report["sites"].as_array().map_or(0, Vec::len);
    let mut text = serde_json::to_string_pretty(&report).map_err(std::io::Error::other)?;
    text.push('\n');
    fs::create_dir_all(dir)?;
    fs::write(dir.join("events.json"), text)?;
    Ok(count)
}

#[cfg(test)]
mod tests {
    use super::EventKind;

    /// Atomics are recorded only. Gating them would inject a
    /// conductor order the P/T net does not model (an artificial blocking
    /// point), so `gated()` stays false for all three atomic kinds and true
    /// for every queue-semantics event.
    #[test]
    fn atomics_are_recorded_not_gated() {
        for kind in [
            EventKind::AtomicLoad,
            EventKind::AtomicStore,
            EventKind::AtomicCmpXchg,
        ] {
            assert!(!kind.gated(), "{} must not be gated", kind.name());
        }
        for kind in [
            EventKind::Lock,
            EventKind::RwLockRead,
            EventKind::RwLockWrite,
            EventKind::Unlock,
            EventKind::DropRead,
            EventKind::DropWrite,
            EventKind::Wait,
            EventKind::Notify,
            EventKind::Spawn,
            EventKind::Join,
        ] {
            assert!(kind.gated(), "{} must be gated", kind.name());
        }
    }
}
