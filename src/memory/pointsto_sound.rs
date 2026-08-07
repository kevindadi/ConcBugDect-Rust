//! Sound pointer analysis module with a user-friendly API.
//!
//! Provides [`PointsToResult`] as a high-level wrapper around the Andersen-style
//! constraint-based pointer analysis in [`crate::memory::pointsto`].
//!
//! # Usage
//!
//! ```ignore
//! use crate::memory::pointsto_sound::{analyze_body, PointsToResult};
//!
//! let result = analyze_body(body, tcx);
//! // Query points-to set for a local variable
//! let targets = result.points_to_set(local);
//! // Check may-alias between two locals
//! let aliased = result.may_alias(local_a, local_b);
//! // Pretty-print the full report
//! println!("{}", result.format_report());
//! ```

extern crate rustc_middle;

use std::fmt;

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::{Body, Local, Place};
use rustc_middle::ty::TyCtxt;

use crate::memory::pointsto::{Andersen, ConstraintNode, PointsToMap};

// Re-export core types so downstream can use them without importing pointsto directly.
pub use crate::memory::pointsto::{AliasAnalysis, AliasId, ApproximateAliasKind};

/// A human-readable description of a points-to target.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PointsToTarget {
    /// An allocation site, identified by the local that was allocated.
    Alloc { local: u32, projection: String },
    /// Another local variable (or a projected sub-place).
    Local { local: u32, projection: String },
    /// A constant value.
    Constant(String),
    /// A dereferenced constant.
    ConstantDeref(String),
}

impl fmt::Display for PointsToTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PointsToTarget::Alloc { local, projection } if projection.is_empty() => {
                write!(f, "Alloc(_{local})")
            }
            PointsToTarget::Alloc { local, projection } => {
                write!(f, "Alloc(_{local}{projection})")
            }
            PointsToTarget::Local { local, projection } if projection.is_empty() => {
                write!(f, "_{local}")
            }
            PointsToTarget::Local { local, projection } => {
                write!(f, "_{local}{projection}")
            }
            PointsToTarget::Constant(s) => write!(f, "Const({s})"),
            PointsToTarget::ConstantDeref(s) => write!(f, "*Const({s})"),
        }
    }
}

/// Result of a sound pointer analysis on a single function body.
///
/// Provides convenient query methods and formatted output.
pub struct PointsToResult<'tcx> {
    /// The raw points-to map from the analysis.
    raw: PointsToMap<'tcx>,
}

impl<'tcx> PointsToResult<'tcx> {
    /// Run the Andersen pointer analysis on the given function body
    /// and return a [`PointsToResult`] wrapping the result.
    pub fn analyze(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let mut andersen = Andersen::new(body, tcx);
        andersen.analyze();
        Self {
            raw: andersen.finish(),
        }
    }

    /// Borrow the raw [`PointsToMap`] for advanced queries.
    pub fn raw_map(&self) -> &PointsToMap<'tcx> {
        &self.raw
    }

    /// Returns the points-to set for a given [`Local`] variable as
    /// human-readable [`PointsToTarget`] values.
    ///
    /// If the local is not found in the analysis result, returns an empty vec.
    pub fn points_to_set(&self, local: Local) -> Vec<PointsToTarget> {
        let key = ConstraintNode::Place(Place::from(local).as_ref());
        self.raw
            .get(&key)
            .map(|set| set.iter().map(Self::node_to_target).collect())
            .unwrap_or_default()
    }

    /// Returns a map of every local variable to its points-to set.
    pub fn all_points_to(&self) -> FxHashMap<u32, Vec<PointsToTarget>> {
        let mut result: FxHashMap<u32, Vec<PointsToTarget>> = FxHashMap::default();
        for (node, targets) in &self.raw {
            if let ConstraintNode::Place(p) = node {
                let local_id = p.local.as_u32();
                let targets: Vec<_> = targets.iter().map(Self::node_to_target).collect();
                result.entry(local_id).or_default().extend(targets);
            }
        }
        result
    }

    /// Check whether two local variables may alias (i.e. their points-to sets intersect).
    pub fn may_alias(&self, a: Local, b: Local) -> bool {
        let key_a = ConstraintNode::Place(Place::from(a).as_ref());
        let key_b = ConstraintNode::Place(Place::from(b).as_ref());
        match (self.raw.get(&key_a), self.raw.get(&key_b)) {
            (Some(pts_a), Some(pts_b)) => !pts_a.is_disjoint(pts_b),
            _ => false,
        }
    }

    /// Check whether `pointer` may point to `pointee`.
    pub fn may_point_to(&self, pointer: Local, pointee: Local) -> bool {
        let key = ConstraintNode::Place(Place::from(pointer).as_ref());
        let target_place = ConstraintNode::Place(Place::from(pointee).as_ref());
        let target_alloc = ConstraintNode::Alloc(Place::from(pointee).as_ref());
        match self.raw.get(&key) {
            Some(pts) => pts.contains(&target_place) || pts.contains(&target_alloc),
            None => false,
        }
    }

    /// Return the number of non-empty entries in the points-to map.
    pub fn entry_count(&self) -> usize {
        self.raw.values().filter(|s| !s.is_empty()).count()
    }

    /// Returns `true` if the analysis produced any points-to information.
    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    /// Format a complete human-readable report of all points-to relations.
    pub fn format_report(&self) -> String {
        let mut out = String::new();
        out.push_str("=== Points-To Analysis Report ===\n\n");

        // Collect and sort entries for deterministic output.
        let mut entries: Vec<_> = self.raw.iter().collect();
        entries.sort_by(|(a, _), (b, _)| Self::cmp_nodes(a, b));

        if entries.is_empty() {
            out.push_str("  (no points-to relations found)\n");
        }

        for (node, pointees) in &entries {
            if pointees.is_empty() {
                continue;
            }
            let node_str = format!("{}", node);
            let mut targets: Vec<String> = pointees
                .iter()
                .map(|p| Self::node_to_target(p).to_string())
                .collect();
            targets.sort();
            out.push_str(&format!("  {} -> {{ {} }}\n", node_str, targets.join(", ")));
        }

        out.push_str(&format!(
            "\nTotal entries: {} (non-empty: {})\n",
            self.raw.len(),
            self.entry_count()
        ));
        out.push_str("=== End Report ===\n");
        out
    }

    fn node_to_target(node: &ConstraintNode<'tcx>) -> PointsToTarget {
        match node {
            ConstraintNode::Alloc(p) => PointsToTarget::Alloc {
                local: p.local.as_u32(),
                projection: if p.projection.is_empty() {
                    String::new()
                } else {
                    format!("{:?}", p.projection)
                },
            },
            ConstraintNode::Place(p) => PointsToTarget::Local {
                local: p.local.as_u32(),
                projection: if p.projection.is_empty() {
                    String::new()
                } else {
                    format!("{:?}", p.projection)
                },
            },
            ConstraintNode::Constant(c) => PointsToTarget::Constant(format!("{:?}", c)),
            ConstraintNode::ConstantDeref(c) => PointsToTarget::ConstantDeref(format!("{:?}", c)),
        }
    }

    fn cmp_nodes(a: &ConstraintNode<'_>, b: &ConstraintNode<'_>) -> std::cmp::Ordering {
        // Sort order: Place < Alloc < Constant < ConstantDeref
        fn rank(n: &ConstraintNode<'_>) -> u8 {
            match n {
                ConstraintNode::Place(_) => 0,
                ConstraintNode::Alloc(_) => 1,
                ConstraintNode::Constant(_) => 2,
                ConstraintNode::ConstantDeref(_) => 3,
            }
        }
        let ra = rank(a);
        let rb = rank(b);
        if ra != rb {
            return ra.cmp(&rb);
        }
        // Within the same variant, compare by formatted representation.
        format!("{}", a).cmp(&format!("{}", b))
    }
}

impl<'tcx> fmt::Display for PointsToResult<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format_report())
    }
}

/// Convenience function: run Andersen pointer analysis on a function body.
pub fn analyze_body<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> PointsToResult<'tcx> {
    PointsToResult::analyze(body, tcx)
}
