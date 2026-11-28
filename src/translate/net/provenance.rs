//! Side record of how each original-net transition was lowered from MIR.
//! `NetBuilder::transition` is the only writer of `origins`.

use std::collections::BTreeMap;

use rustc_middle::mir::{Operand, Place, Rvalue, TerminatorKind};
use rustc_middle::ty::TyCtxt;

use super::TransitionId;
use crate::translate::mir_utils::rvalue_read_places;
use crate::util::format_name;

/// Where one original-net transition came from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransOrigin {
    /// Function the transition belongs to, in `format_name` form (the same
    /// string the function's places are named with, e.g.
    /// `crate::f::{closure#0}`).
    pub fn_def_path: String,
    /// Basic-block index inside that function.
    pub bb: usize,
    /// Span in the `{:?}` form the rest of the translation uses.
    pub span: String,
}

/// One definition site of a basic block: a statement assignment or a call
/// destination. `operands` are the root locals the right-hand side reads,
/// i.e. the places a Def-Use chain continues into — unless `stop_recursion`
/// is set (call destinations), where the chain stops and lets the reader
/// follow the recorded span into the callee's source.
#[derive(Clone, Debug)]
pub struct DefRecord {
    pub local: usize,
    pub span: String,
    /// Readable MIR summary of the right-hand side (`discriminant(_2)`,
    /// `call std::vec::Vec::len(_4)`, `const 1_i32`, …).
    pub rhs: String,
    pub operands: Vec<usize>,
    pub stop_recursion: bool,
}

/// The data-dependent branch of a block's terminator, if any.
#[derive(Clone, Debug)]
pub enum GuardFacts {
    /// `SwitchInt`: the discriminant operand and every target, with the
    /// explicit cases as `Some(value)` and the fallback as `None`.
    Switch {
        /// Operand in `Debug` form, e.g. `copy _3`.
        operand: String,
        /// Root local the operand reads, when it reads one.
        operand_local: Option<usize>,
        targets: Vec<(Option<u128>, usize)>,
    },
    /// `Assert`: the condition operand and the block taken when it holds.
    Assert {
        operand: String,
        operand_local: Option<usize>,
        expected: bool,
        target: usize,
    },
}

/// MIR facts of one basic block.
#[derive(Clone, Debug, Default)]
pub struct BbFacts {
    /// Definitions in statement order, followed by the terminator's call
    /// destination (if the terminator is a `Call`).
    pub defs: Vec<DefRecord>,
    pub guard: Option<GuardFacts>,
}

/// One loop-summary transition (`LoopSemantics::Summary`): the cut
/// back edge it re-opens and the transition that implements it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopSummaryFacts {
    /// The cut edge's source block (the transition's origin block).
    pub from_bb: usize,
    /// The cut edge's target block the summary re-enters.
    pub to_bb: usize,
    /// Index into [`TranslationProvenance::origins`], i.e. the original-net
    /// transition id.
    pub transition: usize,
    /// The transition that cuts the edge again once the budget is spent
    /// (`trigger -> structural sink`). It keeps the post-re-entry latch
    /// terminal instead of a fake control deadlock.
    pub fallback_transition: usize,
}

/// MIR facts of one translated function.
#[derive(Clone, Debug, Default)]
pub struct FunctionFacts {
    pub bbs: BTreeMap<usize, BbFacts>,
    /// `(from_bb, to_bb)` edges removed by cycle breaking; empty when
    /// `break_cfg_cycles` is off or the function has no loops.
    pub cut_back_edges: Vec<(usize, usize)>,
    /// The loop-summary transitions emitted for those cut edges (empty under
    /// `loop_semantics = cut`).
    pub loop_summaries: Vec<LoopSummaryFacts>,
    /// Number of arguments; locals `1..=arg_count` are parameters.
    pub arg_count: usize,
    /// Declaration spans of every local (`local -> span`), so a chain that
    /// stops at a parameter or finds no definition on the path can still
    /// point at where the local lives.
    pub locals: BTreeMap<usize, String>,
}

impl FunctionFacts {
    pub fn bb(&self, bb: usize) -> Option<&BbFacts> {
        self.bbs.get(&bb)
    }

    /// Whether `local` is a function argument.
    pub fn is_param(&self, local: usize) -> bool {
        local >= 1 && local <= self.arg_count
    }

    /// The declaration span of `local`.
    pub fn local_span(&self, local: usize) -> Option<&str> {
        self.locals.get(&local).map(String::as_str)
    }
}

/// Provenance of one translation run.
#[derive(Clone, Debug, Default)]
pub struct TranslationProvenance {
    /// One entry per original-net transition, in `TransitionId` order.
    pub origins: Vec<TransOrigin>,
    pub functions: BTreeMap<String, FunctionFacts>,
    /// The transitions that *implement* a block's `SwitchInt`/`Assert` branch
    /// (`fn_def_path -> bb -> transition ids`). A block has several other
    /// transitions (start, statements, cleanup) whose origin shares the bb, so
    /// the path-predicate extractor must key the guard on the transition that
    /// actually fires it, not on the bb alone.
    pub guard_transitions: BTreeMap<String, BTreeMap<usize, Vec<usize>>>,
}

impl TranslationProvenance {
    pub fn origin(&self, transition: TransitionId) -> Option<&TransOrigin> {
        self.origins.get(transition.index())
    }

    pub fn function(&self, fn_def_path: &str) -> Option<&FunctionFacts> {
        self.functions.get(fn_def_path)
    }

    /// Whether `transition` is one of the transitions that realize the guard
    /// of its block (`SwitchInt` target or `Assert` success edge).
    pub fn is_guard_transition(&self, transition: TransitionId) -> bool {
        let Some(origin) = self.origin(transition) else {
            return false;
        };
        self.guard_transitions
            .get(&origin.fn_def_path)
            .and_then(|bbs| bbs.get(&origin.bb))
            .is_some_and(|ids| ids.contains(&transition.index()))
    }

    /// A source span inside `bb`: the span of the first transition recorded
    /// for that block (its start, a statement, or the terminator). Used to
    /// name a `SwitchInt` target's entry point in the predicate report; `None`
    /// when the block produced no transition (empty/unreachable).
    pub fn bb_entry_span(&self, fn_def_path: &str, bb: usize) -> Option<&str> {
        self.origins
            .iter()
            .find(|origin| origin.fn_def_path == fn_def_path && origin.bb == bb)
            .map(|origin| origin.span.as_str())
    }
}

// MIR renderings (faithful, no invented type information) ───────────────

/// `Debug`-form operand (`copy _3`, `move _1.0`, `const 1_i32`).
pub fn operand_summary(operand: &Operand<'_>) -> String {
    format!("{operand:?}")
}

/// Root locals read by a set of places, in order, duplicates removed.
pub fn root_locals<'a, 'tcx>(places: impl IntoIterator<Item = &'a Place<'tcx>>) -> Vec<usize>
where
    'tcx: 'a,
{
    let mut locals = Vec::new();
    for place in places {
        let local = place.local.index();
        if !locals.contains(&local) {
            locals.push(local);
        }
    }
    locals
}

/// A compact, faithful summary of an assignment's right-hand side.
pub fn rvalue_summary(rvalue: &Rvalue<'_>) -> String {
    match rvalue {
        Rvalue::Use(operand, _) => operand_summary(operand),
        Rvalue::Repeat(operand, _) => format!("[{}; _]", operand_summary(operand)),
        Rvalue::Ref(_, kind, place) => format!("&{kind:?} {place:?}"),
        Rvalue::RawPtr(_, place) => format!("raw_ptr {place:?}"),
        Rvalue::Cast(_, operand, ty) => format!("{} as {ty:?}", operand_summary(operand)),
        Rvalue::BinaryOp(op, operands) => {
            let (left, right) = &**operands;
            format!(
                "{} {op:?} {}",
                operand_summary(left),
                operand_summary(right)
            )
        }
        Rvalue::UnaryOp(op, operand) => format!("{op:?} {}", operand_summary(operand)),
        Rvalue::Aggregate(_, operands) => {
            let items: Vec<String> = operands.iter().map(operand_summary).collect();
            format!("aggregate({})", items.join(", "))
        }
        Rvalue::Discriminant(place) => format!("discriminant({place:?})"),
        Rvalue::CopyForDeref(place) => format!("copy_for_deref({place:?})"),
        Rvalue::Reborrow(_, mutability, place) => {
            format!("reborrow({mutability:?} {place:?})")
        }
        Rvalue::ThreadLocalRef(def_id) => {
            format!("thread_local_ref({})", format_name(*def_id))
        }
        Rvalue::WrapUnsafeBinder(operand, _) => operand_summary(operand),
    }
}

/// A compact summary of a call terminator (`call std::vec::Vec::len(_4)`).
pub fn call_summary<'tcx>(
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    body: &rustc_middle::mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> String {
    let callee = match func.ty(body, tcx).kind() {
        rustc_middle::ty::TyKind::FnDef(def_id, _)
        | rustc_middle::ty::TyKind::Closure(def_id, _) => format_name(*def_id),
        _ => operand_summary(func),
    };
    let args: Vec<String> = args.iter().map(|arg| operand_summary(&arg.node)).collect();
    format!("call {callee}({})", args.join(", "))
}

/// The root locals read by a `SwitchInt`/`Assert` operand.
pub fn operand_root_local(operand: &Operand<'_>) -> Option<usize> {
    operand.place().map(|place| place.local.index())
}

/// Whether a terminator is a `SwitchInt`/`Assert` guard.
pub fn is_guard_terminator(kind: &TerminatorKind<'_>) -> bool {
    matches!(
        kind,
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. }
    )
}

/// The locals read by an assignment or call right-hand side, for the
/// Def-Use chain recursion.
pub fn def_operands(rvalue: &Rvalue<'_>) -> Vec<usize> {
    root_locals(rvalue_read_places(rvalue))
}
