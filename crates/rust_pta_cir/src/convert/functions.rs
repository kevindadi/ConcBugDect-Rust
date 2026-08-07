//! Build CIR function bodies from Petri-net structure.

use rust_petri_net_analysis::net::Net;
use rust_petri_net_analysis::net::structure::PlaceType;

use crate::ast::{FnKind, Function, Op, Statement, Transfer};
use crate::convert::ops::transition_to_op;
use crate::convert::resources::concurrency_transition_ids;

/// Discover function entry/end place pairs from the net.
pub fn discover_functions(net: &Net) -> Vec<(String, bool)> {
    let mut functions = Vec::new();
    for place in net.places.iter() {
        if place.place_type != PlaceType::FunctionStart {
            continue;
        }
        if let Some(name) = place.name.strip_suffix("_start") {
            let is_main = name.contains("main") || name.ends_with("::main");
            functions.push((name.to_string(), is_main));
        }
    }
    functions.sort_by(|a, b| a.0.cmp(&b.0));
    functions
}

pub fn build_functions(net: &Net, entry: &str) -> Vec<Function> {
    let tids = concurrency_transition_ids(net);
    discover_functions(net)
        .into_iter()
        .map(|(name, is_main)| {
            let kind = if is_main || name == entry {
                FnKind::Normal
            } else if name.contains("closure") || name.contains("{closure") {
                FnKind::Closure
            } else {
                FnKind::Closure
            };
            let body = build_stub_body(net, &tids, &name);
            Function { name, kind, body }
        })
        .collect()
}

fn build_stub_body(
    net: &Net,
    tids: &[rust_petri_net_analysis::net::ids::TransitionId],
    fn_name: &str,
) -> Vec<Statement> {
    let mut stmts = Vec::new();
    let mut sid = 1u32;

    for tid in tids {
        let transition = &net.transitions[*tid];
        if !transition.name.contains(fn_name)
            && !matches!(
                transition.transition_type,
                rust_petri_net_analysis::net::structure::TransitionType::Spawn(_)
                    | rust_petri_net_analysis::net::structure::TransitionType::Join(_)
            )
        {
            continue;
        }
        let op = transition_to_op(&transition.transition_type, &transition.name);
        if matches!(op, Op::Nop) {
            continue;
        }
        let current = Statement::format_sid(sid);
        let next = Statement::format_sid(sid + 1);
        let transfer = if matches!(op, Op::Return) {
            Transfer::Return
        } else {
            Transfer::Next(next)
        };
        stmts.push(Statement::new(current, op, transfer));
        sid += 1;
    }

    if stmts.is_empty() {
        stmts.push(Statement::new(
            Statement::format_sid(1),
            Op::Nop,
            Transfer::Return,
        ));
    } else if !matches!(stmts.last().unwrap().op, Op::Return) {
        let last_sid = Statement::format_sid(sid);
        stmts.push(Statement::new(last_sid, Op::Return, Transfer::Return));
    }

    stmts
}
