use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, Statement, Terminator, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use std::fmt::Write;
use std::fs;
use std::path::Path;

pub fn write_mir_dot<'tcx, P: AsRef<Path>>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
    path: P,
) -> std::io::Result<()> {
    if let Some(parent) = path.as_ref().parent() {
        fs::create_dir_all(parent)?;
    }

    let dot = generate_mir_dot(tcx, def_id, body);
    fs::write(path, dot)?;
    Ok(())
}

/// Emit a Graphviz DOT representation of MIR.
fn generate_mir_dot<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, body: &Body<'tcx>) -> String {
    let fn_name = tcx.def_path_str(def_id);
    let mut dot = String::new();

    let _ = writeln!(&mut dot, "digraph MIR_{} {{", sanitize_name(&fn_name));
    let _ = writeln!(&mut dot, "    rankdir=TB;");
    let _ = writeln!(&mut dot, "    node [fontname=\"Helvetica\", fontsize=10];");
    let _ = writeln!(&mut dot, "    edge [fontname=\"Helvetica\", fontsize=9];");

    // Emit basic-block nodes.
    for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
        if bb.is_cleanup || bb.is_empty_unreachable() {
            continue;
        }

        let node_id = format!("bb{}", bb_idx.index());
        let mut label = format!("BB{}", bb_idx.index());

        if !bb.statements.is_empty() {
            label.push_str("\\n");
            for (idx, stmt) in bb.statements.iter().enumerate() {
                let stmt_str = format_statement(stmt);
                if idx < 3 {
                    label.push_str(&format!("{}\\n", escape_label(&stmt_str)));
                } else if idx == 3 {
                    label.push_str("...\\n");
                    break;
                }
            }
        }

        if let Some(term) = &bb.terminator {
            label.push_str(&format!("\\n---\\n{}", format_terminator(term)));
        }

        let shape = if bb_idx.index() == 0 {
            "ellipse"
        } else {
            "box"
        };

        let fillcolor = if bb.is_cleanup { "#ffcccc" } else { "#e3f2fd" };

        let _ = writeln!(
            &mut dot,
            "    {} [label=\"{}\", shape={}, style=filled, fillcolor=\"{}\"];",
            node_id,
            escape_label(&label),
            shape,
            fillcolor
        );
    }

    for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
        if bb.is_cleanup || bb.is_empty_unreachable() {
            continue;
        }

        let from_id = format!("bb{}", bb_idx.index());

        if let Some(term) = &bb.terminator {
            match &term.kind {
                TerminatorKind::Goto { target } => {
                    let to_id = format!("bb{}", target.index());
                    let _ = writeln!(&mut dot, "    {} -> {};", from_id, to_id);
                }
                TerminatorKind::SwitchInt { targets, .. } => {
                    for (value, target) in targets.iter() {
                        let to_id = format!("bb{}", target.index());
                        let label = format!("{:?}", value);
                        let _ = writeln!(
                            &mut dot,
                            "    {} -> {} [label=\"{}\"];",
                            from_id,
                            to_id,
                            escape_label(&label)
                        );
                    }
                }
                TerminatorKind::Call { target, .. } => {
                    if let Some(target_bb) = target {
                        let to_id = format!("bb{}", target_bb.index());
                        let _ =
                            writeln!(&mut dot, "    {} -> {} [label=\"call\"];", from_id, to_id);
                    }
                }
                TerminatorKind::Return => {
                    let _ = writeln!(&mut dot, "    {} -> return [label=\"return\"];", from_id);
                }
                TerminatorKind::Assert { target, .. } => {
                    let to_id = format!("bb{}", target.index());
                    let _ = writeln!(&mut dot, "    {} -> {} [label=\"assert\"];", from_id, to_id);
                }
                _ => {
                    let _ = writeln!(
                        &mut dot,
                        "    {} -> end_{} [label=\"{:?}\"];",
                        from_id,
                        bb_idx.index(),
                        term.kind
                    );
                }
            }
        }
    }

    let _ = writeln!(&mut dot, "}}");
    dot
}

fn format_statement(stmt: &Statement<'_>) -> String {
    match &stmt.kind {
        rustc_middle::mir::StatementKind::Assign(box (place, rvalue)) => {
            format!("{:?} = {:?}", place, rvalue)
        }
        rustc_middle::mir::StatementKind::FakeRead(..) => "FakeRead".to_string(),
        rustc_middle::mir::StatementKind::SetDiscriminant { .. } => "SetDiscriminant".to_string(),
        rustc_middle::mir::StatementKind::StorageLive(..) => "StorageLive".to_string(),
        rustc_middle::mir::StatementKind::StorageDead(..) => "StorageDead".to_string(),
        // rustc_middle::mir::StatementKind::Retag(.., _) => "Retag".to_string(),
        rustc_middle::mir::StatementKind::PlaceMention(..) => "PlaceMention".to_string(),
        rustc_middle::mir::StatementKind::AscribeUserType(..) => "AscribeUserType".to_string(),
        rustc_middle::mir::StatementKind::Coverage(..) => "Coverage".to_string(),
        rustc_middle::mir::StatementKind::Intrinsic(..) => "Intrinsic".to_string(),
        rustc_middle::mir::StatementKind::ConstEvalCounter => "ConstEvalCounter".to_string(),
        rustc_middle::mir::StatementKind::Nop => "Nop".to_string(),
        _ => format!("{:?}", stmt.kind),
    }
}

fn format_terminator(term: &Terminator<'_>) -> String {
    match &term.kind {
        TerminatorKind::Goto { target } => format!("goto BB{}", target.index()),
        TerminatorKind::SwitchInt { targets, .. } => {
            format!("switch ({} targets)", targets.all_targets().len())
        }
        TerminatorKind::Call { .. } => "call".to_string(),
        TerminatorKind::Return => "return".to_string(),
        TerminatorKind::Assert { .. } => "assert".to_string(),
        TerminatorKind::Drop { .. } => "drop".to_string(),
        TerminatorKind::Unreachable => "unreachable".to_string(),
        _ => format!("{:?}", term.kind),
    }
}

fn escape_label(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "")
        .replace('{', "\\{")
        .replace('}', "\\}")
        .replace('<', "\\<")
        .replace('>', "\\>")
}

fn sanitize_name(name: &str) -> String {
    name.replace('-', "_")
        .replace(':', "_")
        .replace('.', "_")
        .replace('/', "_")
        .replace(' ', "_")
}
