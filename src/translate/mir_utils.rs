use rustc_middle::mir::{Operand, Place, Rvalue};

pub fn operand_place<'a, 'tcx>(operand: &'a Operand<'tcx>) -> Option<&'a Place<'tcx>> {
    match operand {
        Operand::Move(place) | Operand::Copy(place) => Some(place),
        _ => None,
    }
}

pub fn rvalue_read_places<'a, 'tcx>(rvalue: &'a Rvalue<'tcx>) -> Vec<&'a Place<'tcx>> {
    match rvalue {
        Rvalue::Use(operand, _)
        | Rvalue::Repeat(operand, _)
        | Rvalue::Cast(_, operand, _)
        | Rvalue::UnaryOp(_, operand) => operand_place(operand).into_iter().collect(),
        Rvalue::BinaryOp(_, box (left, right)) => [operand_place(left), operand_place(right)]
            .into_iter()
            .flatten()
            .collect(),
        Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::CopyForDeref(place) => vec![place],
        Rvalue::Aggregate(_, operands) => operands.iter().filter_map(operand_place).collect(),
        _ => Vec::new(),
    }
}
