//! Checked Spec terms over the existing two-cut raw arena; no runtime changes.
use super::spec_arena as arena;
use nera::*;

pub fn unit(stride: u64) -> VirUnit {
    let mut unit = arena::unit(1, 3, arena::Mutation::None);
    let function = VirFunctionId::new(1);
    let location = VirSpecLocation::FunctionEntry { function };
    let origin = unit
        .source_map
        .origin_at(VirLocation::FunctionEntry { function })
        .unwrap()
        .id;
    let clause = VirSpecClauseId::new(unit.specs.clauses().len() as u32);
    let id = VirSpecTermId::new;
    for (index, (ty, kind)) in [
        (
            VirSpecType::U64,
            VirSpecTermKind::Snapshot(VirSpecSnapshot::Parameter { function, slot: 0 }),
        ),
        (
            VirSpecType::U64,
            VirSpecTermKind::Snapshot(VirSpecSnapshot::Parameter { function, slot: 1 }),
        ),
        (
            VirSpecType::U64,
            VirSpecTermKind::CheckedScale {
                operand: id(0),
                stride,
            },
        ),
        (
            VirSpecType::U64,
            VirSpecTermKind::CheckedScale {
                operand: id(1),
                stride,
            },
        ),
        (VirSpecType::U64, VirSpecTermKind::U64(0)),
        (VirSpecType::U64, VirSpecTermKind::U64(48)),
        (VirSpecType::U64, VirSpecTermKind::U64(8)),
        (
            VirSpecType::U64,
            VirSpecTermKind::CheckedAdd {
                left: id(2),
                right: id(6),
            },
        ),
        (
            VirSpecType::U64,
            VirSpecTermKind::CheckedSub {
                left: id(3),
                right: id(2),
            },
        ),
        (
            VirSpecType::Bool,
            VirSpecTermKind::LessOrEqual {
                left: id(8),
                right: id(5),
            },
        ),
        (
            VirSpecType::Bool,
            VirSpecTermKind::RangeContains {
                outer_start: id(4),
                outer_end: id(5),
                inner_start: id(2),
                inner_end: id(3),
            },
        ),
        (
            VirSpecType::Bool,
            VirSpecTermKind::RangeDisjoint {
                left_start: id(4),
                left_end: id(7),
                right_start: id(3),
                right_end: id(5),
            },
        ),
        (
            VirSpecType::Bool,
            VirSpecTermKind::And(vec![id(9), id(10), id(11)]),
        ),
    ]
    .into_iter()
    .enumerate()
    {
        unit.specs.terms_mut().push(VirSpecTerm {
            id: id(index as u32),
            clause,
            ty,
            kind,
            origin,
        });
    }
    unit.specs.clauses_mut().push(VirSpecClause {
        id: clause,
        owner: VirSpecClauseOwner::Prove(VirSpecProveId::new(0)),
        location,
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic { root: id(12) },
    });
    unit.specs.proves_mut().push(VirSpecProve {
        id: VirSpecProveId::new(0),
        function,
        location,
        clause,
        origin,
    });
    unit
}
