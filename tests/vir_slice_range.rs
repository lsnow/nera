#[path = "support/slice_program.rs"]
mod slice_program;

use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64MachineInstruction};
use nera::{
    ObligationStatus, ResourceObligationKind, SpannedVirInstruction, VirConstant,
    VirExecutionErrorKind, VirFunctionId, VirIndexBounds, VirInstruction, VirRuntimeValue, VirType,
    VirUnit, VirValue, VirValueId, analyze_function_cfg, interpret,
};

fn rebuild_runtime(unit: VirUnit) -> VirUnit {
    VirUnit::from_runtime(unit.memory, unit.runtime.entry, unit.runtime.functions)
}

#[test]
fn array_to_slice_subslice_and_index_reach_every_runtime_consumer() {
    let validated = slice_program::validated();
    assert!(validated.stable_dump().contains("slice.range"));
    assert!(validated.stable_dump().contains("bounds slice(%17)"));
    let resolved = validated.resolve().expect("slice fixture resolves");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("slice range analysis converges");
    assert!(
        analysis.all_obligations_proven(),
        "{:?}",
        analysis.obligations()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("slice fixture executes")
            .values(),
        &[VirRuntimeValue::U64(40)]
    );

    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("slice fixture lowers natively");
    let instructions = machine
        .function(VirFunctionId::new(0))
        .expect("slice entry machine function")
        .blocks()
        .iter()
        .flat_map(|block| block.instructions())
        .collect::<Vec<_>>();
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction, X86_64MachineInstruction::Subtract64 { .. }))
    );
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction, X86_64MachineInstruction::Multiply64 { .. }))
    );
}

#[test]
fn empty_one_past_slice_is_valid_but_reversed_and_oob_ranges_are_refuted() {
    let empty = slice_program::one_range_unit(4, 4)
        .into_validated()
        .expect("one-past empty slice is structurally valid");
    let empty = empty.resolve().expect("empty slice resolves");
    assert!(
        analyze_function_cfg(&empty, VirFunctionId::new(0))
            .expect("empty slice analysis")
            .all_obligations_proven()
    );
    assert_eq!(
        interpret(empty.runtime())
            .expect("empty one-past slice executes")
            .values(),
        &[VirRuntimeValue::U64(0)]
    );

    for (start, end, expected_kind) in [(3, 2, "ordered"), (1, 5, "bounded")] {
        let validated = slice_program::one_range_unit(start, end)
            .into_validated()
            .expect("range condition belongs to verification");
        let resolved = validated.resolve().expect("invalid range fixture resolves");
        let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
            .expect("invalid range analysis converges");
        assert!(analysis.obligations().iter().any(|record| {
            record.obligation().status() == ObligationStatus::Refuted
                && matches!(
                    (expected_kind, record.obligation().kind()),
                    ("ordered", ResourceObligationKind::SliceRangeOrdered { .. })
                        | (
                            "bounded",
                            ResourceObligationKind::SliceRangeWithinBounds { .. }
                        )
                )
        }));
        assert!(matches!(
            interpret(resolved.runtime())
                .expect_err("invalid range cannot execute")
                .kind(),
            VirExecutionErrorKind::InvalidSliceRange { .. }
        ));
    }

    let mut index_oob = slice_program::full_unit();
    let index = index_oob.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .find_map(|instruction| match &mut instruction.instruction {
            VirInstruction::Constant { result, value } if result.id == VirValueId::new(24) => {
                Some(value)
            }
            _ => None,
        })
        .expect("slice index constant");
    *index = VirConstant::U64(2);
    let index_oob = index_oob
        .into_validated()
        .expect("slice index bounds are a verifier condition");
    let index_oob = index_oob.resolve().expect("slice index fixture resolves");
    let analysis = analyze_function_cfg(&index_oob, VirFunctionId::new(0))
        .expect("slice index analysis converges");
    assert!(analysis.obligations().iter().any(|record| matches!(
        record.obligation().kind(),
        ResourceObligationKind::SliceIndexWithinBounds { .. }
    ) && record.obligation().status()
        == ObligationStatus::Refuted));
    assert_eq!(
        interpret(index_oob.runtime())
            .expect_err("one-past slice index cannot execute")
            .kind(),
        &VirExecutionErrorKind::IndexOutOfBounds {
            index: 2,
            length: 2,
        }
    );
}

#[test]
fn forged_permission_and_length_overflow_fail_closed() {
    let mut forged = slice_program::one_range_unit(0, 1);
    let forged_span = forged.runtime.functions[0].source_span;
    forged.runtime.functions[0].blocks[0].instructions.insert(
        1,
        SpannedVirInstruction {
            instruction: VirInstruction::LocalStorage {
                pointer_result: VirValue {
                    id: VirValueId::new(30),
                    ty: VirType::Pointer {
                        access: slice_program::ARRAY_ACCESS,
                    },
                },
                permission_result: VirValue {
                    id: VirValueId::new(31),
                    ty: VirType::Permission,
                },
                access: slice_program::ARRAY_ACCESS,
            },
            source_span: forged_span,
        },
    );
    let range = forged.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .find_map(|instruction| match &mut instruction.instruction {
            VirInstruction::SliceRange { permission, .. } => Some(permission),
            _ => None,
        })
        .expect("range instruction");
    *range = VirValueId::new(31);
    let forged = rebuild_runtime(forged)
        .into_validated()
        .expect("allocation mismatch is not structural");
    let forged = forged.resolve().expect("forged fixture resolves");
    let analysis =
        analyze_function_cfg(&forged, VirFunctionId::new(0)).expect("forged permission analysis");
    assert!(analysis.obligations().iter().any(|record| matches!(
        record.obligation().kind(),
        ResourceObligationKind::PermissionMatchesAllocation { .. }
    ) && record.obligation().status()
        == ObligationStatus::Refuted));
    assert!(matches!(
        interpret(forged.runtime())
            .expect_err("foreign permission cannot create a slice")
            .kind(),
        VirExecutionErrorKind::PermissionMismatch { .. }
    ));

    let mut overflow = slice_program::one_range_unit(0, u64::MAX);
    let span = overflow.runtime.functions[0].source_span;
    let instructions = &mut overflow.runtime.functions[0].blocks[0].instructions;
    let range_position = instructions
        .iter()
        .position(|instruction| {
            matches!(instruction.instruction, VirInstruction::SliceRange { .. })
        })
        .expect("range instruction");
    instructions.insert(
        range_position,
        SpannedVirInstruction {
            instruction: VirInstruction::Constant {
                result: VirValue {
                    id: VirValueId::new(30),
                    ty: VirType::U64,
                },
                value: VirConstant::U64(u64::MAX),
            },
            source_span: span,
        },
    );
    let VirInstruction::SliceRange {
        base,
        source,
        bounds,
        ..
    } = &mut instructions[range_position + 1].instruction
    else {
        unreachable!("range retained after insertion")
    };
    *base = VirValueId::new(3);
    *source = slice_program::SLICE_ACCESS;
    *bounds = VirIndexBounds::Slice {
        length: VirValueId::new(30),
    };
    let overflow = rebuild_runtime(overflow)
        .into_validated()
        .expect("dynamic extent overflow is a verifier condition");
    let overflow = overflow.resolve().expect("overflow fixture resolves");
    let analysis = analyze_function_cfg(&overflow, VirFunctionId::new(0))
        .expect("overflow analysis converges");
    assert!(analysis.obligations().iter().any(|record| matches!(
        record.obligation().kind(),
        ResourceObligationKind::SliceRangeStrideNoOverflow { .. }
    ) && record.obligation().status()
        == ObligationStatus::Refuted));
    assert_eq!(
        interpret(overflow.runtime())
            .expect_err("slice extent multiplication must not wrap")
            .kind(),
        &VirExecutionErrorKind::AddressCalculationOverflow
    );
}

#[test]
fn consumed_parent_permission_cannot_be_reused_as_an_implicit_reborrow() {
    let mut duplicated = slice_program::full_unit();
    let permission = duplicated.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .filter_map(|instruction| match &mut instruction.instruction {
            VirInstruction::SliceRange { permission, .. } => Some(permission),
            _ => None,
        })
        .nth(1)
        .expect("subslice range");
    *permission = VirValueId::new(1);

    let duplicated = duplicated
        .into_validated()
        .expect("permission availability belongs to resource verification");
    let duplicated = duplicated.resolve().expect("reborrow mutation resolves");
    let analysis = analyze_function_cfg(&duplicated, VirFunctionId::new(0))
        .expect("reborrow mutation analysis converges");
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::PermissionAvailable { permission }
                if permission == VirValueId::new(1)
        ) && record.obligation().status() == ObligationStatus::Refuted
    }));
    assert_eq!(
        interpret(duplicated.runtime())
            .expect_err("a consumed parent permission cannot be reused")
            .kind(),
        &VirExecutionErrorKind::PermissionAlreadyConsumed(VirValueId::new(1))
    );
}

#[test]
fn validator_rechecks_slice_shape_and_result_expansion() {
    let mut wrong_result = slice_program::full_unit();
    let range = wrong_result.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .find_map(|instruction| match &mut instruction.instruction {
            VirInstruction::SliceRange { length_result, .. } => Some(length_result),
            _ => None,
        })
        .expect("slice range");
    range.ty = VirType::Bool;
    assert!(wrong_result.into_validated().is_err());

    let mut wrong_shape = slice_program::full_unit();
    let range = wrong_shape.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .find_map(|instruction| match &mut instruction.instruction {
            VirInstruction::SliceRange { slice, .. } => Some(slice),
            _ => None,
        })
        .expect("slice range");
    *range = slice_program::ARRAY_ACCESS;
    assert!(wrong_shape.into_validated().is_err());
}
