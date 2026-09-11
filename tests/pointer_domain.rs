#[path = "support/frontend_checks.rs"]
mod frontend_checks;
#[path = "support/slice_program.rs"]
mod slice_program;

use nera::{
    CfgAnalysisConfig, ObligationStatus, ResourceObligationKind, SourceFile, VirExecutionErrorKind,
    VirInstruction, VirType, VirValue, VirValueId, analyze, interpret, verify_program,
};

const SOURCE: &str = include_str!("../spec/cases/verify/pointer-domain.nera");

#[test]
fn empty_views_allow_zero_offset_but_not_expansion_or_typed_projection() {
    for (at, delta, project, accepted) in [
        (2, 0, false, true),
        (4, 0, false, true),
        (2, 1, false, false),
        (2, 0, true, false),
    ] {
        let mut unit = slice_program::one_range_unit(at, at);
        let body = &mut unit.runtime.functions[0].blocks[0];
        let span = body.source_span;
        body.instructions.extend([
            nera::SpannedVirInstruction {
                source_span: span,
                instruction: VirInstruction::Constant {
                    result: VirValue {
                        id: VirValueId::new(30),
                        ty: VirType::U64,
                    },
                    value: nera::VirConstant::U64(delta),
                },
            },
            nera::SpannedVirInstruction {
                source_span: span,
                instruction: VirInstruction::PointerOffset {
                    result: VirValue {
                        id: VirValueId::new(31),
                        ty: VirType::Pointer {
                            access: slice_program::U64_ACCESS,
                        },
                    },
                    base: VirValueId::new(16),
                    delta_bytes: VirValueId::new(30),
                },
            },
        ]);
        if project {
            body.instructions.push(nera::SpannedVirInstruction {
                source_span: span,
                instruction: VirInstruction::ObjectLeafAddress {
                    result: VirValue {
                        id: VirValueId::new(32),
                        ty: VirType::Pointer {
                            access: slice_program::U64_ACCESS,
                        },
                    },
                    base: VirValueId::new(31),
                    owner: slice_program::U64_ACCESS,
                    leaf: slice_program::U64_ACCESS,
                    offset_bytes: 0,
                },
            });
        }
        unit.rebuild_source_map_from_runtime("empty-domain.nera", 1);
        let validated = unit.into_validated().unwrap();
        let resolved = validated.resolve().unwrap();
        let transfer = nera::transfer_instruction_sequence_with_memory(
            &nera::ResourceState::new(),
            &resolved.runtime().functions[0].blocks[0].instructions,
            resolved.runtime().memory,
        )
        .unwrap();
        assert_eq!(
            transfer.all_obligations_proven(),
            accepted,
            "{at}/{delta}/{project}: {:?}",
            transfer.obligations()
        );
        if accepted {
            assert_eq!(
                interpret(resolved.runtime()).unwrap().values(),
                [nera::VirRuntimeValue::U64(0)]
            );
        } else {
            assert!(matches!(
                interpret(resolved.runtime()).unwrap_err().kind(),
                VirExecutionErrorKind::PointerDomainViolation { .. }
            ));
        }
    }
}

#[test]
fn forged_dynamic_slice_extent_cannot_overflow_the_stride_calculation() {
    let mut unit = slice_program::full_unit();
    let body = &mut unit.runtime.functions[0].blocks[0];
    let index = body
        .instructions
        .iter()
        .position(|i| {
            matches!(
                i.instruction,
                VirInstruction::SliceRange {
                    bounds: nera::VirIndexBounds::Slice { .. },
                    ..
                }
            )
        })
        .unwrap();
    let VirInstruction::SliceRange { bounds, .. } = &mut body.instructions[index].instruction
    else {
        unreachable!()
    };
    *bounds = nera::VirIndexBounds::Slice {
        length: VirValueId::new(30),
    };
    body.instructions.insert(
        index,
        nera::SpannedVirInstruction {
            source_span: body.source_span,
            instruction: VirInstruction::Constant {
                result: VirValue {
                    id: VirValueId::new(30),
                    ty: VirType::U64,
                },
                value: nera::VirConstant::U64(u64::MAX),
            },
        },
    );
    unit.rebuild_source_map_from_runtime("stride-overflow.nera", 1);
    let validated = unit.into_validated().unwrap();
    let resolved = validated.resolve().unwrap();
    let transfer = nera::transfer_instruction_sequence_with_memory(
        &nera::ResourceState::new(),
        &resolved.runtime().functions[0].blocks[0].instructions,
        resolved.runtime().memory,
    )
    .unwrap();
    assert!(transfer.obligations().iter().any(|o| matches!(
        o.kind(),
        ResourceObligationKind::SliceRangeStrideNoOverflow { .. }
    ) && o.status() == ObligationStatus::Refuted));
    assert!(matches!(
        interpret(resolved.runtime()).unwrap_err().kind(),
        VirExecutionErrorKind::AddressCalculationOverflow
    ));
}

#[test]
fn incompatible_domain_join_stays_unknown_instead_of_restoring_allocation_extent() {
    let unit = slice_program::one_range_unit(1, 2)
        .into_validated()
        .unwrap();
    let runtime = unit.runtime();
    let transfer = nera::transfer_instruction_sequence_with_memory(
        &nera::ResourceState::new(),
        &runtime.functions[0].blocks[0].instructions,
        runtime.memory,
    )
    .unwrap();
    let nera::AbstractValue::Pointer(pointer) =
        *transfer.state().value(VirValueId::new(16)).unwrap()
    else {
        unreachable!()
    };
    assert_eq!(pointer.join(pointer).domain(), pointer.domain());
    let joined = pointer.join(pointer.with_domain(nera::VirPointerDomain::Allocation));
    assert_eq!(joined.domain(), nera::VirPointerDomain::Unknown);
    let mut state = transfer.state().clone();
    state
        .define_value(VirValueId::new(30), nera::AbstractValue::Pointer(joined))
        .unwrap();
    state
        .define_value(
            VirValueId::new(31),
            nera::AbstractValue::U64(nera::U64Interval::exact(0)),
        )
        .unwrap();
    let step = nera::SpannedVirInstruction {
        source_span: runtime.functions[0].source_span,
        instruction: VirInstruction::PointerOffset {
            result: VirValue {
                id: VirValueId::new(32),
                ty: VirType::Pointer {
                    access: slice_program::U64_ACCESS,
                },
            },
            base: VirValueId::new(30),
            delta_bytes: VirValueId::new(31),
        },
    };
    let output =
        nera::transfer_instruction_sequence_with_memory(&state, &[step], runtime.memory).unwrap();
    assert!(!output.all_obligations_proven());
    let nera::AbstractValue::Pointer(result) = *output.state().value(VirValueId::new(32)).unwrap()
    else {
        unreachable!()
    };
    assert_eq!(result.domain(), nera::VirPointerDomain::Unknown);
}

#[test]
fn current_unit_cannot_claim_the_old_allocation_wide_semantic_profile() {
    let output = frontend_checks::accepted("domain-profile.nera", SOURCE);
    let mut unit = output.vir().unwrap().as_unit().clone();
    unit.runtime.semantic_profile = nera::VIR_SYSTEM_SEMANTICS_V1;
    assert!(matches!(
        unit.into_validated().unwrap_err().kind(),
        nera::VirValidationErrorKind::SemanticProfileMismatch { .. }
    ));
}

#[test]
fn arithmetic_endpoints_and_unaligned_addresses_do_not_read_or_mint_authority() {
    frontend_checks::checked("pointer-domain.nera", SOURCE, 42);
    for source in [
        "fn main() -> u64 { let mut b: bool; let p = &raw mut b; let end = p + 1; b = true; return 42; }",
        "fn main() -> u64 { let a = [[10,20],[30,40]]; let p = &raw a[0][0]; let end = p + 16; return 42; }",
        "fn main() -> u64 { let p = alloc<u64>(2); let q = p + 8; *q = 42; let value = *q; free(p); return value; }",
    ] {
        frontend_checks::checked("domain-positive.nera", source, 42);
    }
}

#[test]
fn offset_cannot_escape_a_field_row_or_selected_slice() {
    for source in [
        "struct Pair { x: u64, y: u64, } fn main() -> u64 { let a = Pair { x: 20, y: 22 }; let p = &raw a.x; let q = p + 9; return 42; }",
        "fn main() -> u64 { let a = [[10,20],[30,40]]; let p = &raw a[0][0]; let q = p + 24; return 42; }",
        "fn main() -> u64 { let a = [10,20,30,40]; let v = &a[1..2]; let p = &raw v[0]; let q = p + 9; return 42; }",
    ] {
        let output = frontend_checks::accepted("domain-escape.nera", source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(!verification.is_memory_checked_core0());
        assert!(
            verification
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .any(|o| matches!(
                    o.obligation().kind(),
                    ResourceObligationKind::PointerDomainContains { .. }
                ) && o.obligation().status() == ObligationStatus::Refuted),
            "{:?}",
            verification.diagnostics()
        );
        assert!(matches!(
            interpret(resolved.runtime()).unwrap_err().kind(),
            VirExecutionErrorKind::PointerDomainViolation { .. }
        ));
    }
}

#[test]
fn dead_instance_and_addition_overflow_are_not_hidden_by_an_endpoint() {
    for source in [
        "fn main() -> u64 { let p = alloc<u64>(1); let address = &raw *p; free(p); let end = address + 0; return 42; }",
        "fn main() -> u64 { let x=42; let p=&raw x; let end=p+8; let overflow=end+18446744073709551615; return 42; }",
    ] {
        let output = frontend_checks::accepted("domain-dead.nera", source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        assert!(
            !verify_program(&resolved, CfgAnalysisConfig::default())
                .unwrap()
                .is_memory_checked_core0()
        );
        assert!(matches!(
            interpret(resolved.runtime()).unwrap_err().kind(),
            VirExecutionErrorKind::UseAfterFree { .. }
                | VirExecutionErrorKind::PointerOffsetOutOfBounds { .. }
        ));
    }
}

#[test]
fn one_past_field_cannot_be_read_even_with_whole_allocation_authority() {
    let source = "struct Pair { x: u64, y: u64, } fn main() -> u64 { let a=Pair { x:20, y:22 }; let p=&raw a.x; let end=p+8; return 42; }";
    let output = frontend_checks::accepted("endpoint-load.nera", source);
    let mut unit = output.vir().unwrap().as_unit().clone();
    let body = &mut unit.runtime.functions[0].blocks[0];
    let (permission, access) = body
        .instructions
        .iter()
        .find_map(|i| match i.instruction {
            VirInstruction::RawAddress {
                source_permission,
                result:
                    VirValue {
                        ty: VirType::Pointer { access },
                        ..
                    },
                ..
            } => Some((source_permission, access)),
            _ => None,
        })
        .unwrap();
    let index = body
        .instructions
        .iter()
        .position(|i| matches!(i.instruction, VirInstruction::PointerOffset { .. }))
        .unwrap();
    let VirInstruction::PointerOffset { result, .. } = body.instructions[index].instruction else {
        unreachable!()
    };
    body.instructions.insert(
        index + 1,
        nera::SpannedVirInstruction {
            source_span: body.instructions[index].source_span,
            instruction: VirInstruction::Load {
                result: VirValue {
                    id: VirValueId::new(10000),
                    ty: VirType::U64,
                },
                pointer: result.id,
                permission,
                access,
            },
        },
    );
    unit.rebuild_source_map_from_runtime("endpoint-load.nera", source.len());
    unit.rebuild_implicit_contracts_from_runtime();
    let validated = unit.into_validated().unwrap();
    let resolved = validated.resolve().unwrap();
    assert!(
        !verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert!(matches!(
        interpret(resolved.runtime()).unwrap_err().kind(),
        VirExecutionErrorKind::PointerDomainViolation {
            start_bytes: 8,
            end_bytes: 16,
            ..
        }
    ));
}

#[test]
fn raw_offsets_preserve_readonly_and_do_not_recover_references() {
    for (body, diagnostic) in [
        (
            "let x=42; let p=&raw x; let q=p+0; *q=7;",
            "writable pointer",
        ),
        (
            "let mut x=42; let p=&raw mut x; let q=p+0; let r=&*q;",
            "10.1/10.3",
        ),
        (
            "let x=42; let p=&raw x; let q=p+0; let value=*q;",
            "no access permission",
        ),
    ] {
        let output = analyze(&SourceFile::from_text(
            "domain-gate.nera",
            format!("fn main()->u64 {{ {body} return 42; }}"),
        ));
        assert!(output.vir().is_none());
        assert!(
            output
                .issues()
                .iter()
                .any(|i| i.diagnostic().message().contains(diagnostic)),
            "{:?}",
            output.issues()
        );
    }
}
