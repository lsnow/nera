use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64InstructionPlan};
use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, VirAbiClass, VirBasicBlock, VirBlockId,
    VirBorrowEnvironment, VirBorrowRegion, VirBorrowRegionConstraint, VirBorrowRegionConstraintId,
    VirBorrowRegionId, VirBorrowRegionOrigin, VirBorrowRegionScope, VirConstant, VirContractId,
    VirEndianness, VirExecutionErrorKind, VirFunction, VirFunctionId, VirInstruction, VirLayout,
    VirLayoutId, VirLoanEffect, VirLoanId, VirLoanKind, VirLoanRange, VirMemoryAccess,
    VirMemorySchema, VirMemoryType, VirMemoryTypeKind, VirMutability, VirOriginId, VirPointerKind,
    VirRegionId, VirSignature, VirTargetDataLayout, VirTerminator, VirType, VirTypeId, VirUnit,
    VirUnitVersion, VirValidationErrorKind, VirValue, VirValueId, analyze_function_cfg, interpret,
};

const U64_TYPE: VirTypeId = VirTypeId::new(0);
const SHARED_REFERENCE_TYPE: VirTypeId = VirTypeId::new(1);
const MUTABLE_REFERENCE_TYPE: VirTypeId = VirTypeId::new(2);
const U64_ACCESS: VirMemoryAccess = VirMemoryAccess::new(U64_TYPE, VirLayoutId::new(0));
const SHARED_REFERENCE_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(SHARED_REFERENCE_TYPE, VirLayoutId::new(1));
const MUTABLE_REFERENCE_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(MUTABLE_REFERENCE_TYPE, VirLayoutId::new(2));

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(start, end).expect("valid test span")
}

fn reference_schema() -> VirMemorySchema {
    let mut schema = VirMemorySchema {
        target: VirTargetDataLayout {
            endianness: VirEndianness::Little,
            pointer_size_bytes: 8,
            pointer_alignment: 8,
            usize_size_bytes: 8,
            usize_alignment: 8,
        },
        types: vec![
            VirMemoryType {
                id: U64_TYPE,
                kind: VirMemoryTypeKind::Integer(nera::VirIntegerType::U64),
                layout: VirLayoutId::new(0),
            },
            VirMemoryType {
                id: SHARED_REFERENCE_TYPE,
                kind: VirMemoryTypeKind::Pointer {
                    pointee: U64_TYPE,
                    kind: VirPointerKind::Reference,
                    mutability: VirMutability::Const,
                },
                layout: VirLayoutId::new(1),
            },
            VirMemoryType {
                id: MUTABLE_REFERENCE_TYPE,
                kind: VirMemoryTypeKind::Pointer {
                    pointee: U64_TYPE,
                    kind: VirPointerKind::Reference,
                    mutability: VirMutability::Mutable,
                },
                layout: VirLayoutId::new(2),
            },
        ],
        type_capabilities: Vec::new(),
        layouts: vec![
            VirLayout {
                id: VirLayoutId::new(0),
                ty: U64_TYPE,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(1),
                ty: SHARED_REFERENCE_TYPE,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(2),
                ty: MUTABLE_REFERENCE_TYPE,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            },
        ],
        fields: Vec::new(),
        variants: Vec::new(),
    };
    schema
        .assign_canonical_type_capabilities()
        .expect("reference capabilities derive");
    schema
}

fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

fn effect(
    loan: u32,
    region: u32,
    parent: Option<u32>,
    pointer: u32,
    permission: u32,
) -> VirLoanEffect {
    VirLoanEffect {
        loan: VirLoanId::new(loan),
        kind: VirLoanKind::Shared,
        region: VirBorrowRegionId::new(region),
        parent: parent.map(VirLoanId::new),
        source_pointer: VirValueId::new(pointer),
        source_permission: VirValueId::new(permission),
        reference: SHARED_REFERENCE_ACCESS,
        range: VirLoanRange {
            start_bytes: 0,
            end_bytes: 8,
        },
        // `VirUnit::from_runtime` replaces this placeholder with the
        // canonical generated origin for the effect location.
        origin: VirOriginId::new(0),
    }
}

fn spanned(instruction: VirInstruction, start: usize) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(start, start + 1),
    }
}

fn loan_unit() -> VirUnit {
    let instructions = vec![
        spanned(
            VirInstruction::Constant {
                result: value(0, VirType::U64),
                value: VirConstant::U64(8),
            },
            10,
        ),
        spanned(
            VirInstruction::Allocate {
                pointer_result: value(1, VirType::Pointer { access: U64_ACCESS }),
                permission_result: value(2, VirType::Permission),
                size_bytes: VirValueId::new(0),
                alignment: 8,
                region: VirRegionId::new(0),
                element: U64_ACCESS,
            },
            12,
        ),
        spanned(
            VirInstruction::Initialize {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
                value: VirValueId::new(0),
                access: U64_ACCESS,
            },
            14,
        ),
        spanned(
            VirInstruction::LoanBegin {
                effect: effect(0, 0, None, 1, 2),
                reference_result: value(3, VirType::Pointer { access: U64_ACCESS }),
                permission_result: value(4, VirType::Permission),
            },
            20,
        ),
        spanned(
            VirInstruction::LoanAliasShared {
                effect: effect(0, 0, None, 3, 4),
                reference_result: value(5, VirType::Pointer { access: U64_ACCESS }),
                permission_result: value(6, VirType::Permission),
            },
            22,
        ),
        spanned(
            VirInstruction::LoanReborrow {
                effect: effect(1, 1, Some(0), 5, 6),
                reference_result: value(7, VirType::Pointer { access: U64_ACCESS }),
                permission_result: value(8, VirType::Permission),
            },
            24,
        ),
        spanned(
            VirInstruction::LoanEnd {
                effect: effect(1, 1, Some(0), 7, 8),
            },
            26,
        ),
        spanned(
            VirInstruction::LoanEnd {
                effect: effect(0, 0, None, 5, 6),
            },
            28,
        ),
    ];
    let mut unit = VirUnit::from_runtime(
        reference_schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "loan_schema".to_owned(),
            signature: VirSignature {
                parameters: Vec::new(),
                results: Vec::new(),
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: Vec::new(),
                instructions,
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return { values: Vec::new() },
                    source_span: span(30, 31),
                },
                source_span: span(5, 40),
            }],
            source_span: span(0, 50),
        }],
    );
    unit.borrows = VirBorrowEnvironment::from_tables(
        vec![
            VirBorrowRegion {
                id: VirBorrowRegionId::new(0),
                owner: VirFunctionId::new(0),
                origin: VirBorrowRegionOrigin::Lexical,
                scope: VirBorrowRegionScope::Blocks(vec![VirBlockId::new(0)]),
                source_origin: VirOriginId::new(0),
            },
            VirBorrowRegion {
                id: VirBorrowRegionId::new(1),
                owner: VirFunctionId::new(0),
                origin: VirBorrowRegionOrigin::Inferred,
                scope: VirBorrowRegionScope::Blocks(vec![VirBlockId::new(0)]),
                source_origin: VirOriginId::new(0),
            },
        ],
        vec![VirBorrowRegionConstraint {
            id: VirBorrowRegionConstraintId::new(0),
            owner: VirFunctionId::new(0),
            subregion: VirBorrowRegionId::new(1),
            superregion: VirBorrowRegionId::new(0),
            source_origin: VirOriginId::new(0),
        }],
    );
    unit
}

fn instruction_effect_mut(unit: &mut VirUnit, index: usize) -> &mut VirLoanEffect {
    match &mut unit.runtime.functions[0].blocks[0].instructions[index].instruction {
        VirInstruction::LoanBegin { effect, .. }
        | VirInstruction::LoanAliasShared { effect, .. }
        | VirInstruction::LoanReborrow { effect, .. }
        | VirInstruction::LoanEnd { effect } => effect,
        instruction => panic!("expected loan instruction, found {instruction:?}"),
    }
}

#[test]
fn current_schema_dumps_every_closed_loan_effect_and_reaches_all_consumers() {
    let unit = loan_unit();
    unit.validate().expect("canonical loan schema validates");
    let dump = unit.stable_dump();
    assert!(dump.starts_with("vir-unit-v27\n"));
    assert!(dump.contains("borrow-regions {"));
    assert!(dump.contains("constraint bconstraint0 owner fn0 bregion1 <= bregion0"));
    for spelling in [
        "loan.begin",
        "loan.alias-shared",
        "loan.reborrow",
        "loan.end",
        "reason loan-effect",
    ] {
        assert!(dump.contains(spelling), "missing {spelling} in {dump}");
    }

    let validated = unit.into_validated().expect("loan VIR seals");
    assert!(
        validated
            .runtime()
            .stable_dump()
            .starts_with("runtime-vir-v17\n")
    );
    let resolved = validated
        .resolve()
        .expect("loan VIR has no unresolved calls");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("verifier executes the 7.2.4 loan transfer");
    assert!(!analysis.all_obligations_proven());
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            nera::ResourceObligationKind::LoanEndedExactlyOnce { loan }
                if loan == VirLoanId::new(0)
        ) && record.obligation().status() == nera::ObligationStatus::Refuted
    }));
    assert_eq!(
        interpret(resolved.runtime())
            .expect_err("runtime shadow catches the deliberately missing final end")
            .kind(),
        &VirExecutionErrorKind::LoanNotEnded {
            loan: VirLoanId::new(0)
        }
    );
    let plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("native planning erases the unverified loan shadow");
    let instructions = plan.functions()[0].blocks()[0].instructions();
    assert!(
        instructions
            .iter()
            .any(|plan| plan == &X86_64InstructionPlan::LoanReference)
    );
    assert!(
        instructions
            .iter()
            .any(|plan| plan == &X86_64InstructionPlan::ErasedLoan)
    );
}

#[test]
fn historical_versions_cannot_accept_v6_loan_origins() {
    let mut unit = loan_unit();
    unit.version = VirUnitVersion::V5;
    assert!(matches!(
        unit.validate()
            .expect_err("V5 cannot carry loan effects")
            .kind(),
        VirValidationErrorKind::UnsupportedUnitVersion(VirUnitVersion::V5)
    ));
}

#[test]
fn region_and_constraint_tables_are_dense_owned_scoped_and_anchored() {
    let mut unit = loan_unit();
    unit.borrows = VirBorrowEnvironment::from_tables(
        vec![VirBorrowRegion {
            id: VirBorrowRegionId::new(4),
            owner: VirFunctionId::new(0),
            origin: VirBorrowRegionOrigin::Lexical,
            scope: VirBorrowRegionScope::Blocks(vec![VirBlockId::new(0)]),
            source_origin: VirOriginId::new(0),
        }],
        Vec::new(),
    );
    assert!(matches!(
        unit.validate().expect_err("region IDs are dense").kind(),
        VirValidationErrorKind::NonDenseBorrowRegionId { .. }
    ));

    let mut unit = loan_unit();
    unit.borrows = VirBorrowEnvironment::from_tables(
        vec![VirBorrowRegion {
            scope: VirBorrowRegionScope::Blocks(Vec::new()),
            ..unit.borrows.regions()[0].clone()
        }],
        Vec::new(),
    );
    assert_eq!(
        unit.validate()
            .expect_err("empty lexical scope is invalid")
            .kind(),
        &VirValidationErrorKind::InvalidBorrowRegion(VirBorrowRegionId::new(0))
    );

    let mut unit = loan_unit();
    let regions = unit.borrows.regions().to_vec();
    unit.borrows = VirBorrowEnvironment::from_tables(
        regions,
        vec![VirBorrowRegionConstraint {
            subregion: VirBorrowRegionId::new(0),
            superregion: VirBorrowRegionId::new(0),
            ..unit.borrows.constraints()[0]
        }],
    );
    assert_eq!(
        unit.validate()
            .expect_err("reflexive stored edge is invalid")
            .kind(),
        &VirValidationErrorKind::InvalidBorrowRegionConstraint(VirBorrowRegionConstraintId::new(0))
    );
}

#[test]
fn loan_validation_rederives_range_metadata_parent_scope_and_origin() {
    let mut unit = loan_unit();
    instruction_effect_mut(&mut unit, 3).range.end_bytes = 7;
    assert_eq!(
        unit.validate()
            .expect_err("range is derived from pointee layout")
            .kind(),
        &VirValidationErrorKind::InvalidLoanRange(VirLoanId::new(0))
    );

    let mut unit = loan_unit();
    instruction_effect_mut(&mut unit, 7).region = VirBorrowRegionId::new(1);
    assert_eq!(
        unit.validate()
            .expect_err("effect metadata must match its definition")
            .kind(),
        &VirValidationErrorKind::LoanMetadataMismatch(VirLoanId::new(0))
    );

    let mut unit = loan_unit();
    instruction_effect_mut(&mut unit, 5).parent = Some(VirLoanId::new(4));
    assert_eq!(
        unit.validate()
            .expect_err("reborrow parent must be earlier")
            .kind(),
        &VirValidationErrorKind::InvalidLoanParent(VirLoanId::new(1))
    );

    let mut unit = loan_unit();
    for index in [5, 6] {
        let effect = instruction_effect_mut(&mut unit, index);
        effect.kind = VirLoanKind::Mutable;
        effect.reference = MUTABLE_REFERENCE_ACCESS;
    }
    assert_eq!(
        unit.validate()
            .expect_err("shared parents cannot grant mutable child loans")
            .kind(),
        &VirValidationErrorKind::InvalidLoanParent(VirLoanId::new(1))
    );

    let mut unit = loan_unit();
    for index in [5, 6] {
        let range = &mut instruction_effect_mut(&mut unit, index).range;
        range.start_bytes = 8;
        range.end_bytes = 16;
    }
    assert_eq!(
        unit.validate()
            .expect_err("child range must be contained by its parent")
            .kind(),
        &VirValidationErrorKind::InvalidLoanParent(VirLoanId::new(1))
    );

    let mut unit = loan_unit();
    let instructions = &mut unit.runtime.functions[0].blocks[0].instructions;
    instructions.swap(3, 4);
    instruction_effect_mut(&mut unit, 3).source_pointer = VirValueId::new(1);
    instruction_effect_mut(&mut unit, 3).source_permission = VirValueId::new(2);
    assert_eq!(
        unit.validate()
            .expect_err("aliases cannot precede their definition")
            .kind(),
        &VirValidationErrorKind::LoanEffectOutOfOrder(VirLoanId::new(0))
    );

    let mut unit = loan_unit();
    instruction_effect_mut(&mut unit, 3).origin = VirOriginId::new(0);
    assert_eq!(
        unit.validate()
            .expect_err("user origins cannot forge loan effects")
            .kind(),
        &VirValidationErrorKind::InvalidLoanEffectOrigin(VirLoanId::new(0))
    );
}
