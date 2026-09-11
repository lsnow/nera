use nera::{
    AbstractLoan, AbstractProvenance, ByteSpan, CfgAnalysisConfig, FunctionCfgAnalysis,
    LoanActivity, LoanPrecisionLoss, ObligationStatus, PermissionAuthority, ResourceJoinError,
    ResourceObligationKind, ResourceState, SpannedVirTerminator, VirBasicBlock, VirBlockId,
    VirBlockTarget, VirBorrowEnvironment, VirBorrowRegion, VirBorrowRegionConstraint,
    VirBorrowRegionConstraintId, VirBorrowRegionId, VirBorrowRegionOrigin, VirBorrowRegionScope,
    VirContractId, VirFunction, VirFunctionId, VirInstruction, VirLoanId, VirLoanKind, VirOriginId,
    VirSignature, VirTerminator, VirType, VirValueId, analyze_function_cfg,
    analyze_function_cfg_with_config,
};

#[path = "support/loan_program.rs"]
mod loan_program;

fn analyze(unit: nera::VirUnit) -> FunctionCfgAnalysis {
    let validated = unit.into_validated().expect("loan fixture validates");
    let resolved = validated.resolve().expect("loan fixture resolves");
    analyze_function_cfg(&resolved, VirFunctionId::new(0)).expect("loan analysis succeeds")
}

fn status(
    analysis: &FunctionCfgAnalysis,
    predicate: impl Fn(ResourceObligationKind) -> bool,
) -> Option<ObligationStatus> {
    analysis
        .obligations()
        .iter()
        .find(|record| predicate(record.obligation().kind()))
        .map(|record| record.obligation().status())
}

fn has_obligation(
    analysis: &FunctionCfgAnalysis,
    expected_status: ObligationStatus,
    predicate: impl Fn(ResourceObligationKind) -> bool,
) -> bool {
    analysis.obligations().iter().any(|record| {
        predicate(record.obligation().kind()) && record.obligation().status() == expected_status
    })
}

#[test]
fn shared_aliases_end_independently_and_restore_owner_write() {
    let analysis = analyze(loan_program::shared_lifecycle());
    assert!(analysis.all_obligations_proven());
    let final_state = analysis
        .returns()
        .first()
        .expect("safe lifecycle returns")
        .state();
    assert_eq!(
        final_state
            .loan(VirLoanId::new(0))
            .map(|loan| loan.activity()),
        Some(LoanActivity::Ended)
    );
    for permission in [VirValueId::new(5), VirValueId::new(8)] {
        assert!(matches!(
            final_state.value(permission),
            Some(nera::AbstractValue::Permission(fact))
                if fact.authority() == PermissionAuthority::Loan(VirLoanId::new(0))
                    && fact.availability() == nera::PermissionAvailability::Consumed
        ));
    }
}

#[test]
fn active_shared_loan_allows_reads_but_refutes_owner_write_and_free() {
    let mut write = loan_program::allocation_prefix();
    write.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::Load {
                result: loan_program::value(6, VirType::U64),
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
                access: loan_program::U64_ACCESS,
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::Store {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: loan_program::U64_ACCESS,
            },
        ),
    ]);
    let analysis = analyze(loan_program::unit(write, 1));
    assert!(has_obligation(
        &analysis,
        ObligationStatus::Refuted,
        |kind| matches!(
            kind,
            ResourceObligationKind::LoanCompatible {
                permission,
                required: nera::AccessPermission::Write,
                ..
            } if permission == VirValueId::new(2)
        ),
    ));

    let mut free = loan_program::allocation_prefix();
    free.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);
    let analysis = analyze(loan_program::unit(free, 1));
    assert!(has_obligation(
        &analysis,
        ObligationStatus::Refuted,
        |kind| matches!(
            kind,
            ResourceObligationKind::LoanCompatible {
                permission,
                required: nera::AccessPermission::Write,
                ..
            } if permission == VirValueId::new(2)
        ),
    ));
}

#[test]
fn mutable_loan_excludes_owner_but_allows_reference_write() {
    let mut instructions = loan_program::allocation_prefix();
    instructions.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::Store {
                pointer: VirValueId::new(4),
                value: VirValueId::new(3),
                permission: VirValueId::new(5),
                access: loan_program::U64_ACCESS,
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 4, 5),
            },
        ),
        loan_program::spanned(
            7,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);
    assert!(analyze(loan_program::unit(instructions, 1)).all_obligations_proven());
}

#[test]
fn permission_move_transfers_the_canonical_loan_authority() {
    let mut instructions = loan_program::allocation_prefix();
    instructions.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::PermissionMove {
                result: loan_program::permission(6),
                source: VirValueId::new(5),
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::Store {
                pointer: VirValueId::new(4),
                value: VirValueId::new(3),
                permission: VirValueId::new(6),
                access: loan_program::U64_ACCESS,
            },
        ),
        loan_program::spanned(
            7,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 4, 6),
            },
        ),
        loan_program::spanned(
            8,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);
    let analysis = analyze(loan_program::unit(instructions, 1));
    assert!(analysis.all_obligations_proven());
    let loan = analysis.returns()[0]
        .state()
        .loan(VirLoanId::new(0))
        .expect("loan remains recorded");
    assert_eq!(loan.activity(), LoanActivity::Ended);
    assert!(loan.authorities().is_empty());
}

#[test]
fn cfg_projection_keeps_unpassed_alias_authority_alive() {
    let mut instructions = loan_program::allocation_prefix();
    instructions.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::LoanAliasShared {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 4, 5),
                reference_result: loan_program::pointer(6),
                permission_result: loan_program::permission(7),
            },
        ),
    ]);
    let mut unit = loan_program::unit(instructions.clone(), 1);
    unit.runtime.functions[0].blocks = vec![
        VirBasicBlock {
            id: VirBlockId::new(0),
            parameters: Vec::new(),
            instructions,
            terminator: SpannedVirTerminator {
                terminator: VirTerminator::Jump {
                    target: VirBlockTarget {
                        block: VirBlockId::new(1),
                        arguments: vec![VirValueId::new(4), VirValueId::new(5)],
                    },
                },
                source_span: loan_program::span(40),
            },
            source_span: ByteSpan::new(5, 42).expect("entry span"),
        },
        VirBasicBlock {
            id: VirBlockId::new(1),
            parameters: vec![loan_program::pointer(10), loan_program::permission(11)],
            instructions: vec![loan_program::spanned(
                20,
                VirInstruction::LoanEnd {
                    effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 10, 11),
                },
            )],
            terminator: SpannedVirTerminator {
                terminator: VirTerminator::Return { values: Vec::new() },
                source_span: loan_program::span(62),
            },
            source_span: ByteSpan::new(45, 65).expect("successor span"),
        },
    ];
    unit.runtime.functions[0].source_span = ByteSpan::new(0, 66).expect("function span");
    unit.borrows = VirBorrowEnvironment::from_tables(
        vec![VirBorrowRegion {
            id: VirBorrowRegionId::new(0),
            owner: VirFunctionId::new(0),
            origin: VirBorrowRegionOrigin::Inferred,
            scope: VirBorrowRegionScope::Blocks(vec![VirBlockId::new(0), VirBlockId::new(1)]),
            source_origin: VirOriginId::new(0),
        }],
        Vec::new(),
    );
    unit.rebuild_source_map_from_runtime("<loan-cfg-alias>", 80);

    let analysis = analyze(unit);
    assert!(has_obligation(
        &analysis,
        ObligationStatus::Refuted,
        |kind| matches!(kind, ResourceObligationKind::LoanEndedExactlyOnce { loan }
            if loan == VirLoanId::new(0))
    ));
    let loan = analysis
        .block(VirBlockId::new(1))
        .expect("successor analyzed")
        .instruction_states()
        .last()
        .expect("loan end state recorded")
        .loan(VirLoanId::new(0))
        .expect("loan remains active");
    assert_eq!(loan.activity(), LoanActivity::Active);
    assert_eq!(loan.authorities().len(), 1);
}

fn reborrow_lifecycle() -> nera::VirUnit {
    let mut instructions = loan_program::allocation_prefix();
    instructions.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::LoanReborrow {
                effect: loan_program::effect(1, VirLoanKind::Shared, 1, Some(0), 4, 5),
                reference_result: loan_program::pointer(6),
                permission_result: loan_program::permission(7),
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::Load {
                result: loan_program::value(8, VirType::U64),
                pointer: VirValueId::new(6),
                permission: VirValueId::new(7),
                access: loan_program::U64_ACCESS,
            },
        ),
        loan_program::spanned(
            7,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(1, VirLoanKind::Shared, 1, Some(0), 6, 7),
            },
        ),
        loan_program::spanned(
            8,
            VirInstruction::Store {
                pointer: VirValueId::new(4),
                value: VirValueId::new(3),
                permission: VirValueId::new(5),
                access: loan_program::U64_ACCESS,
            },
        ),
        loan_program::spanned(
            9,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 4, 5),
            },
        ),
        loan_program::spanned(
            10,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);
    loan_program::unit(instructions, 2)
}

#[test]
fn reborrow_suspends_parent_and_exact_child_end_restores_it() {
    let analysis = analyze(reborrow_lifecycle());
    assert!(analysis.all_obligations_proven());
    let states = analysis
        .block(nera::VirBlockId::new(0))
        .expect("entry block analyzed")
        .instruction_states();
    assert_eq!(
        states[5]
            .loan(VirLoanId::new(0))
            .map(|loan| loan.activity()),
        Some(LoanActivity::Suspended)
    );
    assert_eq!(
        states[7]
            .loan(VirLoanId::new(0))
            .map(|loan| loan.activity()),
        Some(LoanActivity::Active)
    );
}

#[test]
fn guarded_child_lifecycle_restores_parent_on_every_join_alternative() {
    let mut entry_instructions = loan_program::allocation_prefix();
    entry_instructions.push(loan_program::spanned(
        4,
        VirInstruction::LoanBegin {
            effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 1, 2),
            reference_result: loan_program::pointer(4),
            permission_result: loan_program::permission(5),
        },
    ));
    let mut unit = nera::VirUnit::from_runtime(
        loan_program::memory_schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "guarded_reborrow".to_owned(),
            signature: VirSignature {
                parameters: vec![VirType::Bool],
                results: Vec::new(),
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![
                VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![loan_program::value(100, VirType::Bool)],
                    instructions: entry_instructions,
                    terminator: SpannedVirTerminator {
                        terminator: VirTerminator::Branch {
                            condition: VirValueId::new(100),
                            then_target: VirBlockTarget {
                                block: VirBlockId::new(1),
                                arguments: vec![
                                    VirValueId::new(4),
                                    VirValueId::new(5),
                                    VirValueId::new(1),
                                    VirValueId::new(2),
                                ],
                            },
                            else_target: VirBlockTarget {
                                block: VirBlockId::new(2),
                                arguments: vec![
                                    VirValueId::new(4),
                                    VirValueId::new(5),
                                    VirValueId::new(1),
                                    VirValueId::new(2),
                                ],
                            },
                        },
                        source_span: loan_program::span(20),
                    },
                    source_span: ByteSpan::new(5, 52).expect("entry span"),
                },
                VirBasicBlock {
                    id: VirBlockId::new(1),
                    parameters: vec![
                        loan_program::pointer(10),
                        loan_program::permission(11),
                        loan_program::pointer(12),
                        loan_program::permission(13),
                    ],
                    instructions: vec![
                        loan_program::spanned(
                            21,
                            VirInstruction::LoanReborrow {
                                effect: loan_program::effect(
                                    1,
                                    VirLoanKind::Shared,
                                    1,
                                    Some(0),
                                    10,
                                    11,
                                ),
                                reference_result: loan_program::pointer(14),
                                permission_result: loan_program::permission(15),
                            },
                        ),
                        loan_program::spanned(
                            22,
                            VirInstruction::LoanEnd {
                                effect: loan_program::effect(
                                    1,
                                    VirLoanKind::Shared,
                                    1,
                                    Some(0),
                                    14,
                                    15,
                                ),
                            },
                        ),
                    ],
                    terminator: SpannedVirTerminator {
                        terminator: VirTerminator::Jump {
                            target: VirBlockTarget {
                                block: VirBlockId::new(3),
                                arguments: vec![
                                    VirValueId::new(10),
                                    VirValueId::new(11),
                                    VirValueId::new(12),
                                    VirValueId::new(13),
                                ],
                            },
                        },
                        source_span: loan_program::span(58),
                    },
                    source_span: ByteSpan::new(50, 60).expect("then span"),
                },
                VirBasicBlock {
                    id: VirBlockId::new(2),
                    parameters: vec![
                        loan_program::pointer(20),
                        loan_program::permission(21),
                        loan_program::pointer(22),
                        loan_program::permission(23),
                    ],
                    instructions: Vec::new(),
                    terminator: SpannedVirTerminator {
                        terminator: VirTerminator::Jump {
                            target: VirBlockTarget {
                                block: VirBlockId::new(3),
                                arguments: vec![
                                    VirValueId::new(20),
                                    VirValueId::new(21),
                                    VirValueId::new(22),
                                    VirValueId::new(23),
                                ],
                            },
                        },
                        source_span: loan_program::span(63),
                    },
                    source_span: ByteSpan::new(61, 65).expect("else span"),
                },
                VirBasicBlock {
                    id: VirBlockId::new(3),
                    parameters: vec![
                        loan_program::pointer(30),
                        loan_program::permission(31),
                        loan_program::pointer(32),
                        loan_program::permission(33),
                    ],
                    instructions: vec![
                        loan_program::spanned(
                            25,
                            VirInstruction::Load {
                                result: loan_program::value(34, VirType::U64),
                                pointer: VirValueId::new(30),
                                permission: VirValueId::new(31),
                                access: loan_program::U64_ACCESS,
                            },
                        ),
                        loan_program::spanned(
                            26,
                            VirInstruction::LoanEnd {
                                effect: loan_program::effect(
                                    0,
                                    VirLoanKind::Mutable,
                                    0,
                                    None,
                                    30,
                                    31,
                                ),
                            },
                        ),
                        loan_program::spanned(
                            27,
                            VirInstruction::Free {
                                pointer: VirValueId::new(32),
                                permission: VirValueId::new(33),
                            },
                        ),
                    ],
                    terminator: SpannedVirTerminator {
                        terminator: VirTerminator::Return { values: Vec::new() },
                        source_span: loan_program::span(78),
                    },
                    source_span: ByteSpan::new(60, 80).expect("join span"),
                },
            ],
            source_span: ByteSpan::new(0, 82).expect("function span"),
        }],
    );
    unit.borrows = VirBorrowEnvironment::from_tables(
        vec![
            VirBorrowRegion {
                id: VirBorrowRegionId::new(0),
                owner: VirFunctionId::new(0),
                origin: VirBorrowRegionOrigin::Inferred,
                scope: VirBorrowRegionScope::Blocks(vec![
                    VirBlockId::new(0),
                    VirBlockId::new(1),
                    VirBlockId::new(2),
                    VirBlockId::new(3),
                ]),
                source_origin: VirOriginId::new(0),
            },
            VirBorrowRegion {
                id: VirBorrowRegionId::new(1),
                owner: VirFunctionId::new(0),
                origin: VirBorrowRegionOrigin::Inferred,
                scope: VirBorrowRegionScope::Blocks(vec![VirBlockId::new(1)]),
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
    unit.rebuild_source_map_from_runtime("<guarded-reborrow>", 100);

    let analysis = analyze(unit);
    assert!(
        analysis.all_obligations_proven(),
        "obligations: {:#?}",
        analysis.obligations()
    );
}

#[test]
fn parent_end_before_child_and_double_or_missing_end_fail_closed() {
    let mut premature = reborrow_lifecycle();
    premature.runtime.functions[0].blocks[0]
        .instructions
        .insert(
            7,
            loan_program::spanned(
                11,
                VirInstruction::LoanEnd {
                    effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 4, 5),
                },
            ),
        );
    premature.rebuild_source_map_from_runtime("<premature-end>", 64);
    let analysis = analyze(premature);
    assert!(has_obligation(
        &analysis,
        ObligationStatus::Refuted,
        |kind| matches!(
            kind,
            ResourceObligationKind::LoanEndedExactlyOnce { loan }
                if loan == VirLoanId::new(0)
        )
    ));

    let mut double = loan_program::shared_lifecycle();
    double.runtime.functions[0].blocks[0].instructions.insert(
        9,
        loan_program::spanned(
            11,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 4, 5),
            },
        ),
    );
    double.rebuild_source_map_from_runtime("<double-end>", 64);
    let analysis = analyze(double);
    assert!(has_obligation(
        &analysis,
        ObligationStatus::Refuted,
        |kind| matches!(kind, ResourceObligationKind::LoanEndedExactlyOnce { .. })
    ));

    let mut missing = loan_program::shared_lifecycle();
    missing.runtime.functions[0].blocks[0]
        .instructions
        .truncate(8);
    missing.rebuild_source_map_from_runtime("<missing-end>", 64);
    let analysis = analyze(missing);
    assert!(has_obligation(
        &analysis,
        ObligationStatus::Refuted,
        |kind| matches!(kind, ResourceObligationKind::LoanEndedExactlyOnce { .. })
    ));
}

#[test]
fn loop_carried_unended_instance_fails_closed_without_transfer_failure() {
    let mut instructions = loan_program::allocation_prefix();
    instructions.push(loan_program::spanned(
        4,
        VirInstruction::LoanBegin {
            effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
            reference_result: loan_program::pointer(4),
            permission_result: loan_program::permission(5),
        },
    ));
    let mut unit = loan_program::unit(instructions, 1);
    unit.runtime.functions[0].blocks[0].terminator = SpannedVirTerminator {
        terminator: VirTerminator::Jump {
            target: VirBlockTarget {
                block: VirBlockId::new(0),
                arguments: Vec::new(),
            },
        },
        source_span: loan_program::span(10),
    };
    unit.rebuild_source_map_from_runtime("<escaping-loop-loan>", 64);

    let analysis = analyze(unit);
    assert!(analysis.returns().is_empty());
    assert!(analysis.loop_blocks().contains(&VirBlockId::new(0)));
    assert!(has_obligation(
        &analysis,
        ObligationStatus::Unknown,
        |kind| matches!(
            kind,
            ResourceObligationKind::LoanEndedExactlyOnce { loan }
                if loan == VirLoanId::new(0)
        )
    ));
    assert!(!analysis.all_obligations_proven());
}

#[test]
fn overlapping_mutable_root_and_permission_split_cannot_bypass_loan_identity() {
    let mut conflict = loan_program::allocation_prefix();
    conflict.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(1, VirLoanKind::Mutable, 0, None, 1, 2),
                reference_result: loan_program::pointer(6),
                permission_result: loan_program::permission(7),
            },
        ),
    ]);
    let analysis = analyze(loan_program::unit(conflict, 1));
    assert!(has_obligation(
        &analysis,
        ObligationStatus::Refuted,
        |kind| matches!(
            kind,
            ResourceObligationKind::LoanCompatible {
                loan: Some(loan),
                ..
            } if loan == VirLoanId::new(1)
        )
    ));

    let mut split = loan_program::allocation_prefix();
    split.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::Constant {
                result: loan_program::value(6, VirType::U64),
                value: nera::VirConstant::U64(4),
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::PermissionSplit {
                left_result: loan_program::permission(7),
                right_result: loan_program::permission(8),
                source: VirValueId::new(5),
                split_at_bytes: VirValueId::new(6),
            },
        ),
    ]);
    let analysis = analyze(loan_program::unit(split, 1));
    assert!(has_obligation(
        &analysis,
        ObligationStatus::Refuted,
        |kind| matches!(
            kind,
            ResourceObligationKind::LoanCompatible {
                loan: Some(loan),
                permission,
                ..
            } if loan == VirLoanId::new(0) && permission == VirValueId::new(5)
        )
    ));
}

#[test]
fn loan_budgets_degrade_to_unknown_without_granting_authority() {
    let unit = loan_program::shared_lifecycle();
    let validated = unit.into_validated().expect("loan fixture validates");
    let resolved = validated.resolve().expect("loan fixture resolves");
    let analysis = analyze_function_cfg_with_config(
        &resolved,
        VirFunctionId::new(0),
        CfgAnalysisConfig {
            max_active_loans_per_case: 0,
            ..CfgAnalysisConfig::default()
        },
    )
    .expect("budget loss is not an analysis crash");
    assert_eq!(
        status(&analysis, |kind| matches!(
            kind,
            ResourceObligationKind::LoanWithinBudget { loan, .. }
                if loan == VirLoanId::new(0)
        )),
        Some(ObligationStatus::Unknown)
    );
    let begin_state = &analysis
        .block(VirBlockId::new(0))
        .expect("entry analyzed")
        .instruction_states()[4];
    assert!(begin_state.loan(VirLoanId::new(0)).is_none());
    assert!(matches!(
        begin_state.value(VirValueId::new(5)),
        Some(nera::AbstractValue::Permission(permission))
            if permission.authority() == PermissionAuthority::Unknown
    ));
    assert!(!analysis.all_obligations_proven());
    assert!(
        analysis
            .guarded_precision_losses()
            .values()
            .any(|losses| { losses.contains(&nera::GuardedStatePrecisionLoss::ActiveLoanBudget) })
    );
}

#[test]
fn alias_region_and_reborrow_depth_budgets_are_reported_without_false_proofs() {
    for (config, expected) in [
        (
            CfgAnalysisConfig {
                max_aliases_per_loan: 1,
                ..CfgAnalysisConfig::default()
            },
            nera::GuardedStatePrecisionLoss::LoanAliasBudget,
        ),
        (
            CfgAnalysisConfig {
                max_region_constraints_per_function: 0,
                ..CfgAnalysisConfig::default()
            },
            nera::GuardedStatePrecisionLoss::RegionConstraintBudget,
        ),
        (
            CfgAnalysisConfig {
                max_reborrow_depth: 0,
                ..CfgAnalysisConfig::default()
            },
            nera::GuardedStatePrecisionLoss::ReborrowDepthBudget,
        ),
    ] {
        let unit = if expected == nera::GuardedStatePrecisionLoss::LoanAliasBudget {
            loan_program::shared_lifecycle()
        } else {
            reborrow_lifecycle()
        };
        let validated = unit.into_validated().expect("loan fixture validates");
        let resolved = validated.resolve().expect("loan fixture resolves");
        let analysis = analyze_function_cfg_with_config(&resolved, VirFunctionId::new(0), config)
            .expect("loan budget is conservative");
        assert!(!analysis.all_obligations_proven());
        assert!(
            analysis
                .guarded_precision_losses()
                .values()
                .any(|losses| losses.contains(&expected))
        );
    }
}

fn abstract_loan(activity: LoanActivity) -> AbstractLoan {
    AbstractLoan::new(
        AbstractProvenance::Known(nera::AbstractAllocationId::new(0)),
        nera::ByteRange::new(0, 8).expect("range"),
        VirLoanKind::Shared,
        VirBorrowRegionId::new(0),
        None,
        activity,
    )
}

#[test]
fn loan_join_is_conservative_and_rejects_inconsistent_metadata() {
    let mut active = ResourceState::new();
    active
        .define_loan(VirLoanId::new(0), abstract_loan(LoanActivity::Active))
        .expect("loan unique");
    let mut ended = ResourceState::new();
    ended
        .define_loan(VirLoanId::new(0), abstract_loan(LoanActivity::Ended))
        .expect("loan unique");
    let joined = active.join(&ended).expect("compatible loan join");
    assert_eq!(
        joined.loan(VirLoanId::new(0)).map(|loan| loan.activity()),
        Some(LoanActivity::MaybeActive)
    );
    assert!(
        joined
            .loan_precision_losses()
            .contains(&LoanPrecisionLoss::LoanJoin)
    );
    assert_eq!(active.join(&active).expect("idempotent"), active);
    assert_eq!(
        active.join(&ended).expect("commutative"),
        ended.join(&active).expect("commutative")
    );

    let mut incompatible = ResourceState::new();
    incompatible
        .define_loan(
            VirLoanId::new(0),
            AbstractLoan::new(
                AbstractProvenance::Known(nera::AbstractAllocationId::new(0)),
                nera::ByteRange::new(8, 16).expect("range"),
                VirLoanKind::Shared,
                VirBorrowRegionId::new(0),
                None,
                LoanActivity::Active,
            ),
        )
        .expect("loan unique");
    assert_eq!(
        active.join(&incompatible),
        Err(ResourceJoinError::LoanMetadataMismatch {
            loan: VirLoanId::new(0)
        })
    );

    let absent = ResourceState::new();
    assert!(
        ended
            .join(&absent)
            .expect("ended loan has no live authority")
            .loan(VirLoanId::new(0))
            .is_none(),
        "an ended loop-local instance must not poison the next iteration"
    );
    assert_eq!(
        active
            .join(&absent)
            .expect("active/absent join remains conservative")
            .loan(VirLoanId::new(0))
            .map(|loan| loan.activity()),
        Some(LoanActivity::MaybeActive)
    );
}

#[test]
fn loan_join_obeys_semilattice_laws_before_guard_reduction() {
    let states = [
        LoanActivity::Active,
        LoanActivity::Suspended,
        LoanActivity::Ended,
        LoanActivity::MaybeActive,
    ]
    .map(|activity| {
        let mut state = ResourceState::new();
        state
            .define_loan(VirLoanId::new(0), abstract_loan(activity))
            .expect("loan unique");
        state
    });
    for left in &states {
        assert_eq!(left.join(left).expect("idempotent"), *left);
        for right in &states {
            assert_eq!(
                left.join(right).expect("commutative"),
                right.join(left).expect("commutative")
            );
            for third in &states {
                assert_eq!(
                    left.join(right)
                        .expect("left join")
                        .join(third)
                        .expect("left-associated"),
                    left.join(&right.join(third).expect("right join"))
                        .expect("right-associated")
                );
            }
        }
    }
}
