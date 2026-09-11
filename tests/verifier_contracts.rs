use nera::{
    AbstractValue, ByteSpan, CfgAnalysisConfig, ObligationStatus, ResourceObligationKind,
    SpannedVirInstruction, SpannedVirTerminator, ValidatedVirUnit, VerifierDiagnosticKind,
    VerifierFindingSite, VerifierSpecEntity, VirBasicBlock, VirBlockId, VirBlockTarget,
    VirCallTarget, VirConstant, VirContractAccess, VirContractFree, VirContractId,
    VirContractInitialization, VirContractLiveness, VirContractOwnership, VirContractPosition,
    VirFunction, VirFunctionId, VirInstruction, VirLocation, VirRegionId, VirSignature,
    VirSpecClauseId, VirSpecLocation, VirTerminator, VirType, VirUnit, VirValidationErrorKind,
    VirValue, VirValueId, analyze_function_cfg_with_config, verify_program,
};

#[path = "support/contract_builder.rs"]
mod contract_builder;

use contract_builder::{
    PermissionFact, PointerFact, add_own_word, add_resource_clause, add_u64_range, function_origin,
};

fn span() -> ByteSpan {
    ByteSpan::new(10, 20).expect("valid test span")
}

fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

fn word(id: u32) -> VirValue {
    value(id, VirType::U64)
}

fn pointer(id: u32) -> VirValue {
    value(
        id,
        VirType::Pointer {
            access: nera::VirMemoryAccess::core_u64(),
        },
    )
}

fn permission(id: u32) -> VirValue {
    value(id, VirType::Permission)
}

fn instruction(instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(),
    }
}

fn block(
    parameters: Vec<VirValue>,
    instructions: Vec<SpannedVirInstruction>,
    values: Vec<VirValueId>,
) -> VirBasicBlock {
    VirBasicBlock {
        id: VirBlockId::new(0),
        parameters,
        instructions,
        terminator: SpannedVirTerminator {
            terminator: VirTerminator::Return { values },
            source_span: span(),
        },
        source_span: span(),
    }
}

fn function(
    id: u32,
    name: &str,
    signature: VirSignature,
    contract: u32,
    block: VirBasicBlock,
) -> VirFunction {
    VirFunction {
        id: VirFunctionId::new(id),
        name: name.to_owned(),
        signature,
        contract: VirContractId::new(contract),
        entry: VirBlockId::new(0),
        blocks: vec![block],
        source_span: span(),
    }
}

fn validated(functions: Vec<VirFunction>) -> ValidatedVirUnit {
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        functions[0].id,
        functions,
    )
    .into_validated()
    .expect("test program must be valid VIR")
}

fn configured(program: ValidatedVirUnit, configure: impl FnOnce(&mut VirUnit)) -> ValidatedVirUnit {
    let mut unit = program.as_unit().clone();
    configure(&mut unit);
    unit.into_validated().expect("configured contract fixture")
}

#[test]
fn inferred_own_facts_verify_load_and_free_without_explicit_clauses() {
    let signature = VirSignature {
        parameters: vec![
            VirType::Pointer {
                access: nera::VirMemoryAccess::core_u64(),
            },
            VirType::Permission,
        ],
        results: vec![VirType::U64],
    };
    let program = validated(vec![function(
        0,
        "consume",
        signature.clone(),
        0,
        block(
            vec![pointer(0), permission(1)],
            vec![
                instruction(VirInstruction::Load {
                    result: word(2),
                    pointer: VirValueId::new(0),
                    permission: VirValueId::new(1),
                    access: nera::VirMemoryAccess::core_u64(),
                }),
                instruction(VirInstruction::Free {
                    pointer: VirValueId::new(0),
                    permission: VirValueId::new(1),
                }),
            ],
            vec![VirValueId::new(2)],
        ),
    )]);
    let program = configured(program, |unit| {
        let origin = function_origin(unit, VirFunctionId::new(0));
        add_own_word(
            &mut unit.specs,
            VirContractId::new(0),
            VirContractPosition::Requires,
            origin,
            0,
            0,
            1,
            VirContractInitialization::Initialized,
        );
    });

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("closed contract environment must verify");

    assert!(verification.is_memory_checked_core0());
    assert!(verification.diagnostics().is_empty());
    assert!(verification.trust_report().entries().is_empty());
}

#[test]
fn call_summary_checks_preconditions_and_restores_returned_permission() {
    let callee_signature = VirSignature {
        parameters: vec![
            VirType::Pointer {
                access: nera::VirMemoryAccess::core_u64(),
            },
            VirType::Permission,
        ],
        results: vec![
            VirType::Pointer {
                access: nera::VirMemoryAccess::core_u64(),
            },
            VirType::Permission,
        ],
    };
    let caller_signature = VirSignature {
        parameters: Vec::new(),
        results: Vec::new(),
    };
    let callee = function(
        1,
        "identity",
        callee_signature.clone(),
        1,
        block(
            vec![pointer(0), permission(1)],
            Vec::new(),
            vec![VirValueId::new(0), VirValueId::new(1)],
        ),
    );
    let caller = function(
        0,
        "caller",
        caller_signature.clone(),
        0,
        block(
            Vec::new(),
            vec![
                instruction(VirInstruction::Constant {
                    result: word(0),
                    value: VirConstant::U64(8),
                }),
                instruction(VirInstruction::Allocate {
                    pointer_result: pointer(1),
                    permission_result: permission(2),
                    size_bytes: VirValueId::new(0),
                    alignment: 8,
                    region: VirRegionId::new(0),
                    element: nera::VirMemoryAccess::core_u64(),
                }),
                instruction(VirInstruction::Constant {
                    result: word(3),
                    value: VirConstant::U64(9),
                }),
                instruction(VirInstruction::Initialize {
                    pointer: VirValueId::new(1),
                    value: VirValueId::new(3),
                    permission: VirValueId::new(2),
                    access: nera::VirMemoryAccess::core_u64(),
                }),
                instruction(VirInstruction::Call {
                    results: vec![pointer(4), permission(5)],
                    target: VirCallTarget {
                        symbol: "identity".to_owned(),
                        signature: callee_signature.clone(),
                        contract: VirContractId::new(1),
                        abi: None,
                    },
                    arguments: vec![VirValueId::new(1), VirValueId::new(2)],
                }),
                instruction(VirInstruction::Load {
                    result: word(6),
                    pointer: VirValueId::new(4),
                    permission: VirValueId::new(5),
                    access: nera::VirMemoryAccess::core_u64(),
                }),
                instruction(VirInstruction::Free {
                    pointer: VirValueId::new(4),
                    permission: VirValueId::new(5),
                }),
            ],
            Vec::new(),
        ),
    );
    let program = configured(validated(vec![caller, callee]), |unit| {
        let origin = function_origin(unit, VirFunctionId::new(1));
        add_own_word(
            &mut unit.specs,
            VirContractId::new(1),
            VirContractPosition::Requires,
            origin,
            0,
            0,
            1,
            VirContractInitialization::Initialized,
        );
        add_own_word(
            &mut unit.specs,
            VirContractId::new(1),
            VirContractPosition::Ensures,
            origin,
            0,
            0,
            1,
            VirContractInitialization::Initialized,
        );
    });

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("modular call must analyze");

    assert!(verification.is_memory_checked_core0());
    let caller = verification
        .functions()
        .get(&VirFunctionId::new(0))
        .expect("caller result");
    assert!(caller.cfg().obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::CallContractPrecondition { .. }
        ) && matches!(record.location(), VirLocation::CallEdge { .. })
    }));
}

#[test]
fn recursive_call_uses_its_registered_contract_without_inlining() {
    let signature = VirSignature {
        parameters: Vec::new(),
        results: Vec::new(),
    };
    let recursive = function(
        0,
        "recursive",
        signature.clone(),
        0,
        block(
            Vec::new(),
            vec![instruction(VirInstruction::Call {
                results: Vec::new(),
                target: VirCallTarget {
                    symbol: "recursive".to_owned(),
                    signature: signature.clone(),
                    contract: VirContractId::new(0),
                    abi: None,
                },
                arguments: Vec::new(),
            })],
            Vec::new(),
        ),
    );
    let program = validated(vec![recursive]);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("a closed recursive contract is checked modularly");

    assert!(verification.is_memory_checked_core0());
    assert!(verification.diagnostics().is_empty());
    assert!(
        verification.functions()[&VirFunctionId::new(0)]
            .cfg()
            .all_obligations_proven()
    );
}

#[test]
fn fresh_summary_resources_are_alpha_renamed_per_call_site() {
    let allocator_signature = VirSignature {
        parameters: Vec::new(),
        results: vec![
            VirType::Pointer {
                access: nera::VirMemoryAccess::core_u64(),
            },
            VirType::Permission,
        ],
    };
    let caller_signature = VirSignature {
        parameters: Vec::new(),
        results: Vec::new(),
    };
    let allocator = function(
        1,
        "make",
        allocator_signature.clone(),
        1,
        block(
            Vec::new(),
            vec![
                instruction(VirInstruction::Constant {
                    result: word(0),
                    value: VirConstant::U64(8),
                }),
                instruction(VirInstruction::Allocate {
                    pointer_result: pointer(1),
                    permission_result: permission(2),
                    size_bytes: VirValueId::new(0),
                    alignment: 8,
                    region: VirRegionId::new(0),
                    element: nera::VirMemoryAccess::core_u64(),
                }),
                instruction(VirInstruction::Constant {
                    result: word(3),
                    value: VirConstant::U64(1),
                }),
                instruction(VirInstruction::Initialize {
                    pointer: VirValueId::new(1),
                    value: VirValueId::new(3),
                    permission: VirValueId::new(2),
                    access: nera::VirMemoryAccess::core_u64(),
                }),
            ],
            vec![VirValueId::new(1), VirValueId::new(2)],
        ),
    );
    let call_target = VirCallTarget {
        symbol: "make".to_owned(),
        signature: allocator_signature.clone(),
        contract: VirContractId::new(1),
        abi: None,
    };
    let caller = function(
        0,
        "caller",
        caller_signature.clone(),
        0,
        block(
            Vec::new(),
            vec![
                instruction(VirInstruction::Call {
                    results: vec![pointer(0), permission(1)],
                    target: call_target.clone(),
                    arguments: Vec::new(),
                }),
                instruction(VirInstruction::Call {
                    results: vec![pointer(2), permission(3)],
                    target: call_target,
                    arguments: Vec::new(),
                }),
                instruction(VirInstruction::Free {
                    pointer: VirValueId::new(0),
                    permission: VirValueId::new(1),
                }),
                instruction(VirInstruction::Free {
                    pointer: VirValueId::new(2),
                    permission: VirValueId::new(3),
                }),
            ],
            Vec::new(),
        ),
    );
    let program = configured(validated(vec![caller, allocator]), |unit| {
        let origin = function_origin(unit, VirFunctionId::new(1));
        add_own_word(
            &mut unit.specs,
            VirContractId::new(1),
            VirContractPosition::Ensures,
            origin,
            0,
            0,
            1,
            VirContractInitialization::Initialized,
        );
    });

    let analysis = analyze_function_cfg_with_config(
        &program.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
        CfgAnalysisConfig::default(),
    )
    .expect("caller analysis must succeed");

    assert!(analysis.all_obligations_proven());
    let exit = analysis
        .block(VirBlockId::new(0))
        .expect("entry block")
        .exit_state();
    let AbstractValue::Pointer(first) = exit.value(VirValueId::new(0)).copied().expect("first")
    else {
        panic!("first result must be a pointer")
    };
    let AbstractValue::Pointer(second) = exit.value(VirValueId::new(2)).copied().expect("second")
    else {
        panic!("second result must be a pointer")
    };
    assert_ne!(first.provenance(), second.provenance());
}

#[test]
fn missing_mutable_borrow_fact_produces_actionable_diagnostic() {
    let signature = VirSignature {
        parameters: vec![
            VirType::Pointer {
                access: nera::VirMemoryAccess::core_u64(),
            },
            VirType::Permission,
        ],
        results: Vec::new(),
    };
    let program = validated(vec![function(
        0,
        "bad_store",
        signature.clone(),
        0,
        block(
            vec![pointer(0), permission(1)],
            vec![
                instruction(VirInstruction::Constant {
                    result: word(2),
                    value: VirConstant::U64(4),
                }),
                instruction(VirInstruction::Store {
                    pointer: VirValueId::new(0),
                    value: VirValueId::new(2),
                    permission: VirValueId::new(1),
                    access: nera::VirMemoryAccess::core_u64(),
                }),
            ],
            Vec::new(),
        ),
    )]);
    let program = configured(program, |unit| {
        let origin = function_origin(unit, VirFunctionId::new(0));
        add_resource_clause(
            &mut unit.specs,
            VirContractId::new(0),
            VirContractPosition::Requires,
            origin,
            true,
            0,
            VirRegionId::new(0),
            8,
            8,
            VirContractLiveness::Live,
            VirContractOwnership::Unowned,
            VirContractInitialization::Initialized,
            &[PointerFact {
                slot: 0,
                lower: 0,
                upper: 0,
                alignment: 8,
            }],
            &[PermissionFact {
                slot: 1,
                start: 0,
                end: 8,
                access: VirContractAccess::Read,
                free: VirContractFree::No,
            }],
        );
    });

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("verification must return diagnostics");

    assert!(!verification.is_memory_checked_core0());
    let diagnostic = verification
        .diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.message().contains("permits mutation"))
        .expect("write permission diagnostic");
    assert_eq!(diagnostic.kind(), VerifierDiagnosticKind::RefutedObligation);
    assert_eq!(diagnostic.source_span(), span());
    assert!(
        diagnostic
            .suggestion()
            .expect("contract suggestion")
            .contains("mutable borrow")
    );
}

#[test]
fn call_requires_is_checked_against_the_callers_actual_borrow() {
    let signature = VirSignature {
        parameters: vec![
            VirType::Pointer {
                access: nera::VirMemoryAccess::core_u64(),
            },
            VirType::Permission,
        ],
        results: Vec::new(),
    };
    let callee = function(
        1,
        "mutate",
        signature.clone(),
        1,
        block(vec![pointer(0), permission(1)], Vec::new(), Vec::new()),
    );
    let caller = function(
        0,
        "caller",
        signature.clone(),
        0,
        block(
            vec![pointer(0), permission(1)],
            vec![instruction(VirInstruction::Call {
                results: Vec::new(),
                target: VirCallTarget {
                    symbol: "mutate".to_owned(),
                    signature: signature.clone(),
                    contract: VirContractId::new(1),
                    abi: None,
                },
                arguments: vec![VirValueId::new(0), VirValueId::new(1)],
            })],
            Vec::new(),
        ),
    );
    let program = configured(validated(vec![caller, callee]), |unit| {
        for (function, access) in [
            (VirFunctionId::new(0), VirContractAccess::Read),
            (VirFunctionId::new(1), VirContractAccess::Write),
        ] {
            let origin = function_origin(unit, function);
            add_resource_clause(
                &mut unit.specs,
                VirContractId::new(function.get()),
                VirContractPosition::Requires,
                origin,
                true,
                0,
                VirRegionId::new(0),
                8,
                8,
                VirContractLiveness::Live,
                VirContractOwnership::Unowned,
                VirContractInitialization::Initialized,
                &[PointerFact {
                    slot: 0,
                    lower: 0,
                    upper: 0,
                    alignment: 8,
                }],
                &[PermissionFact {
                    slot: 1,
                    start: 0,
                    end: 8,
                    access,
                    free: VirContractFree::No,
                }],
            );
        }
    });

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("closed program must produce a verification result");

    assert!(!verification.is_memory_checked_core0());
    assert!(verification.diagnostics().iter().any(|diagnostic| {
        diagnostic
            .message()
            .contains("call satisfies contract1 `requires` clause 1")
            && diagnostic
                .suggestion()
                .is_some_and(|suggestion| suggestion.contains("establish contract1"))
    }));
}

#[test]
fn explicit_clause_origins_remain_typed_and_auditable() {
    let signature = VirSignature {
        parameters: vec![VirType::U64, VirType::U64, VirType::U64],
        results: Vec::new(),
    };
    let program = configured(
        validated(vec![function(
            0,
            "sources",
            signature.clone(),
            0,
            block(vec![word(0), word(1), word(2)], Vec::new(), Vec::new()),
        )]),
        |unit| {
            let origin = function_origin(unit, VirFunctionId::new(0));
            for slot in 0..3 {
                add_u64_range(
                    &mut unit.specs,
                    VirContractId::new(0),
                    VirContractPosition::Requires,
                    origin,
                    slot,
                    slot as u64,
                    slot as u64,
                );
            }
        },
    );

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("fact sources must be accepted and reported");

    assert!(verification.is_memory_checked_core0());
    assert!(verification.trust_report().entries().is_empty());
}

#[test]
fn violated_ensures_clause_is_checked_at_each_return() {
    let signature = VirSignature {
        parameters: vec![VirType::Bool],
        results: vec![VirType::U64],
    };
    let program = configured(
        VirUnit::from_runtime(
            nera::VirMemorySchema::core_u64(),
            VirFunctionId::new(0),
            vec![VirFunction {
                id: VirFunctionId::new(0),
                name: "wrong_result".to_owned(),
                signature: signature.clone(),
                contract: VirContractId::new(0),
                entry: VirBlockId::new(0),
                blocks: vec![
                    VirBasicBlock {
                        id: VirBlockId::new(0),
                        parameters: vec![value(0, VirType::Bool)],
                        instructions: Vec::new(),
                        terminator: SpannedVirTerminator {
                            terminator: VirTerminator::Branch {
                                condition: VirValueId::new(0),
                                then_target: VirBlockTarget {
                                    block: VirBlockId::new(1),
                                    arguments: Vec::new(),
                                },
                                else_target: VirBlockTarget {
                                    block: VirBlockId::new(2),
                                    arguments: Vec::new(),
                                },
                            },
                            source_span: span(),
                        },
                        source_span: span(),
                    },
                    VirBasicBlock {
                        id: VirBlockId::new(1),
                        parameters: Vec::new(),
                        instructions: vec![instruction(VirInstruction::Constant {
                            result: word(1),
                            value: VirConstant::U64(2),
                        })],
                        terminator: SpannedVirTerminator {
                            terminator: VirTerminator::Return {
                                values: vec![VirValueId::new(1)],
                            },
                            source_span: span(),
                        },
                        source_span: span(),
                    },
                    VirBasicBlock {
                        id: VirBlockId::new(2),
                        parameters: Vec::new(),
                        instructions: vec![instruction(VirInstruction::Constant {
                            result: word(2),
                            value: VirConstant::U64(3),
                        })],
                        terminator: SpannedVirTerminator {
                            terminator: VirTerminator::Return {
                                values: vec![VirValueId::new(2)],
                            },
                            source_span: span(),
                        },
                        source_span: span(),
                    },
                ],
                source_span: span(),
            }],
        )
        .into_validated()
        .expect("two-return program validates"),
        |unit| {
            let origin = function_origin(unit, VirFunctionId::new(0));
            add_u64_range(
                &mut unit.specs,
                VirContractId::new(0),
                VirContractPosition::Ensures,
                origin,
                0,
                1,
                1,
            );
        },
    );

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("postcondition checking must run");

    assert!(!verification.is_memory_checked_core0());
    assert_eq!(verification.diagnostics().len(), 2);
    assert_eq!(
        verification.diagnostics()[0].kind(),
        VerifierDiagnosticKind::RefutedPostcondition
    );
    assert!(verification.diagnostics()[0].message().contains("clause 0"));
    let finding = verification.diagnostics()[0].finding();
    assert_eq!(
        finding.site(),
        VerifierFindingSite::Spec {
            location: VirSpecLocation::FunctionResult {
                function: VirFunctionId::new(0),
            },
            entity: VerifierSpecEntity::Clause(VirSpecClauseId::new(0)),
            occurrence: Some(VirLocation::Terminator {
                function: VirFunctionId::new(0),
                block: VirBlockId::new(1),
            }),
        }
    );
    let second = verification.diagnostics()[1].finding();
    assert_eq!(finding.origin(), second.origin());
    assert_eq!(finding.source_position(), second.source_position());
    assert_ne!(finding.site(), second.site());
    assert_eq!(
        second.occurrence(),
        Some(VirLocation::Terminator {
            function: VirFunctionId::new(0),
            block: VirBlockId::new(2),
        })
    );
    let replay = verify_program(
        &program.resolve().expect("replay input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("postcondition replay");
    assert_eq!(verification, replay);
}

#[test]
fn unresolved_contract_ids_fail_closed_before_cfg_analysis() {
    let signature = VirSignature {
        parameters: Vec::new(),
        results: Vec::new(),
    };
    let unit = VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![function(
            0,
            "missing",
            signature,
            9,
            block(Vec::new(), Vec::new(), Vec::new()),
        )],
    );

    assert!(matches!(
        unit.into_validated()
            .expect_err("contract IDs must be dense")
            .kind(),
        VirValidationErrorKind::NonDenseContractId { .. }
    ));
}

#[test]
fn contract_checks_keep_proven_refuted_and_unknown_distinct() {
    assert_ne!(ObligationStatus::Proven, ObligationStatus::Refuted);
    assert_ne!(ObligationStatus::Proven, ObligationStatus::Unknown);
    assert_ne!(ObligationStatus::Refuted, ObligationStatus::Unknown);
}
