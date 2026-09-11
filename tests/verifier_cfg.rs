use nera::{
    AbstractAllocationId, AbstractValue, ByteSpan, CfgAnalysisConfig, CfgAnalysisError,
    CfgObligationOrigin, LivenessState, ObligationStatus, PermissionAvailability,
    ResourceObligationKind, ResourceState, SpannedVirInstruction, SpannedVirTerminator,
    U64Interval, ValidatedVirUnit, VirBasicBlock, VirBlockId, VirBlockTarget, VirConstant,
    VirContractId, VirFunction, VirFunctionId, VirInstruction, VirIntegerPredicate, VirRegionId,
    VirSignature, VirTerminator, VirType, VirUnit, VirValue, VirValueId, analyze_function_cfg,
    analyze_function_cfg_with_entry,
};

fn span() -> ByteSpan {
    ByteSpan::new(0, 100).expect("valid test span")
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

fn boolean(id: u32) -> VirValue {
    value(id, VirType::Bool)
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

fn terminator(terminator: VirTerminator) -> SpannedVirTerminator {
    SpannedVirTerminator {
        terminator,
        source_span: span(),
    }
}

fn target(block: u32, arguments: &[u32]) -> VirBlockTarget {
    VirBlockTarget {
        block: VirBlockId::new(block),
        arguments: arguments.iter().copied().map(VirValueId::new).collect(),
    }
}

fn block(
    id: u32,
    parameters: Vec<VirValue>,
    instructions: Vec<SpannedVirInstruction>,
    end: VirTerminator,
) -> VirBasicBlock {
    VirBasicBlock {
        id: VirBlockId::new(id),
        parameters,
        instructions,
        terminator: terminator(end),
        source_span: span(),
    }
}

fn validated(
    parameters: Vec<VirType>,
    results: Vec<VirType>,
    blocks: Vec<VirBasicBlock>,
) -> ValidatedVirUnit {
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "test".to_owned(),
            signature: VirSignature {
                parameters,
                results,
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks,
            source_span: span(),
        }],
    )
    .into_validated()
    .expect("test VIR must be structurally valid")
}

#[test]
fn branch_comparison_facts_are_renamed_and_rechecked_on_both_edges() {
    let program = validated(
        vec![VirType::U64, VirType::U64],
        Vec::new(),
        vec![
            block(
                0,
                vec![word(0), word(1)],
                vec![instruction(VirInstruction::Compare {
                    result: boolean(2),
                    predicate: VirIntegerPredicate::LessThan,
                    left: VirValueId::new(0),
                    right: VirValueId::new(1),
                })],
                VirTerminator::Branch {
                    condition: VirValueId::new(2),
                    then_target: target(1, &[0, 1, 2]),
                    else_target: target(2, &[0, 1, 2]),
                },
            ),
            block(
                1,
                vec![word(10), word(11), boolean(12)],
                vec![
                    instruction(VirInstruction::Compare {
                        result: boolean(13),
                        predicate: VirIntegerPredicate::LessThan,
                        left: VirValueId::new(10),
                        right: VirValueId::new(11),
                    }),
                    instruction(VirInstruction::Check {
                        condition: VirValueId::new(13),
                    }),
                ],
                VirTerminator::Return { values: Vec::new() },
            ),
            block(
                2,
                vec![word(20), word(21), boolean(22)],
                vec![
                    instruction(VirInstruction::Compare {
                        result: boolean(23),
                        predicate: VirIntegerPredicate::GreaterOrEqual,
                        left: VirValueId::new(20),
                        right: VirValueId::new(21),
                    }),
                    instruction(VirInstruction::Check {
                        condition: VirValueId::new(23),
                    }),
                ],
                VirTerminator::Return { values: Vec::new() },
            ),
        ],
    );

    let analysis = analyze_function_cfg(
        &program.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("valid CFG analysis must converge");

    assert!(analysis.all_obligations_proven());
    assert_eq!(analysis.returns().len(), 2);
    assert_eq!(
        analysis
            .obligations()
            .iter()
            .filter(|record| matches!(
                record.obligation().kind(),
                ResourceObligationKind::CheckTrue { .. }
            ))
            .count(),
        2
    );
    assert_eq!(
        analysis,
        analyze_function_cfg(
            &program.resolve().expect("analysis input resolves"),
            VirFunctionId::new(0)
        )
        .expect("analysis must be deterministic")
    );
}

#[test]
fn diamond_cfg_preserves_initialized_memory_and_linear_permissions() {
    let program = validated(
        vec![VirType::Bool],
        vec![VirType::U64],
        vec![
            block(
                0,
                vec![boolean(0)],
                vec![
                    instruction(VirInstruction::Constant {
                        result: word(1),
                        value: VirConstant::U64(8),
                    }),
                    instruction(VirInstruction::Allocate {
                        pointer_result: pointer(2),
                        permission_result: permission(3),
                        size_bytes: VirValueId::new(1),
                        alignment: 8,
                        region: VirRegionId::new(0),
                        element: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(4),
                        value: VirConstant::U64(7),
                    }),
                    instruction(VirInstruction::Initialize {
                        pointer: VirValueId::new(2),
                        value: VirValueId::new(4),
                        permission: VirValueId::new(3),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                ],
                VirTerminator::Branch {
                    condition: VirValueId::new(0),
                    then_target: target(1, &[2, 3, 4]),
                    else_target: target(2, &[2, 3, 4]),
                },
            ),
            block(
                1,
                vec![pointer(10), permission(11), word(12)],
                vec![instruction(VirInstruction::Write {
                    pointer: VirValueId::new(10),
                    value: VirValueId::new(12),
                    permission: VirValueId::new(11),
                    access: nera::VirMemoryAccess::core_u64(),
                })],
                VirTerminator::Jump {
                    target: target(3, &[10, 11]),
                },
            ),
            block(
                2,
                vec![pointer(20), permission(21), word(22)],
                vec![instruction(VirInstruction::Store {
                    pointer: VirValueId::new(20),
                    value: VirValueId::new(22),
                    permission: VirValueId::new(21),
                    access: nera::VirMemoryAccess::core_u64(),
                })],
                VirTerminator::Jump {
                    target: target(3, &[20, 21]),
                },
            ),
            block(
                3,
                vec![pointer(30), permission(31)],
                vec![
                    instruction(VirInstruction::Load {
                        result: word(32),
                        pointer: VirValueId::new(30),
                        permission: VirValueId::new(31),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Free {
                        pointer: VirValueId::new(30),
                        permission: VirValueId::new(31),
                    }),
                ],
                VirTerminator::Return {
                    values: vec![VirValueId::new(32)],
                },
            ),
        ],
    );

    let analysis = analyze_function_cfg(
        &program.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("diamond analysis must converge");

    assert!(analysis.all_obligations_proven());
    assert_eq!(analysis.returns().len(), 1);
    let exit = analysis
        .block(VirBlockId::new(3))
        .expect("exit block analysis");
    let allocation = exit
        .exit_state()
        .allocation(AbstractAllocationId::vir_allocation_site(VirValueId::new(
            2,
        )))
        .expect("allocation remains tracked after free");
    assert_eq!(allocation.liveness(), LivenessState::Dead);
}

#[test]
fn cfg_edges_and_returns_enforce_linear_permission_moves() {
    let duplicate_edge = validated(
        vec![VirType::Permission],
        Vec::new(),
        vec![
            block(
                0,
                vec![permission(0)],
                Vec::new(),
                VirTerminator::Jump {
                    target: target(1, &[0, 0]),
                },
            ),
            block(
                1,
                vec![permission(10), permission(11)],
                Vec::new(),
                VirTerminator::Return { values: Vec::new() },
            ),
        ],
    );
    let edge = analyze_function_cfg(
        &duplicate_edge.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("duplicate permission is an obligation");
    assert!(!edge.all_obligations_proven());
    assert!(edge.returns().is_empty());
    assert!(edge.obligations().iter().any(|record| {
        record.block() == VirBlockId::new(0)
            && record.origin()
                == CfgObligationOrigin::Jump {
                    target: VirBlockId::new(1),
                }
            && matches!(
                record.obligation().kind(),
                ResourceObligationKind::PermissionOperandsDistinct { .. }
            )
            && record.obligation().status() == ObligationStatus::Refuted
            && record.location()
                == nera::VirLocation::Terminator {
                    function: VirFunctionId::new(0),
                    block: VirBlockId::new(0),
                }
    }));

    let permission_return = validated(
        vec![VirType::Permission],
        vec![VirType::Permission],
        vec![block(
            0,
            vec![permission(0)],
            Vec::new(),
            VirTerminator::Return {
                values: vec![VirValueId::new(0)],
            },
        )],
    );
    let returned = analyze_function_cfg(
        &permission_return
            .resolve()
            .expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("permission return must transfer");
    assert!(returned.all_obligations_proven());
    let AbstractValue::Permission(returned_permission) = returned.returns()[0].values()[0] else {
        panic!("expected returned permission fact");
    };
    assert_eq!(
        returned_permission.availability(),
        PermissionAvailability::Available
    );
    let AbstractValue::Permission(local) = returned.returns()[0]
        .state()
        .value(VirValueId::new(0))
        .copied()
        .expect("local permission fact")
    else {
        panic!("expected local permission fact");
    };
    assert_eq!(local.availability(), PermissionAvailability::Consumed);

    let duplicate_return = validated(
        vec![VirType::Permission],
        vec![VirType::Permission, VirType::Permission],
        vec![block(
            0,
            vec![permission(0)],
            Vec::new(),
            VirTerminator::Return {
                values: vec![VirValueId::new(0), VirValueId::new(0)],
            },
        )],
    );
    let duplicate = analyze_function_cfg(
        &duplicate_return.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("duplicate permission return is an obligation");
    assert!(!duplicate.all_obligations_proven());
    assert!(duplicate.returns().is_empty());
}

#[test]
fn loop_widening_converges_without_silently_assuming_memory_safety() {
    let program = widening_memory_loop();

    let analysis = analyze_function_cfg(
        &program.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("default widening must converge");

    assert!(analysis.loop_blocks().contains(&VirBlockId::new(1)));
    assert!(analysis.widened_blocks().contains(&VirBlockId::new(1)));
    assert!(!analysis.all_obligations_proven());
    assert!(analysis.obligations().iter().any(|record| {
        record.block() == VirBlockId::new(1)
            && matches!(
                record.obligation().kind(),
                ResourceObligationKind::AccessWithinBounds { .. }
            )
            && record.obligation().status() == ObligationStatus::Unknown
    }));
    let AbstractValue::U64(offset) = analysis
        .block(VirBlockId::new(1))
        .expect("loop block")
        .entry_state()
        .value(VirValueId::new(12))
        .copied()
        .expect("loop offset")
    else {
        panic!("expected loop offset interval");
    };
    assert_eq!(offset, U64Interval::unknown());
    assert!(analysis.block_visits() < CfgAnalysisConfig::default().max_block_visits);
}

#[test]
fn allocation_site_inside_a_loop_is_reanalyzed_as_a_fresh_instance() {
    let program = validated(
        vec![VirType::Bool],
        Vec::new(),
        vec![
            block(
                0,
                vec![boolean(0)],
                vec![
                    instruction(VirInstruction::Constant {
                        result: word(1),
                        value: VirConstant::U64(8),
                    }),
                    instruction(VirInstruction::Allocate {
                        pointer_result: pointer(2),
                        permission_result: permission(3),
                        size_bytes: VirValueId::new(1),
                        alignment: 8,
                        region: VirRegionId::new(0),
                        element: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(4),
                        value: VirConstant::U64(1),
                    }),
                    instruction(VirInstruction::Initialize {
                        pointer: VirValueId::new(2),
                        value: VirValueId::new(4),
                        permission: VirValueId::new(3),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Free {
                        pointer: VirValueId::new(2),
                        permission: VirValueId::new(3),
                    }),
                ],
                VirTerminator::Branch {
                    condition: VirValueId::new(0),
                    then_target: target(0, &[0]),
                    else_target: target(1, &[]),
                },
            ),
            block(
                1,
                Vec::new(),
                Vec::new(),
                VirTerminator::Return { values: Vec::new() },
            ),
        ],
    );

    let analysis = analyze_function_cfg(
        &program.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("loop-local allocation site must not collide across iterations");

    assert!(analysis.all_obligations_proven());
    assert!(analysis.loop_blocks().contains(&VirBlockId::new(0)));
    assert_eq!(analysis.returns().len(), 1);
}

#[test]
fn every_block_in_a_multi_block_cycle_exposes_an_inferred_entry_invariant() {
    let program = validated(
        vec![VirType::Bool],
        Vec::new(),
        vec![
            block(
                0,
                vec![boolean(0)],
                Vec::new(),
                VirTerminator::Branch {
                    condition: VirValueId::new(0),
                    then_target: target(1, &[0]),
                    else_target: target(2, &[]),
                },
            ),
            block(
                1,
                vec![boolean(10)],
                Vec::new(),
                VirTerminator::Jump {
                    target: target(0, &[10]),
                },
            ),
            block(
                2,
                Vec::new(),
                Vec::new(),
                VirTerminator::Return { values: Vec::new() },
            ),
        ],
    );

    let analysis = analyze_function_cfg(
        &program.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("multi-block loop must converge");

    assert_eq!(
        analysis.loop_blocks(),
        &[VirBlockId::new(0), VirBlockId::new(1)]
            .into_iter()
            .collect()
    );
    assert!(
        analysis
            .block(VirBlockId::new(0))
            .expect("first loop block")
            .is_loop_block()
    );
    assert!(
        analysis
            .block(VirBlockId::new(1))
            .expect("second loop block")
            .is_loop_block()
    );
}

#[test]
fn analysis_budget_exhaustion_fails_closed_when_widening_is_disabled() {
    let program = widening_memory_loop();
    let error = analyze_function_cfg_with_entry(
        &program.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
        &ResourceState::new(),
        CfgAnalysisConfig {
            max_block_visits: 4,
            widen_after_updates: u32::MAX,
            ..CfgAnalysisConfig::default()
        },
    )
    .expect_err("an unbounded interval chain must hit the explicit budget");

    assert_eq!(
        error,
        CfgAnalysisError::BlockVisitLimitExceeded { limit: 4 }
    );
}

fn widening_memory_loop() -> ValidatedVirUnit {
    validated(
        vec![VirType::Bool],
        Vec::new(),
        vec![
            block(
                0,
                vec![boolean(0)],
                vec![
                    instruction(VirInstruction::Constant {
                        result: word(1),
                        value: VirConstant::U64(8),
                    }),
                    instruction(VirInstruction::Allocate {
                        pointer_result: pointer(2),
                        permission_result: permission(3),
                        size_bytes: VirValueId::new(1),
                        alignment: 8,
                        region: VirRegionId::new(0),
                        element: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(4),
                        value: VirConstant::U64(0),
                    }),
                ],
                VirTerminator::Jump {
                    target: target(1, &[2, 3, 4, 0]),
                },
            ),
            block(
                1,
                vec![pointer(10), permission(11), word(12), boolean(13)],
                vec![
                    instruction(VirInstruction::PointerOffset {
                        result: pointer(14),
                        base: VirValueId::new(10),
                        delta_bytes: VirValueId::new(12),
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(15),
                        value: VirConstant::U64(1),
                    }),
                    instruction(VirInstruction::Write {
                        pointer: VirValueId::new(14),
                        value: VirValueId::new(15),
                        permission: VirValueId::new(11),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(16),
                        value: VirConstant::U64(8),
                    }),
                    instruction(VirInstruction::WordAdd {
                        result: word(17),
                        left: VirValueId::new(12),
                        right: VirValueId::new(16),
                    }),
                ],
                VirTerminator::Branch {
                    condition: VirValueId::new(13),
                    then_target: target(1, &[10, 11, 17, 13]),
                    else_target: target(2, &[10, 11]),
                },
            ),
            block(
                2,
                vec![pointer(20), permission(21)],
                vec![instruction(VirInstruction::Free {
                    pointer: VirValueId::new(20),
                    permission: VirValueId::new(21),
                })],
                VirTerminator::Return { values: Vec::new() },
            ),
        ],
    )
}
