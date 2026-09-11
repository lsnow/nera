use nera::{
    ByteSpan, CfgAnalysisConfig, ObligationStatus, ResourceObligationKind, SpannedVirInstruction,
    SpannedVirTerminator, ValidatedVirUnit, VerifierFindingSite, VirBasicBlock, VirBlockId,
    VirCallTarget, VirConstant, VirContractAccess, VirContractFree, VirContractId,
    VirContractInitialization, VirContractLiveness, VirContractOwnership, VirContractPosition,
    VirFunction, VirFunctionId, VirInstruction, VirRegionId, VirSignature, VirTerminator, VirType,
    VirUnit, VirValidationErrorKind, VirValue, VirValueId, verify_program,
};

#[path = "support/address_program.rs"]
mod address_program;

#[path = "support/contract_builder.rs"]
mod contract_builder;

use contract_builder::{
    PermissionFact, PointerFact, add_resource_clause, add_u64_range, function_origin,
};

#[test]
fn typed_address_program_proves_bounds_alignment_liveness_and_nominal_identity() {
    let validated = address_program::validated();
    let verified = verify_program(
        &validated.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("typed address verification completes");
    assert!(verified.is_memory_checked_core0());
    let repeated = verify_program(
        &validated.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("typed address verification repeats");
    assert_eq!(
        repeated, verified,
        "obligation order and result are deterministic"
    );
    let obligations = verified.functions()[&VirFunctionId::new(0)]
        .cfg()
        .obligations();
    assert!(obligations.iter().any(|record| matches!(
        record.obligation().kind(),
        ResourceObligationKind::IndexWithinBounds { .. }
    )));
    assert!(obligations.iter().any(|record| matches!(
        record.obligation().kind(),
        ResourceObligationKind::PointerMemoryAccessMatches { .. }
    )));

    let mut unsafe_index = validated.as_unit().clone();
    let VirInstruction::Constant { value, .. } =
        &mut unsafe_index.runtime.functions[0].blocks[0].instructions[3].instruction
    else {
        panic!("index constant fixture")
    };
    *value = VirConstant::U64(4);
    let unsafe_index = unsafe_index
        .into_validated()
        .expect("dynamic index mutation remains structural VIR");
    let rejected = verify_program(
        &unsafe_index.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("unsafe index is a refuted obligation, not a transfer failure");
    assert!(!rejected.is_memory_checked_core0());
    assert!(!rejected.diagnostics().is_empty());
    for diagnostic in rejected.diagnostics() {
        let finding = diagnostic.finding();
        let VerifierFindingSite::Runtime(location) = finding.site() else {
            panic!("resource obligation must publish a runtime finding")
        };
        let canonical = unsafe_index
            .as_unit()
            .source_map
            .origin_at(location)
            .expect("validated finding location has an origin");
        assert_eq!(finding.origin(), canonical.id);
        assert_eq!(
            finding.source_position(),
            unsafe_index
                .as_unit()
                .source_map
                .source_span(location)
                .expect("validated finding location resolves")
        );
    }
    assert!(
        rejected.functions()[&VirFunctionId::new(0)]
            .cfg()
            .obligations()
            .iter()
            .any(|record| matches!(
                record.obligation().kind(),
                ResourceObligationKind::IndexWithinBounds { .. }
            ) && record.obligation().status() == ObligationStatus::Refuted)
    );

    let mut wrong_owner = validated.as_unit().clone();
    let VirInstruction::Allocate { element, .. } =
        &mut wrong_owner.runtime.functions[0].blocks[0].instructions[1].instruction
    else {
        panic!("allocation fixture")
    };
    *element = address_program::ARRAY_ACCESS;
    assert!(matches!(
        wrong_owner
            .validate()
            .expect_err("pointer and allocation access must agree")
            .kind(),
        VirValidationErrorKind::TypeMismatch {
            context: "allocation pointer result",
            ..
        }
    ));

    let mut skipped_index = validated.as_unit().clone();
    let VirInstruction::Write { pointer, .. } =
        &mut skipped_index.runtime.functions[0].blocks[0].instructions[6].instruction
    else {
        panic!("typed write fixture")
    };
    *pointer = VirValueId::new(3);
    assert!(matches!(
        skipped_index
            .validate()
            .expect_err("leaf access requires a leaf pointer type")
            .kind(),
        VirValidationErrorKind::TypeMismatch {
            context: "write pointer",
            ..
        }
    ));

    let mut consumed_permission = validated.as_unit().clone();
    let write_span = consumed_permission.runtime.functions[0].blocks[0].instructions[6].source_span;
    consumed_permission.runtime.functions[0].blocks[0]
        .instructions
        .insert(
            6,
            SpannedVirInstruction {
                instruction: VirInstruction::PermissionMove {
                    result: permission(8),
                    source: VirValueId::new(2),
                },
                source_span: write_span,
            },
        );
    consumed_permission.rebuild_source_map_from_runtime("<verifier-case-mutation>", 1);
    let rejected = verify_program(
        &consumed_permission
            .into_validated()
            .expect("consumed permission mutation remains structural VIR")
            .resolve()
            .expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("missing permission is a refuted obligation");
    assert!(
        rejected.functions()[&VirFunctionId::new(0)]
            .cfg()
            .obligations()
            .iter()
            .any(|record| matches!(
                record.obligation().kind(),
                ResourceObligationKind::PermissionAvailable { permission }
                    if permission == VirValueId::new(2)
            ) && record.obligation().status() == ObligationStatus::Refuted)
    );

    let mut undersized = validated.as_unit().clone();
    let VirInstruction::Constant { value, .. } =
        &mut undersized.runtime.functions[0].blocks[0].instructions[0].instruction
    else {
        panic!("allocation size fixture")
    };
    *value = VirConstant::U64(32);
    let rejected = verify_program(
        &undersized
            .into_validated()
            .expect("dynamic size mutation remains structural VIR")
            .resolve()
            .expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("undersized object is a refuted obligation");
    assert!(
        rejected.functions()[&VirFunctionId::new(0)]
            .cfg()
            .obligations()
            .iter()
            .any(|record| matches!(
                record.obligation().kind(),
                ResourceObligationKind::AddressObjectWithinBounds { .. }
            ) && record.obligation().status() == ObligationStatus::Refuted)
    );

    let mut underaligned = validated.as_unit().clone();
    let VirInstruction::Allocate { alignment, .. } =
        &mut underaligned.runtime.functions[0].blocks[0].instructions[1].instruction
    else {
        panic!("allocation fixture")
    };
    *alignment = 4;
    let rejected = verify_program(
        &underaligned
            .into_validated()
            .expect("alignment mutation remains structural VIR")
            .resolve()
            .expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("misaligned object is a refuted obligation");
    assert!(
        rejected.functions()[&VirFunctionId::new(0)]
            .cfg()
            .obligations()
            .iter()
            .any(|record| matches!(
                record.obligation().kind(),
                ResourceObligationKind::AddressObjectAligned { .. }
            ) && record.obligation().status() == ObligationStatus::Refuted)
    );
}

const REGION: VirRegionId = VirRegionId::new(0);

fn span() -> ByteSpan {
    ByteSpan::new(100, 110).expect("valid test span")
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
    returns: Vec<VirValueId>,
) -> VirBasicBlock {
    VirBasicBlock {
        id: VirBlockId::new(0),
        parameters,
        instructions,
        terminator: SpannedVirTerminator {
            terminator: VirTerminator::Return { values: returns },
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
    body: VirBasicBlock,
) -> VirFunction {
    VirFunction {
        id: VirFunctionId::new(id),
        name: name.to_owned(),
        signature,
        contract: VirContractId::new(contract),
        entry: VirBlockId::new(0),
        blocks: vec![body],
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
    .expect("case VIR must be structurally valid")
}

fn configured(program: ValidatedVirUnit, configure: impl FnOnce(&mut VirUnit)) -> ValidatedVirUnit {
    let mut unit = program.as_unit().clone();
    configure(&mut unit);
    unit.into_validated().expect("configured verifier case")
}

fn dynamic_slice_case(use_overlapping_permission: bool) -> ValidatedVirUnit {
    let signature = VirSignature {
        parameters: vec![
            VirType::Pointer {
                access: nera::VirMemoryAccess::core_u64(),
            },
            VirType::Permission,
            VirType::U64,
        ],
        results: Vec::new(),
    };
    let mut instructions = vec![
        instruction(VirInstruction::WordAdd {
            result: word(3),
            left: VirValueId::new(2),
            right: VirValueId::new(2),
        }),
        instruction(VirInstruction::WordAdd {
            result: word(4),
            left: VirValueId::new(3),
            right: VirValueId::new(3),
        }),
        instruction(VirInstruction::WordAdd {
            result: word(5),
            left: VirValueId::new(4),
            right: VirValueId::new(4),
        }),
        instruction(VirInstruction::PermissionSplit {
            left_result: permission(6),
            right_result: permission(7),
            source: VirValueId::new(1),
            split_at_bytes: VirValueId::new(5),
        }),
        instruction(VirInstruction::PointerOffset {
            result: pointer(8),
            base: VirValueId::new(0),
            delta_bytes: VirValueId::new(5),
        }),
        instruction(VirInstruction::Load {
            result: word(9),
            pointer: VirValueId::new(0),
            permission: if use_overlapping_permission {
                VirValueId::new(7)
            } else {
                VirValueId::new(6)
            },
            access: nera::VirMemoryAccess::core_u64(),
        }),
        instruction(VirInstruction::Load {
            result: word(10),
            pointer: VirValueId::new(8),
            permission: VirValueId::new(7),
            access: nera::VirMemoryAccess::core_u64(),
        }),
    ];
    if !use_overlapping_permission {
        instructions.push(instruction(VirInstruction::PermissionJoin {
            result: permission(11),
            left: VirValueId::new(6),
            right: VirValueId::new(7),
        }));
    }
    let program = validated(vec![function(
        0,
        "dynamic_split",
        signature.clone(),
        0,
        block(
            vec![pointer(0), permission(1), word(2)],
            instructions,
            Vec::new(),
        ),
    )]);
    configured(program, |unit| {
        let origin = function_origin(unit, VirFunctionId::new(0));
        add_resource_clause(
            &mut unit.specs,
            VirContractId::new(0),
            VirContractPosition::Requires,
            origin,
            true,
            0,
            REGION,
            32,
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
                end: 32,
                access: VirContractAccess::Write,
                free: VirContractFree::No,
            }],
        );
        add_u64_range(
            &mut unit.specs,
            VirContractId::new(0),
            VirContractPosition::Requires,
            origin,
            2,
            1,
            3,
        );
    })
}

#[test]
fn runtime_index_splits_two_disjoint_slice_permissions() {
    let program = dynamic_slice_case(false);

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("dynamic split case must analyze");

    assert!(verification.is_memory_checked_core0());
    let cfg = verification
        .functions()
        .get(&VirFunctionId::new(0))
        .expect("case function")
        .cfg();
    assert!(cfg.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::PermissionJoinCompatible { .. }
        ) && record.obligation().status() == ObligationStatus::Proven
    }));
}

#[test]
fn dynamic_slice_overlap_mutation_is_refuted() {
    let program = dynamic_slice_case(true);

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("overlap mutation must produce a verifier result");

    assert!(!verification.is_memory_checked_core0());
    assert!(
        verification.functions()[&VirFunctionId::new(0)]
            .cfg()
            .obligations()
            .iter()
            .any(|record| {
                matches!(
                    record.obligation().kind(),
                    ResourceObligationKind::PermissionCoversAccess { .. }
                ) && record.obligation().status() == ObligationStatus::Refuted
            })
    );
}

fn object_pool_case(read_uninitialized: bool) -> ValidatedVirUnit {
    let partition_signature = VirSignature {
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
            VirType::Pointer {
                access: nera::VirMemoryAccess::core_u64(),
            },
            VirType::Permission,
        ],
    };
    let partition = function(
        1,
        "pool_partition",
        partition_signature.clone(),
        1,
        block(
            vec![pointer(0), permission(1)],
            vec![
                instruction(VirInstruction::Constant {
                    result: word(2),
                    value: VirConstant::U64(8),
                }),
                instruction(VirInstruction::PermissionSplit {
                    left_result: permission(3),
                    right_result: permission(4),
                    source: VirValueId::new(1),
                    split_at_bytes: VirValueId::new(2),
                }),
                instruction(VirInstruction::PointerOffset {
                    result: pointer(5),
                    base: VirValueId::new(0),
                    delta_bytes: VirValueId::new(2),
                }),
            ],
            vec![
                VirValueId::new(0),
                VirValueId::new(3),
                VirValueId::new(5),
                VirValueId::new(4),
            ],
        ),
    );
    let caller_signature = VirSignature {
        parameters: Vec::new(),
        results: Vec::new(),
    };
    let mut caller_instructions = vec![
        instruction(VirInstruction::Constant {
            result: word(0),
            value: VirConstant::U64(16),
        }),
        instruction(VirInstruction::Allocate {
            pointer_result: pointer(1),
            permission_result: permission(2),
            size_bytes: VirValueId::new(0),
            alignment: 8,
            region: REGION,
            element: nera::VirMemoryAccess::core_u64(),
        }),
        instruction(VirInstruction::Call {
            results: vec![pointer(3), permission(4), pointer(5), permission(6)],
            target: VirCallTarget {
                symbol: "pool_partition".to_owned(),
                signature: partition_signature.clone(),
                contract: VirContractId::new(1),
                abi: None,
            },
            arguments: vec![VirValueId::new(1), VirValueId::new(2)],
        }),
        instruction(VirInstruction::Constant {
            result: word(7),
            value: VirConstant::U64(11),
        }),
        instruction(VirInstruction::Initialize {
            pointer: VirValueId::new(3),
            value: VirValueId::new(7),
            permission: VirValueId::new(4),
            access: nera::VirMemoryAccess::core_u64(),
        }),
    ];
    if read_uninitialized {
        caller_instructions.push(instruction(VirInstruction::Load {
            result: word(8),
            pointer: VirValueId::new(5),
            permission: VirValueId::new(6),
            access: nera::VirMemoryAccess::core_u64(),
        }));
    } else {
        caller_instructions.extend([
            instruction(VirInstruction::Constant {
                result: word(8),
                value: VirConstant::U64(22),
            }),
            instruction(VirInstruction::Initialize {
                pointer: VirValueId::new(5),
                value: VirValueId::new(8),
                permission: VirValueId::new(6),
                access: nera::VirMemoryAccess::core_u64(),
            }),
            instruction(VirInstruction::PermissionJoin {
                result: permission(9),
                left: VirValueId::new(4),
                right: VirValueId::new(6),
            }),
            instruction(VirInstruction::Free {
                pointer: VirValueId::new(3),
                permission: VirValueId::new(9),
            }),
        ]);
    }
    let caller = function(
        0,
        "pool_client",
        caller_signature.clone(),
        0,
        block(Vec::new(), caller_instructions, Vec::new()),
    );
    configured(validated(vec![caller, partition]), |unit| {
        let origin = function_origin(unit, VirFunctionId::new(1));
        for (position, pointers, permissions) in [
            (
                VirContractPosition::Requires,
                vec![PointerFact {
                    slot: 0,
                    lower: 0,
                    upper: 0,
                    alignment: 8,
                }],
                vec![PermissionFact {
                    slot: 1,
                    start: 0,
                    end: 16,
                    access: VirContractAccess::Write,
                    free: VirContractFree::Yes,
                }],
            ),
            (
                VirContractPosition::Ensures,
                vec![
                    PointerFact {
                        slot: 0,
                        lower: 0,
                        upper: 0,
                        alignment: 8,
                    },
                    PointerFact {
                        slot: 2,
                        lower: 8,
                        upper: 8,
                        alignment: 8,
                    },
                ],
                vec![
                    PermissionFact {
                        slot: 1,
                        start: 0,
                        end: 8,
                        access: VirContractAccess::Write,
                        free: VirContractFree::Yes,
                    },
                    PermissionFact {
                        slot: 3,
                        start: 8,
                        end: 16,
                        access: VirContractAccess::Write,
                        free: VirContractFree::Yes,
                    },
                ],
            ),
        ] {
            add_resource_clause(
                &mut unit.specs,
                VirContractId::new(1),
                position,
                origin,
                false,
                0,
                REGION,
                16,
                8,
                VirContractLiveness::Live,
                VirContractOwnership::Owned,
                VirContractInitialization::Uninitialized,
                &pointers,
                &permissions,
            );
        }
    })
}

#[test]
fn arena_object_pool_partitions_initializes_rejoins_and_releases_slots() {
    let program = object_pool_case(false);

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("object-pool case must analyze");

    assert!(verification.is_memory_checked_core0());
}

#[test]
fn object_pool_uninitialized_slot_mutation_is_refuted() {
    let program = object_pool_case(true);

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("object-pool mutation must produce diagnostics");

    assert!(!verification.is_memory_checked_core0());
    assert!(
        verification.functions()[&VirFunctionId::new(0)]
            .cfg()
            .obligations()
            .iter()
            .any(|record| {
                matches!(
                    record.obligation().kind(),
                    ResourceObligationKind::MemoryInitialized { .. }
                ) && record.obligation().status() == ObligationStatus::Refuted
            })
    );
}

fn bump_allocator_case(use_remaining_for_slot: bool) -> ValidatedVirUnit {
    let signature = VirSignature {
        parameters: vec![
            VirType::Pointer {
                access: nera::VirMemoryAccess::core_u64(),
            },
            VirType::Permission,
            VirType::U64,
        ],
        results: Vec::new(),
    };
    let write_permission = if use_remaining_for_slot { 11 } else { 10 };
    let program = validated(vec![function(
        0,
        "bump_word",
        signature.clone(),
        0,
        block(
            vec![pointer(0), permission(1), word(2)],
            vec![
                instruction(VirInstruction::WordAdd {
                    result: word(3),
                    left: VirValueId::new(2),
                    right: VirValueId::new(2),
                }),
                instruction(VirInstruction::WordAdd {
                    result: word(4),
                    left: VirValueId::new(3),
                    right: VirValueId::new(3),
                }),
                instruction(VirInstruction::WordAdd {
                    result: word(5),
                    left: VirValueId::new(4),
                    right: VirValueId::new(4),
                }),
                instruction(VirInstruction::PermissionSplit {
                    left_result: permission(6),
                    right_result: permission(7),
                    source: VirValueId::new(1),
                    split_at_bytes: VirValueId::new(5),
                }),
                instruction(VirInstruction::Constant {
                    result: word(8),
                    value: VirConstant::U64(8),
                }),
                instruction(VirInstruction::WordAdd {
                    result: word(9),
                    left: VirValueId::new(5),
                    right: VirValueId::new(8),
                }),
                instruction(VirInstruction::PermissionSplit {
                    left_result: permission(10),
                    right_result: permission(11),
                    source: VirValueId::new(7),
                    split_at_bytes: VirValueId::new(9),
                }),
                instruction(VirInstruction::PointerOffset {
                    result: pointer(12),
                    base: VirValueId::new(0),
                    delta_bytes: VirValueId::new(5),
                }),
                instruction(VirInstruction::Constant {
                    result: word(13),
                    value: VirConstant::U64(99),
                }),
                instruction(VirInstruction::Write {
                    pointer: VirValueId::new(12),
                    value: VirValueId::new(13),
                    permission: VirValueId::new(write_permission),
                    access: nera::VirMemoryAccess::core_u64(),
                }),
                instruction(VirInstruction::PermissionJoin {
                    result: permission(14),
                    left: VirValueId::new(6),
                    right: VirValueId::new(10),
                }),
                instruction(VirInstruction::PermissionJoin {
                    result: permission(15),
                    left: VirValueId::new(14),
                    right: VirValueId::new(11),
                }),
                instruction(VirInstruction::Free {
                    pointer: VirValueId::new(0),
                    permission: VirValueId::new(15),
                }),
            ],
            Vec::new(),
        ),
    )]);
    configured(program, |unit| {
        let origin = function_origin(unit, VirFunctionId::new(0));
        add_resource_clause(
            &mut unit.specs,
            VirContractId::new(0),
            VirContractPosition::Requires,
            origin,
            false,
            0,
            REGION,
            32,
            8,
            VirContractLiveness::Live,
            VirContractOwnership::Owned,
            VirContractInitialization::Uninitialized,
            &[PointerFact {
                slot: 0,
                lower: 0,
                upper: 0,
                alignment: 8,
            }],
            &[PermissionFact {
                slot: 1,
                start: 0,
                end: 32,
                access: VirContractAccess::Write,
                free: VirContractFree::Yes,
            }],
        );
        add_u64_range(
            &mut unit.specs,
            VirContractId::new(0),
            VirContractPosition::Requires,
            origin,
            2,
            0,
            2,
        );
    })
}

#[test]
fn bump_allocator_proves_dynamic_slot_bounds_alignment_and_non_overlap() {
    let program = bump_allocator_case(false);

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("bump allocator case must analyze");

    assert!(verification.is_memory_checked_core0());
    let cfg = verification.functions()[&VirFunctionId::new(0)].cfg();
    assert_eq!(
        cfg.obligations()
            .iter()
            .filter(|record| matches!(
                record.obligation().kind(),
                ResourceObligationKind::PermissionSplitPointInRange { .. }
            ))
            .count(),
        2
    );
}

#[test]
fn bump_allocator_remaining_range_cannot_mutate_allocated_slot() {
    let program = bump_allocator_case(true);

    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("bump mutation must produce diagnostics");

    assert!(!verification.is_memory_checked_core0());
    assert!(
        verification.functions()[&VirFunctionId::new(0)]
            .cfg()
            .obligations()
            .iter()
            .any(|record| {
                matches!(
                    record.obligation().kind(),
                    ResourceObligationKind::PermissionCoversAccess { .. }
                ) && record.obligation().status() == ObligationStatus::Refuted
            })
    );
}
