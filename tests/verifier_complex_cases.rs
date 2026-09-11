use nera::{
    ByteSpan, CfgAnalysisConfig, ObligationStatus, ResourceObligationKind, SpannedVirInstruction,
    SpannedVirTerminator, ValidatedVirUnit, VirBasicBlock, VirBlockId, VirConstant,
    VirContractAccess, VirContractFree, VirContractId, VirContractInitialization,
    VirContractLiveness, VirContractOwnership, VirContractPosition, VirFunction, VirFunctionId,
    VirInstruction, VirRegionId, VirSignature, VirTerminator, VirType, VirUnit, VirValue,
    VirValueId, verify_program,
};

#[path = "support/contract_builder.rs"]
mod contract_builder;

use contract_builder::{PermissionFact, PointerFact, add_resource_clause, function_origin};

const REGION_HEAP: VirRegionId = VirRegionId::new(0);
const REGION_DEVICE: VirRegionId = VirRegionId::new(99);

fn span() -> ByteSpan {
    ByteSpan::new(200, 220).expect("valid test span")
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

fn program(
    name: &str,
    signature: VirSignature,
    parameters: Vec<VirValue>,
    instructions: Vec<SpannedVirInstruction>,
    returns: Vec<VirValueId>,
) -> ValidatedVirUnit {
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: name.to_owned(),
            signature,
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters,
                instructions,
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return { values: returns },
                    source_span: span(),
                },
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
    .into_validated()
    .expect("complex-case VIR must be structurally valid")
}

fn configured(program: ValidatedVirUnit, configure: impl FnOnce(&mut VirUnit)) -> ValidatedVirUnit {
    let mut unit = program.as_unit().clone();
    configure(&mut unit);
    unit.into_validated().expect("configured complex contract")
}

fn resource_clause(
    unit: &mut VirUnit,
    position: VirContractPosition,
    resource: u32,
    region: VirRegionId,
    ownership: VirContractOwnership,
    pointers: &[PointerFact],
    permissions: &[PermissionFact],
) {
    let origin = function_origin(unit, VirFunctionId::new(0));
    add_resource_clause(
        &mut unit.specs,
        VirContractId::new(0),
        position,
        origin,
        false,
        resource,
        region,
        permissions.first().map_or(8, |permission| permission.end),
        8,
        VirContractLiveness::Live,
        ownership,
        VirContractInitialization::Initialized,
        pointers,
        permissions,
    );
}

fn has_refuted(
    verification: &nera::ProgramVerification,
    predicate: impl Fn(ResourceObligationKind) -> bool,
) -> bool {
    verification.functions()[&VirFunctionId::new(0)]
        .cfg()
        .obligations()
        .iter()
        .any(|record| {
            predicate(record.obligation().kind())
                && record.obligation().status() == ObligationStatus::Refuted
        })
}

fn raw_pointer_container_case(free_before_access: bool) -> ValidatedVirUnit {
    let signature = VirSignature {
        parameters: vec![pointer(0).ty, pointer(1).ty, permission(2).ty],
        results: Vec::new(),
    };
    let load = instruction(VirInstruction::Load {
        result: word(3),
        pointer: VirValueId::new(1),
        permission: VirValueId::new(2),
        access: nera::VirMemoryAccess::core_u64(),
    });
    let free = instruction(VirInstruction::Free {
        pointer: VirValueId::new(0),
        permission: VirValueId::new(2),
    });
    let instructions = if free_before_access {
        vec![free, load]
    } else {
        vec![load, free]
    };
    let program = program(
        "raw_view_container",
        signature.clone(),
        vec![pointer(0), pointer(1), permission(2)],
        instructions,
        Vec::new(),
    );
    configured(program, |unit| {
        resource_clause(
            unit,
            VirContractPosition::Requires,
            0,
            REGION_HEAP,
            VirContractOwnership::Owned,
            &[
                PointerFact {
                    slot: 0,
                    lower: 0,
                    upper: 0,
                    alignment: 8,
                },
                PointerFact {
                    slot: 1,
                    lower: 8,
                    upper: 8,
                    alignment: 8,
                },
            ],
            &[PermissionFact {
                slot: 2,
                start: 0,
                end: 16,
                access: VirContractAccess::Write,
                free: VirContractFree::Yes,
            }],
        );
    })
}

#[test]
fn internal_raw_pointer_view_is_bounded_by_owner_liveness() {
    let program = raw_pointer_container_case(false);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("raw-pointer container must analyze");

    assert!(verification.is_memory_checked_core0());
}

#[test]
fn internal_raw_pointer_view_after_owner_free_is_refuted() {
    let program = raw_pointer_container_case(true);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("raw-pointer UAF mutation must analyze");

    assert!(!verification.is_memory_checked_core0());
    assert!(has_refuted(&verification, |kind| matches!(
        kind,
        ResourceObligationKind::AllocationLive { .. }
    )));
}

fn intrusive_list_case(use_wrong_node_permission: bool) -> ValidatedVirUnit {
    let signature = VirSignature {
        parameters: vec![
            pointer(0).ty,
            permission(1).ty,
            pointer(2).ty,
            pointer(3).ty,
            permission(4).ty,
        ],
        results: Vec::new(),
    };
    let program = program(
        "intrusive_pair",
        signature.clone(),
        vec![
            pointer(0),
            permission(1),
            pointer(2),
            pointer(3),
            permission(4),
        ],
        vec![
            instruction(VirInstruction::Load {
                result: word(5),
                pointer: VirValueId::new(3),
                permission: VirValueId::new(if use_wrong_node_permission { 1 } else { 4 }),
                access: nera::VirMemoryAccess::core_u64(),
            }),
            instruction(VirInstruction::Constant {
                result: word(6),
                value: VirConstant::U64(17),
            }),
            instruction(VirInstruction::Store {
                pointer: VirValueId::new(3),
                value: VirValueId::new(6),
                permission: VirValueId::new(4),
                access: nera::VirMemoryAccess::core_u64(),
            }),
            instruction(VirInstruction::Free {
                pointer: VirValueId::new(0),
                permission: VirValueId::new(1),
            }),
            instruction(VirInstruction::Free {
                pointer: VirValueId::new(2),
                permission: VirValueId::new(4),
            }),
        ],
        Vec::new(),
    );
    configured(program, |unit| {
        resource_clause(
            unit,
            VirContractPosition::Requires,
            0,
            REGION_HEAP,
            VirContractOwnership::Owned,
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
                access: VirContractAccess::Write,
                free: VirContractFree::Yes,
            }],
        );
        resource_clause(
            unit,
            VirContractPosition::Requires,
            1,
            REGION_HEAP,
            VirContractOwnership::Owned,
            &[
                PointerFact {
                    slot: 2,
                    lower: 0,
                    upper: 0,
                    alignment: 8,
                },
                PointerFact {
                    slot: 3,
                    lower: 0,
                    upper: 0,
                    alignment: 8,
                },
            ],
            &[PermissionFact {
                slot: 4,
                start: 0,
                end: 8,
                access: VirContractAccess::Write,
                free: VirContractFree::Yes,
            }],
        );
    })
}

#[test]
fn intrusive_list_edge_uses_the_target_nodes_permission() {
    let program = intrusive_list_case(false);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("intrusive-list pressure case must analyze");

    assert!(verification.is_memory_checked_core0());
}

#[test]
fn intrusive_list_edge_rejects_an_unrelated_node_permission() {
    let program = intrusive_list_case(true);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("intrusive-list mutation must analyze");

    assert!(!verification.is_memory_checked_core0());
    assert!(has_refuted(&verification, |kind| matches!(
        kind,
        ResourceObligationKind::PermissionMatchesAllocation { .. }
    )));
}

fn cyclic_graph_case(free_before_back_edge: bool) -> ValidatedVirUnit {
    let signature = VirSignature {
        parameters: vec![
            pointer(0).ty,
            pointer(1).ty,
            pointer(2).ty,
            pointer(3).ty,
            permission(4).ty,
            permission(5).ty,
        ],
        results: Vec::new(),
    };
    let forward = instruction(VirInstruction::Load {
        result: word(6),
        pointer: VirValueId::new(2),
        permission: VirValueId::new(5),
        access: nera::VirMemoryAccess::core_u64(),
    });
    let back = instruction(VirInstruction::Load {
        result: word(7),
        pointer: VirValueId::new(3),
        permission: VirValueId::new(4),
        access: nera::VirMemoryAccess::core_u64(),
    });
    let free_a = instruction(VirInstruction::Free {
        pointer: VirValueId::new(0),
        permission: VirValueId::new(4),
    });
    let free_b = instruction(VirInstruction::Free {
        pointer: VirValueId::new(1),
        permission: VirValueId::new(5),
    });
    let instructions = if free_before_back_edge {
        vec![forward, free_a, back, free_b]
    } else {
        vec![forward, back, free_a, free_b]
    };
    let program = program(
        "two_node_cycle",
        signature.clone(),
        vec![
            pointer(0),
            pointer(1),
            pointer(2),
            pointer(3),
            permission(4),
            permission(5),
        ],
        instructions,
        Vec::new(),
    );
    configured(program, |unit| {
        resource_clause(
            unit,
            VirContractPosition::Requires,
            0,
            REGION_HEAP,
            VirContractOwnership::Owned,
            &[
                PointerFact {
                    slot: 0,
                    lower: 0,
                    upper: 0,
                    alignment: 8,
                },
                PointerFact {
                    slot: 3,
                    lower: 0,
                    upper: 0,
                    alignment: 8,
                },
            ],
            &[PermissionFact {
                slot: 4,
                start: 0,
                end: 8,
                access: VirContractAccess::Write,
                free: VirContractFree::Yes,
            }],
        );
        resource_clause(
            unit,
            VirContractPosition::Requires,
            1,
            REGION_HEAP,
            VirContractOwnership::Owned,
            &[
                PointerFact {
                    slot: 1,
                    lower: 0,
                    upper: 0,
                    alignment: 8,
                },
                PointerFact {
                    slot: 2,
                    lower: 0,
                    upper: 0,
                    alignment: 8,
                },
            ],
            &[PermissionFact {
                slot: 5,
                start: 0,
                end: 8,
                access: VirContractAccess::Write,
                free: VirContractFree::Yes,
            }],
        );
    })
}

#[test]
fn cyclic_graph_aliases_retain_each_target_allocation_identity() {
    let program = cyclic_graph_case(false);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("cyclic-graph pressure case must analyze");

    assert!(verification.is_memory_checked_core0());
}

#[test]
fn cyclic_graph_back_edge_after_target_free_is_refuted() {
    let program = cyclic_graph_case(true);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("cyclic-graph mutation must analyze");

    assert!(!verification.is_memory_checked_core0());
    assert!(has_refuted(&verification, |kind| matches!(
        kind,
        ResourceObligationKind::AllocationLive { .. }
    )));
}

fn mapped_device_case(try_to_free: bool) -> ValidatedVirUnit {
    let signature = VirSignature {
        parameters: vec![pointer(0).ty, permission(1).ty],
        results: vec![permission(4).ty],
    };
    let mut instructions = vec![
        instruction(VirInstruction::Constant {
            result: word(2),
            value: VirConstant::U64(0x55aa),
        }),
        instruction(VirInstruction::Store {
            pointer: VirValueId::new(0),
            value: VirValueId::new(2),
            permission: VirValueId::new(1),
            access: nera::VirMemoryAccess::core_u64(),
        }),
        instruction(VirInstruction::Load {
            result: word(3),
            pointer: VirValueId::new(0),
            permission: VirValueId::new(1),
            access: nera::VirMemoryAccess::core_u64(),
        }),
    ];
    let returns = if try_to_free {
        instructions.push(instruction(VirInstruction::Free {
            pointer: VirValueId::new(0),
            permission: VirValueId::new(1),
        }));
        vec![VirValueId::new(1)]
    } else {
        instructions.push(instruction(VirInstruction::PermissionMove {
            result: permission(4),
            source: VirValueId::new(1),
        }));
        vec![VirValueId::new(4)]
    };
    let program = program(
        "mapped_device_word",
        signature.clone(),
        vec![pointer(0), permission(1)],
        instructions,
        returns,
    );
    configured(program, |unit| {
        resource_clause(
            unit,
            VirContractPosition::Requires,
            0,
            REGION_DEVICE,
            VirContractOwnership::Unowned,
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
                access: VirContractAccess::Write,
                free: VirContractFree::No,
            }],
        );
        resource_clause(
            unit,
            VirContractPosition::Ensures,
            0,
            REGION_DEVICE,
            VirContractOwnership::Unowned,
            &[],
            &[PermissionFact {
                slot: 0,
                start: 0,
                end: 8,
                access: VirContractAccess::Write,
                free: VirContractFree::No,
            }],
        );
    })
}

#[test]
fn mapped_device_region_allows_access_but_returns_nonfreeing_permission() {
    let program = mapped_device_case(false);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("mapped-device pressure case must analyze");

    assert!(verification.is_memory_checked_core0());
    assert!(verification.trust_report().entries().is_empty());
}

#[test]
fn mapped_device_region_cannot_be_freed_by_an_unowned_permission() {
    let program = mapped_device_case(true);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("mapped-device free mutation must analyze");

    assert!(!verification.is_memory_checked_core0());
    assert!(has_refuted(&verification, |kind| matches!(
        kind,
        ResourceObligationKind::AllocationOwned { .. }
            | ResourceObligationKind::PermissionCanFree { .. }
    )));
}
