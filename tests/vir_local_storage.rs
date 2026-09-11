use nera::backend::{
    X86_64_UNKNOWN_LINUX_GNU, X86_64InstructionPlan, X86_64MachineInstruction,
    X86_64PlanningErrorKind,
};
use nera::{
    AbstractAllocationId, AbstractProvenance, AbstractValue, FreeCapability, ObligationStatus,
    OwnershipState, ResourceObligationKind, VirAbiClass, VirBlockId, VirConstant, VirEndianness,
    VirFunctionId, VirInstruction, VirLayout, VirLayoutId, VirMemoryAccess, VirMemorySchema,
    VirMemoryType, VirMemoryTypeKind, VirObjectShapeErrorKind, VirRuntimeValue,
    VirTargetDataLayout, VirTerminator, VirType, VirTypeId, VirUnit, VirValidationErrorKind,
    VirValueId, analyze_function_cfg, interpret,
};

#[path = "support/address_program.rs"]
mod address_program;
#[path = "support/local_storage_program.rs"]
mod local_storage_program;

#[test]
fn scalar_local_storage_is_verified_executed_dumped_and_lowered() {
    let validated = local_storage_program::scalar_program(41)
        .into_validated()
        .expect("scalar local storage validates");
    assert!(
        validated.stable_dump().contains(
            "%0: ptr<type0/layout0>, %1: permission = local-storage access type0/layout0"
        )
    );

    let resolved = validated.resolve().expect("local program resolves");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("local resource transfer succeeds");
    assert!(analysis.all_obligations_proven());
    let state = &analysis
        .block(VirBlockId::new(0))
        .expect("entry block analysis")
        .instruction_states()[0];
    let allocation_id = AbstractAllocationId::vir_local_storage_site(VirValueId::new(0));
    let allocation = state
        .allocation(allocation_id)
        .expect("local allocation is tracked");
    assert_eq!(allocation.region(), None);
    assert_eq!(allocation.ownership(), OwnershipState::Unowned);
    let AbstractValue::Pointer(pointer) = state
        .value(VirValueId::new(0))
        .copied()
        .expect("local pointer is defined")
    else {
        panic!("local pointer has the wrong abstract type")
    };
    assert_eq!(
        pointer.provenance(),
        AbstractProvenance::Known(allocation_id)
    );
    assert_eq!(pointer.offset_bytes().exact_value(), Some(0));
    assert_eq!(
        pointer.memory_access(),
        Some(nera::VirMemoryAccess::core_u64())
    );
    let AbstractValue::Permission(permission) = state
        .value(VirValueId::new(1))
        .copied()
        .expect("local permission is defined")
    else {
        panic!("local permission has the wrong abstract type")
    };
    assert_eq!(permission.free_capability(), FreeCapability::No);

    let execution = interpret(resolved.runtime()).expect("local program executes");
    assert_eq!(execution.values(), &[VirRuntimeValue::U64(41)]);

    let plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("local program has a native frame plan");
    let function = plan.function(VirFunctionId::new(0)).expect("function plan");
    let region = function
        .frame()
        .local_storage_region(VirValueId::new(0))
        .expect("local frame region");
    assert_eq!(region.size_bytes(), 8);
    assert_eq!(region.alignment_bytes(), 8);
    assert_eq!(region.base_offset_from_rbp_bytes() % 8, 0);
    assert!(matches!(
        function.blocks()[0].instructions()[0],
        X86_64InstructionPlan::LocalStorage(planned) if planned == region
    ));
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("local storage selects native instructions");
    assert!(
        machine.functions()[0]
            .blocks()
            .iter()
            .flat_map(|block| block.instructions())
            .any(|instruction| matches!(
                instruction,
                X86_64MachineInstruction::LoadEffectiveAddress64 { source, .. }
                    if source.displacement() == region.base_offset_from_rbp_bytes()
            ))
    );
}

#[test]
fn local_storage_has_no_free_authority() {
    let mut unit = local_storage_program::scalar_program(7);
    unit.runtime.functions[0].blocks[0].instructions.truncate(3);
    unit.runtime.functions[0].blocks[0]
        .instructions
        .push(local_storage_program::instruction(VirInstruction::Free {
            pointer: VirValueId::new(0),
            permission: VirValueId::new(1),
        }));
    unit.runtime.functions[0].blocks[0].terminator.terminator = VirTerminator::Return {
        values: vec![VirValueId::new(2)],
    };
    let validated = rebuild_source_map(unit)
        .into_validated()
        .expect("free remains structural VIR");
    let resolved = validated.resolve().expect("free fixture resolves");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("free produces proof obligations");
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::PermissionCanFree { .. }
                | ResourceObligationKind::AllocationOwned { .. }
        ) && record.obligation().status() == ObligationStatus::Refuted
    }));
    assert!(matches!(
        interpret(resolved.runtime())
            .expect_err("interpreter rejects freeing frame storage")
            .kind(),
        nera::VirExecutionErrorKind::InvalidFree { .. }
    ));
}

#[test]
fn escaped_local_storage_is_invalidated_on_return() {
    let pointer_type = VirType::Pointer {
        access: nera::VirMemoryAccess::core_u64(),
    };
    let callee_signature = nera::VirSignature {
        parameters: vec![],
        results: vec![pointer_type, VirType::Permission],
    };
    let main = local_storage_program::function(
        0,
        "main",
        vec![],
        vec![VirType::U64],
        vec![local_storage_program::block(
            0,
            vec![],
            vec![
                local_storage_program::instruction(VirInstruction::Call {
                    results: vec![
                        local_storage_program::pointer(0),
                        local_storage_program::permission(1),
                    ],
                    target: nera::VirCallTarget {
                        symbol: "escape".to_owned(),
                        signature: callee_signature.clone(),
                        contract: nera::VirContractId::new(1),
                        abi: None,
                    },
                    arguments: vec![],
                }),
                local_storage_program::instruction(VirInstruction::Load {
                    result: local_storage_program::word(2),
                    pointer: VirValueId::new(0),
                    permission: VirValueId::new(1),
                    access: nera::VirMemoryAccess::core_u64(),
                }),
            ],
            VirTerminator::Return {
                values: vec![VirValueId::new(2)],
            },
        )],
    );
    let callee = local_storage_program::function(
        1,
        "escape",
        vec![],
        callee_signature.results,
        vec![local_storage_program::block(
            0,
            vec![],
            vec![
                local_storage_program::local(10, 11),
                local_storage_program::instruction(VirInstruction::Constant {
                    result: local_storage_program::word(12),
                    value: VirConstant::U64(9),
                }),
                local_storage_program::instruction(VirInstruction::Initialize {
                    pointer: VirValueId::new(10),
                    value: VirValueId::new(12),
                    permission: VirValueId::new(11),
                    access: nera::VirMemoryAccess::core_u64(),
                }),
            ],
            VirTerminator::Return {
                values: vec![VirValueId::new(10), VirValueId::new(11)],
            },
        )],
    );
    let validated = VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![main, callee],
    )
    .into_validated()
    .expect("escaping local pointer is structurally representable");
    let resolved = validated.resolve().expect("escape fixture resolves");
    assert!(matches!(
        interpret(resolved.runtime())
            .expect_err("returned local pointer is already expired")
            .kind(),
        nera::VirExecutionErrorKind::UseAfterLifetimeEnd { .. }
    ));
}

#[test]
fn recursive_calls_instantiate_distinct_local_storage() {
    let validated = local_storage_program::recursive_program();
    let resolved = validated.resolve().expect("recursive fixture resolves");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(1))
        .expect("recursive local storage is analyzed through its contract");
    assert!(analysis.all_obligations_proven());
    let execution = interpret(resolved.runtime()).expect("recursive local storage executes");
    assert_eq!(execution.values(), &[VirRuntimeValue::U64(11)]);
}

#[test]
fn local_storage_resource_facts_survive_branch_and_loop_edges() {
    let function = local_storage_program::function(
        0,
        "local_loop",
        vec![VirType::Bool],
        vec![VirType::U64],
        vec![
            local_storage_program::block(
                0,
                vec![local_storage_program::boolean(0)],
                vec![
                    local_storage_program::local(1, 2),
                    local_storage_program::instruction(VirInstruction::Constant {
                        result: local_storage_program::word(3),
                        value: VirConstant::U64(8),
                    }),
                    local_storage_program::instruction(VirInstruction::Initialize {
                        pointer: VirValueId::new(1),
                        value: VirValueId::new(3),
                        permission: VirValueId::new(2),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                ],
                VirTerminator::Jump {
                    target: local_storage_program::target(1, &[0, 1, 2]),
                },
            ),
            local_storage_program::block(
                1,
                vec![
                    local_storage_program::boolean(10),
                    local_storage_program::pointer(11),
                    local_storage_program::permission(12),
                ],
                vec![],
                VirTerminator::Branch {
                    condition: VirValueId::new(10),
                    then_target: local_storage_program::target(1, &[10, 11, 12]),
                    else_target: local_storage_program::target(2, &[11, 12]),
                },
            ),
            local_storage_program::block(
                2,
                vec![
                    local_storage_program::pointer(20),
                    local_storage_program::permission(21),
                ],
                vec![local_storage_program::instruction(VirInstruction::Load {
                    result: local_storage_program::word(22),
                    pointer: VirValueId::new(20),
                    permission: VirValueId::new(21),
                    access: nera::VirMemoryAccess::core_u64(),
                })],
                VirTerminator::Return {
                    values: vec![VirValueId::new(22)],
                },
            ),
        ],
    );
    let validated = VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![function],
    )
    .into_validated()
    .expect("loop-local fixture validates");
    let resolved = validated.resolve().expect("loop-local fixture resolves");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("local facts reach a cyclic fixed point");
    assert!(analysis.loop_blocks().contains(&VirBlockId::new(1)));
    assert!(analysis.all_obligations_proven());
}

#[test]
fn local_storage_placement_and_shape_are_fail_closed() {
    let mut late = local_storage_program::scalar_program(1);
    late.runtime.functions[0].blocks[0].instructions.swap(0, 1);
    assert_eq!(
        late.into_validated()
            .expect_err("late local must fail")
            .kind(),
        &VirValidationErrorKind::LocalStorageAfterEntryInstruction
    );

    let mut reentered = local_storage_program::scalar_program(1);
    reentered.runtime.functions[0].blocks[0]
        .terminator
        .terminator = VirTerminator::Jump {
        target: local_storage_program::target(0, &[]),
    };
    assert_eq!(
        reentered
            .into_validated()
            .expect_err("entry re-entry would allocate the site twice")
            .kind(),
        &VirValidationErrorKind::LocalStorageEntryReentered
    );

    let mut outside = local_storage_program::scalar_program(1);
    outside.runtime.functions[0].entry = VirBlockId::new(1);
    outside.runtime.functions[0].blocks.insert(
        0,
        local_storage_program::block(
            1,
            vec![],
            vec![],
            VirTerminator::Jump {
                target: local_storage_program::target(0, &[]),
            },
        ),
    );
    assert_eq!(
        rebuild_source_map(outside)
            .into_validated()
            .expect_err("local storage outside the entry block must fail")
            .kind(),
        &VirValidationErrorKind::LocalStorageOutsideEntry
    );

    let mut invalid_access = local_storage_program::scalar_program(1);
    let VirInstruction::LocalStorage { access, .. } =
        &mut invalid_access.runtime.functions[0].blocks[0].instructions[0].instruction
    else {
        unreachable!()
    };
    *access = VirMemoryAccess::new(VirTypeId::new(99), VirLayoutId::new(99));
    assert!(matches!(
        invalid_access
            .into_validated()
            .expect_err("forged access must fail")
            .kind(),
        VirValidationErrorKind::InvalidLocalStorageShape(
            VirObjectShapeErrorKind::InvalidAccess { .. }
        )
    ));

    let mut zero = local_storage_program::scalar_program(1);
    zero.memory = zero_sized_schema();
    let VirInstruction::LocalStorage { access, .. } =
        &mut zero.runtime.functions[0].blocks[0].instructions[0].instruction
    else {
        unreachable!()
    };
    *access = VirMemoryAccess::new(VirTypeId::new(0), VirLayoutId::new(0));
    assert_eq!(
        zero.into_validated()
            .expect_err("zero-sized frame storage is gated")
            .kind(),
        &VirValidationErrorKind::ZeroSizedLocalStorage
    );
}

#[test]
fn aggregate_shape_controls_local_frame_extent_and_padding() {
    let mut unit = local_storage_program::scalar_program(5);
    unit.memory = address_program::schema();
    let block = &mut unit.runtime.functions[0].blocks[0];
    let VirInstruction::LocalStorage {
        pointer_result,
        access,
        ..
    } = &mut block.instructions[0].instruction
    else {
        unreachable!()
    };
    *access = address_program::RECORD_ACCESS;
    pointer_result.ty = VirType::Pointer {
        access: address_program::RECORD_ACCESS,
    };
    block.instructions.insert(
        1,
        local_storage_program::instruction(VirInstruction::FieldAddress {
            result: local_storage_program::value(
                4,
                VirType::Pointer {
                    access: address_program::ARRAY_ACCESS,
                },
            ),
            base: VirValueId::new(0),
            field: nera::VirFieldId::new(0),
            owner: address_program::RECORD_ACCESS,
            field_access: address_program::ARRAY_ACCESS,
            offset_bytes: 8,
        }),
    );
    block.instructions.insert(
        2,
        local_storage_program::instruction(VirInstruction::Constant {
            result: local_storage_program::word(5),
            value: VirConstant::U64(0),
        }),
    );
    block.instructions.insert(
        3,
        local_storage_program::instruction(VirInstruction::IndexAddress {
            result: local_storage_program::value(
                6,
                VirType::Pointer {
                    access: address_program::U64_ACCESS,
                },
            ),
            base: VirValueId::new(4),
            index: VirValueId::new(5),
            source: address_program::ARRAY_ACCESS,
            element: address_program::U64_ACCESS,
            stride_bytes: 8,
            bounds: nera::VirIndexBounds::Array { length: 4 },
        }),
    );
    for instruction in &mut block.instructions[4..] {
        match &mut instruction.instruction {
            VirInstruction::Initialize {
                pointer, access, ..
            }
            | VirInstruction::Load {
                pointer, access, ..
            }
            | VirInstruction::Store {
                pointer, access, ..
            } => {
                *pointer = VirValueId::new(6);
                *access = address_program::U64_ACCESS;
            }
            _ => {}
        }
    }
    let mut forged_owner = unit.clone();
    let VirInstruction::FieldAddress { owner, .. } =
        &mut forged_owner.runtime.functions[0].blocks[0].instructions[1].instruction
    else {
        unreachable!()
    };
    *owner = address_program::ARRAY_ACCESS;
    assert!(matches!(
        rebuild_source_map(forged_owner)
            .into_validated()
            .expect_err("forged projection owner must fail")
            .kind(),
        VirValidationErrorKind::TypeMismatch {
            context: "field address",
            ..
        }
    ));

    let validated = rebuild_source_map(unit)
        .into_validated()
        .expect("aggregate local validates");
    let shape = validated
        .as_unit()
        .memory
        .object_shape(address_program::RECORD_ACCESS)
        .expect("record shape");
    assert_eq!(shape.size_bytes(), 40);
    assert!(!shape.padding().is_empty());
    let resolved = validated.resolve().expect("aggregate fixture resolves");
    let plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("aggregate local has native plan");
    let region = plan.functions()[0]
        .frame()
        .local_storage_region(VirValueId::new(0))
        .expect("aggregate frame region");
    assert_eq!(region.size_bytes(), 40);
    assert_eq!(region.alignment_bytes(), 8);
    assert_eq!(
        interpret(resolved.runtime())
            .expect("aggregate local executes")
            .values(),
        &[VirRuntimeValue::U64(5)]
    );
}

#[test]
fn native_planning_rejects_frame_overflow_at_the_storage_site() {
    let mut unit = local_storage_program::scalar_program(1);
    unit.memory = oversized_enum_schema();
    let VirInstruction::LocalStorage {
        pointer_result,
        access,
        ..
    } = &mut unit.runtime.functions[0].blocks[0].instructions[0].instruction
    else {
        unreachable!()
    };
    *access = VirMemoryAccess::new(VirTypeId::new(1), VirLayoutId::new(1));
    pointer_result.ty = VirType::Pointer { access: *access };
    unit.runtime.functions[0].signature.results.clear();
    unit.runtime.functions[0].blocks[0].instructions.truncate(1);
    unit.runtime.functions[0].blocks[0].terminator.terminator =
        VirTerminator::Return { values: vec![] };
    let validated = rebuild_source_map(unit)
        .into_validated()
        .expect("large shape is valid abstract VIR");
    let resolved = validated.resolve().expect("large fixture resolves");
    let error = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect_err("native frame limit must be enforced");
    assert!(matches!(
        error.kind(),
        X86_64PlanningErrorKind::FrameSizeExceeded { .. }
    ));
    assert_eq!(error.instruction_index(), Some(0));
}

#[test]
fn native_planning_rejects_alignment_beyond_the_frame_guarantee() {
    let mut unit = local_storage_program::scalar_program(1);
    unit.memory = address_program::schema();
    unit.memory.layouts[2].size_bytes = 64;
    unit.memory.layouts[2].alignment = 32;
    let VirInstruction::LocalStorage {
        pointer_result,
        access,
        ..
    } = &mut unit.runtime.functions[0].blocks[0].instructions[0].instruction
    else {
        unreachable!()
    };
    *access = address_program::RECORD_ACCESS;
    pointer_result.ty = VirType::Pointer { access: *access };
    unit.runtime.functions[0].signature.results.clear();
    unit.runtime.functions[0].blocks[0].instructions.truncate(1);
    unit.runtime.functions[0].blocks[0].terminator.terminator =
        VirTerminator::Return { values: vec![] };
    let validated = rebuild_source_map(unit)
        .into_validated()
        .expect("over-aligned shape is valid target-independent VIR");
    let resolved = validated.resolve().expect("over-aligned fixture resolves");
    let error = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect_err("native frame alignment guarantee must be enforced");
    assert_eq!(
        error.kind(),
        &X86_64PlanningErrorKind::UnsupportedLocalStorageAlignment {
            requested: 32,
            maximum: 16,
        }
    );
    assert_eq!(error.instruction_index(), Some(0));
}

fn zero_sized_schema() -> VirMemorySchema {
    let mut schema = VirMemorySchema {
        target: target(),
        types: vec![VirMemoryType {
            id: VirTypeId::new(0),
            kind: VirMemoryTypeKind::Unit,
            layout: VirLayoutId::new(0),
        }],
        type_capabilities: vec![],
        layouts: vec![VirLayout {
            id: VirLayoutId::new(0),
            ty: VirTypeId::new(0),
            size_bytes: 0,
            alignment: 1,
            abi: VirAbiClass::Ignore,
            fields: vec![],
            variants: None,
        }],
        fields: vec![],
        variants: vec![],
    };
    schema.assign_canonical_type_capabilities().unwrap();
    schema
}

fn oversized_enum_schema() -> VirMemorySchema {
    let size = X86_64_UNKNOWN_LINUX_GNU.maximum_frame_size_bytes() + 8;
    let mut schema = VirMemorySchema {
        target: target(),
        types: vec![
            VirMemoryType {
                id: VirTypeId::new(0),
                kind: VirMemoryTypeKind::Integer(nera::VirIntegerType::U64),
                layout: VirLayoutId::new(0),
            },
            VirMemoryType {
                id: VirTypeId::new(1),
                kind: VirMemoryTypeKind::Enum { variants: vec![] },
                layout: VirLayoutId::new(1),
            },
        ],
        type_capabilities: vec![],
        layouts: vec![
            VirLayout {
                id: VirLayoutId::new(0),
                ty: VirTypeId::new(0),
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: vec![],
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(1),
                ty: VirTypeId::new(1),
                size_bytes: size,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![],
                variants: Some(nera::VirVariantLayout {
                    tag_size_bytes: 1,
                    tag_alignment: 1,
                    cases: vec![],
                }),
            },
        ],
        fields: vec![],
        variants: vec![],
    };
    schema.assign_canonical_type_capabilities().unwrap();
    schema
}

const fn target() -> VirTargetDataLayout {
    VirTargetDataLayout {
        endianness: VirEndianness::Little,
        pointer_size_bytes: 8,
        pointer_alignment: 8,
        usize_size_bytes: 8,
        usize_alignment: 8,
    }
}

fn rebuild_source_map(unit: VirUnit) -> VirUnit {
    VirUnit::from_runtime(unit.memory, unit.runtime.entry, unit.runtime.functions)
}
