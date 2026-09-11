use std::collections::BTreeSet;

use nera::{
    AbstractAllocation, AbstractAllocationId, AbstractByteRange, AbstractPermission,
    AbstractPointer, AbstractProvenance, AbstractValue, AccessPermission, ActiveVariantState,
    ByteRange, ByteSpan, FreeCapability, GuaranteedAlignment, InitializationClass, ObjectStateKey,
    ObligationStatus, ResourceObligationKind, ResourceState, SpannedVirInstruction,
    SpannedVirTerminator, U64Interval, VirAbiClass, VirBasicBlock, VirBlockId, VirBlockTarget,
    VirContractId, VirEndianness, VirField, VirFieldId, VirFieldLayout, VirFunction, VirFunctionId,
    VirInstruction, VirIntegerType, VirLayout, VirLayoutId, VirMemoryAccess, VirMemorySchema,
    VirMemoryType, VirMemoryTypeKind, VirObjectDestinationMode, VirObjectSourceMode, VirSignature,
    VirTargetDataLayout, VirTerminator, VirType, VirTypeId, VirUnit, VirValue, VirValueId,
    VirVariant, VirVariantCaseLayout, VirVariantId, VirVariantLayout, analyze_function_cfg,
    transfer_instruction_with_memory,
};

#[path = "support/address_program.rs"]
mod address_program;

const ENUM_ACCESS: VirMemoryAccess = VirMemoryAccess::new(VirTypeId::new(1), VirLayoutId::new(1));
const U64_ACCESS: VirMemoryAccess = VirMemoryAccess::new(VirTypeId::new(0), VirLayoutId::new(0));

fn span() -> ByteSpan {
    ByteSpan::new(0, 1).expect("ordered span")
}

fn range(start: u64, end: u64) -> ByteRange {
    ByteRange::new(start, end).expect("ordered range")
}

fn instruction(instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(),
    }
}

fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

fn pointer_value(id: u32, access: VirMemoryAccess) -> VirValue {
    value(id, VirType::Pointer { access })
}

fn permission_value(id: u32) -> VirValue {
    value(id, VirType::Permission)
}

fn pointer(
    allocation: AbstractAllocationId,
    offset: u64,
    access: VirMemoryAccess,
) -> AbstractValue {
    AbstractValue::Pointer(
        AbstractPointer::new(
            AbstractProvenance::Known(allocation),
            U64Interval::exact(offset),
            GuaranteedAlignment::new(8).expect("aligned pointer"),
        )
        .with_memory_access(Some(access)),
    )
}

fn permission(allocation: AbstractAllocationId, size: u64) -> AbstractValue {
    AbstractValue::Permission(AbstractPermission::new(
        AbstractProvenance::Known(allocation),
        AbstractByteRange::Exact(range(0, size)),
        AccessPermission::Write,
        FreeCapability::No,
    ))
}

fn record_state(destination_initialized: bool, source_initialized_end: u64) -> ResourceState {
    let destination = AbstractAllocationId::new(0);
    let source = AbstractAllocationId::new(1);
    let mut destination_allocation = AbstractAllocation::new_local(40, 8).expect("destination");
    let mut source_allocation = AbstractAllocation::new_local(40, 8).expect("source");
    destination_allocation
        .forget_initialization(range(0, 8))
        .expect("padding is non-value");
    source_allocation
        .forget_initialization(range(0, 8))
        .expect("padding is non-value");
    if destination_initialized {
        destination_allocation
            .mark_initialized(range(8, 40))
            .expect("destination value bytes");
        destination_allocation
            .mark_valid(range(8, 40))
            .expect("destination validity");
    }
    if source_initialized_end > 8 {
        source_allocation
            .mark_initialized(range(8, source_initialized_end))
            .expect("source value bytes");
        source_allocation
            .mark_valid(range(8, source_initialized_end))
            .expect("source validity");
    }

    let mut state = ResourceState::new();
    state
        .define_allocation(destination, destination_allocation)
        .unwrap();
    state.define_allocation(source, source_allocation).unwrap();
    state
        .define_value(
            VirValueId::new(0),
            pointer(destination, 0, address_program::RECORD_ACCESS),
        )
        .unwrap();
    state
        .define_value(VirValueId::new(1), permission(destination, 40))
        .unwrap();
    state
        .define_value(
            VirValueId::new(2),
            pointer(source, 0, address_program::RECORD_ACCESS),
        )
        .unwrap();
    state
        .define_value(VirValueId::new(3), permission(source, 40))
        .unwrap();
    state
}

fn object_transfer(
    destination_mode: VirObjectDestinationMode,
    source_mode: VirObjectSourceMode,
) -> SpannedVirInstruction {
    instruction(VirInstruction::ObjectTransfer {
        destination: VirValueId::new(0),
        destination_permission: VirValueId::new(1),
        source: VirValueId::new(2),
        source_permission: VirValueId::new(3),
        access: address_program::RECORD_ACCESS,
        destination_mode,
        source_mode,
    })
}

#[test]
fn all_transfer_modes_conserve_value_bytes_and_never_read_padding() {
    for (destination_mode, source_mode) in [
        (
            VirObjectDestinationMode::Initialize,
            VirObjectSourceMode::Copy,
        ),
        (
            VirObjectDestinationMode::Initialize,
            VirObjectSourceMode::Move,
        ),
        (VirObjectDestinationMode::Replace, VirObjectSourceMode::Copy),
        (VirObjectDestinationMode::Replace, VirObjectSourceMode::Move),
    ] {
        let input = record_state(
            matches!(destination_mode, VirObjectDestinationMode::Replace),
            40,
        );
        let result = transfer_instruction_with_memory(
            &input,
            &object_transfer(destination_mode, source_mode),
            &address_program::schema(),
        )
        .expect("object transfer");
        assert!(result.all_obligations_proven());
        for present in [
            result.obligations().iter().any(|obligation| {
                matches!(
                    obligation.kind(),
                    ResourceObligationKind::ObjectAllocationLive { .. }
                )
            }),
            result.obligations().iter().any(|obligation| {
                matches!(
                    obligation.kind(),
                    ResourceObligationKind::ObjectWithinBounds { .. }
                )
            }),
            result.obligations().iter().any(|obligation| {
                matches!(
                    obligation.kind(),
                    ResourceObligationKind::ObjectAligned { .. }
                )
            }),
            result.obligations().iter().any(|obligation| {
                matches!(
                    obligation.kind(),
                    ResourceObligationKind::PermissionCoversAccess { .. }
                )
            }),
            result.obligations().iter().any(|obligation| {
                matches!(
                    obligation.kind(),
                    ResourceObligationKind::ObjectValueBytesInitialized { .. }
                )
            }),
            result.obligations().iter().any(|obligation| {
                matches!(
                    obligation.kind(),
                    ResourceObligationKind::ObjectRepresentationValid { .. }
                )
            }),
            result.obligations().iter().any(|obligation| {
                matches!(
                    obligation.kind(),
                    ResourceObligationKind::ObjectNonOverlapping { .. }
                )
            }),
        ] {
            assert!(
                present,
                "object effect must retain every independent proof axis"
            );
        }

        let destination = result
            .state()
            .allocation(AbstractAllocationId::new(0))
            .expect("destination allocation");
        assert_eq!(
            destination.initialization().classify(range(8, 40)),
            InitializationClass::Initialized
        );
        assert!(destination.valid_value_bytes().contains(range(8, 40)));
        assert_eq!(
            destination.initialization().classify(range(0, 8)),
            InitializationClass::MaybeInitialized,
            "padding must remain non-value/unknown"
        );

        let source = result
            .state()
            .allocation(AbstractAllocationId::new(1))
            .expect("source allocation");
        assert_eq!(
            source.initialization().classify(range(8, 40)),
            if matches!(source_mode, VirObjectSourceMode::Move) {
                InitializationClass::Uninitialized
            } else {
                InitializationClass::Initialized
            }
        );
    }
}

#[test]
fn partial_source_and_overlap_fail_closed_with_distinct_obligations() {
    let partial = transfer_instruction_with_memory(
        &record_state(false, 24),
        &object_transfer(
            VirObjectDestinationMode::Initialize,
            VirObjectSourceMode::Copy,
        ),
        &address_program::schema(),
    )
    .expect("partial object transfer");
    assert!(partial.obligations().iter().any(|obligation| {
        matches!(
            obligation.kind(),
            ResourceObligationKind::ObjectValueBytesInitialized { .. }
        ) && obligation.status() == ObligationStatus::Unknown
    }));

    let allocation = AbstractAllocationId::new(4);
    let mut state = ResourceState::new();
    let mut bytes = AbstractAllocation::new_local(80, 8).expect("shared allocation");
    bytes.mark_initialized(range(0, 80)).unwrap();
    bytes.mark_valid(range(0, 80)).unwrap();
    state.define_allocation(allocation, bytes).unwrap();
    for (id, offset) in [(0, 0), (2, 8)] {
        state
            .define_value(
                VirValueId::new(id),
                pointer(allocation, offset, address_program::RECORD_ACCESS),
            )
            .unwrap();
    }
    for id in [1, 3] {
        state
            .define_value(VirValueId::new(id), permission(allocation, 80))
            .unwrap();
    }
    let overlap = transfer_instruction_with_memory(
        &state,
        &object_transfer(VirObjectDestinationMode::Replace, VirObjectSourceMode::Copy),
        &address_program::schema(),
    )
    .expect("overlap is an obligation, not a transfer error");
    assert!(overlap.obligations().iter().any(|obligation| {
        matches!(
            obligation.kind(),
            ResourceObligationKind::ObjectNonOverlapping { .. }
        ) && obligation.status() == ObligationStatus::Refuted
    }));
}

#[test]
fn explicit_deinitialize_removes_only_value_bytes() {
    let input = record_state(false, 40);
    let result = transfer_instruction_with_memory(
        &input,
        &instruction(VirInstruction::ObjectDeinitialize {
            pointer: VirValueId::new(2),
            permission: VirValueId::new(3),
            access: address_program::RECORD_ACCESS,
        }),
        &address_program::schema(),
    )
    .expect("object deinitialize");
    assert!(result.all_obligations_proven());
    let source = result
        .state()
        .allocation(AbstractAllocationId::new(1))
        .expect("source allocation");
    assert_eq!(
        source.initialization().classify(range(8, 40)),
        InitializationClass::Uninitialized
    );
    assert_eq!(
        source.initialization().classify(range(0, 8)),
        InitializationClass::MaybeInitialized
    );
    assert!(!source.valid_value_bytes().contains(range(8, 40)));
}

fn enum_schema() -> VirMemorySchema {
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
                id: U64_ACCESS.ty,
                kind: VirMemoryTypeKind::Integer(VirIntegerType::U64),
                layout: U64_ACCESS.layout,
            },
            VirMemoryType {
                id: ENUM_ACCESS.ty,
                kind: VirMemoryTypeKind::Enum {
                    variants: vec![VirVariantId::new(0), VirVariantId::new(1)],
                },
                layout: ENUM_ACCESS.layout,
            },
        ],
        type_capabilities: vec![],
        layouts: vec![
            VirLayout {
                id: U64_ACCESS.layout,
                ty: U64_ACCESS.ty,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: vec![],
                variants: None,
            },
            VirLayout {
                id: ENUM_ACCESS.layout,
                ty: ENUM_ACCESS.ty,
                size_bytes: 16,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![],
                variants: Some(VirVariantLayout {
                    tag_size_bytes: 8,
                    tag_alignment: 8,
                    cases: vec![
                        VirVariantCaseLayout {
                            variant: VirVariantId::new(0),
                            payload_offset_bytes: 8,
                            fields: vec![VirFieldLayout {
                                field: VirFieldId::new(0),
                                offset_bytes: 0,
                            }],
                        },
                        VirVariantCaseLayout {
                            variant: VirVariantId::new(1),
                            payload_offset_bytes: 8,
                            fields: vec![],
                        },
                    ],
                }),
            },
        ],
        fields: vec![VirField {
            id: VirFieldId::new(0),
            owner: ENUM_ACCESS.ty,
            ty: U64_ACCESS.ty,
        }],
        variants: vec![
            VirVariant {
                id: VirVariantId::new(0),
                owner: ENUM_ACCESS.ty,
                fields: vec![VirFieldId::new(0)],
                discriminant: 0,
            },
            VirVariant {
                id: VirVariantId::new(1),
                owner: ENUM_ACCESS.ty,
                fields: vec![],
                discriminant: 1,
            },
        ],
    };
    schema.assign_canonical_type_capabilities().unwrap();
    schema
}

fn enum_state(active: ActiveVariantState) -> ResourceState {
    let allocation_id = AbstractAllocationId::new(9);
    let mut allocation = AbstractAllocation::new_local(16, 8).expect("enum allocation");
    allocation
        .set_active_variant(ObjectStateKey::new(0, ENUM_ACCESS), active)
        .expect("enum key in bounds");
    let mut state = ResourceState::new();
    state.define_allocation(allocation_id, allocation).unwrap();
    state
        .define_value(VirValueId::new(0), pointer(allocation_id, 0, ENUM_ACCESS))
        .unwrap();
    state
        .define_value(VirValueId::new(1), permission(allocation_id, 16))
        .unwrap();
    state
}

fn set_discriminant(variant: u32, mode: VirObjectDestinationMode) -> SpannedVirInstruction {
    instruction(VirInstruction::EnumSetDiscriminant {
        pointer: VirValueId::new(0),
        permission: VirValueId::new(1),
        access: ENUM_ACCESS,
        variant: VirVariantId::new(variant),
        mode,
    })
}

#[test]
fn discriminant_state_gates_inactive_payload_even_when_bytes_are_initialized() {
    let schema = enum_schema();
    let allocation_id = AbstractAllocationId::new(9);
    let mut unknown = enum_state(ActiveVariantState::Unknown);
    unknown
        .allocation_mut(allocation_id)
        .unwrap()
        .mark_initialized(range(8, 16))
        .unwrap();
    unknown
        .allocation_mut(allocation_id)
        .unwrap()
        .mark_valid(range(8, 16))
        .unwrap();
    unknown
        .define_value(VirValueId::new(2), pointer(allocation_id, 8, U64_ACCESS))
        .unwrap();
    let unknown_read = transfer_instruction_with_memory(
        &unknown,
        &instruction(VirInstruction::Load {
            result: value(3, VirType::U64),
            pointer: VirValueId::new(2),
            permission: VirValueId::new(1),
            access: U64_ACCESS,
        }),
        &schema,
    )
    .expect("unknown active variant is an obligation");
    assert!(unknown_read.obligations().iter().any(|obligation| {
        matches!(
            obligation.kind(),
            ResourceObligationKind::ActiveVariantAllowsAccess { .. }
        ) && obligation.status() == ObligationStatus::Unknown
    }));

    let initialized = transfer_instruction_with_memory(
        &enum_state(ActiveVariantState::Unknown),
        &set_discriminant(0, VirObjectDestinationMode::Initialize),
        &schema,
    )
    .expect("initialize tag");
    assert!(initialized.all_obligations_proven());
    assert_eq!(
        initialized
            .state()
            .allocation(allocation_id)
            .unwrap()
            .active_variant(ObjectStateKey::new(0, ENUM_ACCESS)),
        ActiveVariantState::Exact(VirVariantId::new(0))
    );

    let mut with_payload = initialized.state().clone();
    with_payload
        .define_value(VirValueId::new(2), pointer(allocation_id, 8, U64_ACCESS))
        .unwrap();
    with_payload
        .define_value(
            VirValueId::new(3),
            AbstractValue::U64(U64Interval::exact(7)),
        )
        .unwrap();
    let payload = transfer_instruction_with_memory(
        &with_payload,
        &instruction(VirInstruction::Initialize {
            pointer: VirValueId::new(2),
            value: VirValueId::new(3),
            permission: VirValueId::new(1),
            access: U64_ACCESS,
        }),
        &schema,
    )
    .expect("initialize active payload");
    assert!(payload.all_obligations_proven());

    let switched = transfer_instruction_with_memory(
        payload.state(),
        &set_discriminant(1, VirObjectDestinationMode::Replace),
        &schema,
    )
    .expect("replace tag");
    assert!(switched.all_obligations_proven());
    assert_eq!(
        switched
            .state()
            .allocation(allocation_id)
            .unwrap()
            .initialization()
            .classify(range(8, 16)),
        InitializationClass::Uninitialized,
        "switching variants must not resurrect an old payload"
    );
    let inactive_read = transfer_instruction_with_memory(
        switched.state(),
        &instruction(VirInstruction::Load {
            result: value(4, VirType::U64),
            pointer: VirValueId::new(2),
            permission: VirValueId::new(1),
            access: U64_ACCESS,
        }),
        &schema,
    )
    .expect("inactive payload is reported as an obligation");
    assert!(inactive_read.obligations().iter().any(|obligation| {
        matches!(
            obligation.kind(),
            ResourceObligationKind::ActiveVariantAllowsAccess { .. }
        ) && obligation.status() == ObligationStatus::Refuted
    }));
}

#[test]
fn enum_replace_retires_value_bytes_that_are_absent_from_the_source_variant() {
    let destination_id = AbstractAllocationId::new(20);
    let source_id = AbstractAllocationId::new(21);
    let mut destination = AbstractAllocation::new_local(16, 8).unwrap();
    destination.mark_initialized(range(0, 16)).unwrap();
    destination.mark_valid(range(0, 16)).unwrap();
    destination
        .set_active_variant(
            ObjectStateKey::new(0, ENUM_ACCESS),
            ActiveVariantState::Exact(VirVariantId::new(0)),
        )
        .unwrap();
    let mut source = AbstractAllocation::new_local(16, 8).unwrap();
    source.mark_initialized(range(0, 8)).unwrap();
    source.mark_valid(range(0, 8)).unwrap();
    source
        .set_active_variant(
            ObjectStateKey::new(0, ENUM_ACCESS),
            ActiveVariantState::Exact(VirVariantId::new(1)),
        )
        .unwrap();

    let mut state = ResourceState::new();
    state
        .define_allocation(destination_id, destination)
        .unwrap();
    state.define_allocation(source_id, source).unwrap();
    state
        .define_value(VirValueId::new(0), pointer(destination_id, 0, ENUM_ACCESS))
        .unwrap();
    state
        .define_value(VirValueId::new(1), permission(destination_id, 16))
        .unwrap();
    state
        .define_value(VirValueId::new(2), pointer(source_id, 0, ENUM_ACCESS))
        .unwrap();
    state
        .define_value(VirValueId::new(3), permission(source_id, 16))
        .unwrap();
    let result = transfer_instruction_with_memory(
        &state,
        &instruction(VirInstruction::ObjectTransfer {
            destination: VirValueId::new(0),
            destination_permission: VirValueId::new(1),
            source: VirValueId::new(2),
            source_permission: VirValueId::new(3),
            access: ENUM_ACCESS,
            destination_mode: VirObjectDestinationMode::Replace,
            source_mode: VirObjectSourceMode::Copy,
        }),
        &enum_schema(),
    )
    .expect("enum replace transfer");
    assert!(result.all_obligations_proven());
    let destination = result.state().allocation(destination_id).unwrap();
    assert_eq!(
        destination.active_variant(ObjectStateKey::new(0, ENUM_ACCESS)),
        ActiveVariantState::Exact(VirVariantId::new(1))
    );
    assert_eq!(
        destination.initialization().classify(range(0, 8)),
        InitializationClass::Initialized
    );
    assert_eq!(
        destination.initialization().classify(range(8, 16)),
        InitializationClass::Uninitialized
    );
}

#[test]
fn variant_join_is_commutative_idempotent_associative_and_widening_stable() {
    let key = ObjectStateKey::new(0, ENUM_ACCESS);
    let make = |variant| {
        let mut state = enum_state(ActiveVariantState::Exact(VirVariantId::new(variant)));
        let allocation = state
            .allocation_mut(AbstractAllocationId::new(9))
            .expect("enum allocation");
        allocation.mark_initialized(range(0, 8)).unwrap();
        allocation.mark_valid(range(0, 8)).unwrap();
        state
    };
    let zero = make(0);
    let one = make(1);
    assert_eq!(zero.join(&one).unwrap(), one.join(&zero).unwrap());
    assert_eq!(zero.join(&zero).unwrap(), zero);

    let left = zero.join(&one).unwrap().join(&zero).unwrap();
    let right = zero.join(&one.join(&zero).unwrap()).unwrap();
    assert_eq!(left, right);
    assert_eq!(
        zero.join(&one).unwrap(),
        zero.widen(&zero.join(&one).unwrap()).unwrap()
    );
    assert_eq!(
        left.allocation(AbstractAllocationId::new(9))
            .unwrap()
            .active_variant(key),
        ActiveVariantState::Alternatives(BTreeSet::from([
            VirVariantId::new(0),
            VirVariantId::new(1),
        ]))
    );
}

fn block(
    id: u32,
    parameters: Vec<VirValue>,
    instructions: Vec<SpannedVirInstruction>,
    terminator: VirTerminator,
) -> VirBasicBlock {
    VirBasicBlock {
        id: VirBlockId::new(id),
        parameters,
        instructions,
        terminator: SpannedVirTerminator {
            terminator,
            source_span: span(),
        },
        source_span: span(),
    }
}

fn target(block: u32, arguments: &[u32]) -> VirBlockTarget {
    VirBlockTarget {
        block: VirBlockId::new(block),
        arguments: arguments.iter().copied().map(VirValueId::new).collect(),
    }
}

#[test]
fn cfg_join_retains_finite_variant_alternatives_without_inventing_payload_init() {
    let unit = VirUnit::from_runtime(
        enum_schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "enum_join".to_owned(),
            signature: VirSignature {
                parameters: vec![VirType::Bool],
                results: vec![],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![
                block(
                    0,
                    vec![value(0, VirType::Bool)],
                    vec![instruction(VirInstruction::LocalStorage {
                        pointer_result: pointer_value(1, ENUM_ACCESS),
                        permission_result: permission_value(2),
                        access: ENUM_ACCESS,
                    })],
                    VirTerminator::Branch {
                        condition: VirValueId::new(0),
                        then_target: target(1, &[1, 2]),
                        else_target: target(2, &[1, 2]),
                    },
                ),
                block(
                    1,
                    vec![pointer_value(3, ENUM_ACCESS), permission_value(4)],
                    vec![instruction(VirInstruction::EnumSetDiscriminant {
                        pointer: VirValueId::new(3),
                        permission: VirValueId::new(4),
                        access: ENUM_ACCESS,
                        variant: VirVariantId::new(0),
                        mode: VirObjectDestinationMode::Initialize,
                    })],
                    VirTerminator::Jump {
                        target: target(3, &[3, 4]),
                    },
                ),
                block(
                    2,
                    vec![pointer_value(5, ENUM_ACCESS), permission_value(6)],
                    vec![instruction(VirInstruction::EnumSetDiscriminant {
                        pointer: VirValueId::new(5),
                        permission: VirValueId::new(6),
                        access: ENUM_ACCESS,
                        variant: VirVariantId::new(1),
                        mode: VirObjectDestinationMode::Initialize,
                    })],
                    VirTerminator::Jump {
                        target: target(3, &[5, 6]),
                    },
                ),
                block(
                    3,
                    vec![pointer_value(7, ENUM_ACCESS), permission_value(8)],
                    vec![],
                    VirTerminator::Return { values: vec![] },
                ),
            ],
            source_span: span(),
        }],
    )
    .into_validated()
    .expect("object-effect CFG validates");
    let resolved = unit.resolve().expect("CFG resolves");
    let analysis =
        analyze_function_cfg(&resolved, VirFunctionId::new(0)).expect("CFG object-state analysis");
    assert!(analysis.all_obligations_proven());
    let joined = analysis
        .block(VirBlockId::new(3))
        .expect("join block")
        .entry_state()
        .allocation(AbstractAllocationId::vir_local_storage_site(
            VirValueId::new(1),
        ))
        .expect("local enum allocation");
    assert_eq!(
        joined.active_variant(ObjectStateKey::new(0, ENUM_ACCESS)),
        ActiveVariantState::Alternatives(BTreeSet::from([
            VirVariantId::new(0),
            VirVariantId::new(1),
        ]))
    );
    assert_eq!(
        joined.initialization().classify(range(0, 8)),
        InitializationClass::Initialized
    );
    assert_eq!(
        joined.initialization().classify(range(8, 16)),
        InitializationClass::Uninitialized,
        "neither discriminant effect initializes payload bytes"
    );
}
