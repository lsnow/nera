use nera::{
    AbstractAllocation, AbstractAllocationId, AbstractByteRange, AbstractPermission,
    AbstractPointer, AbstractProvenance, AbstractValue, AccessPermission, ByteRange, ByteSpan,
    FreeCapability, GuaranteedAlignment, InitializationClass, LivenessState, ObligationStatus,
    OwnershipState, PermissionAvailability, ResourceObligationKind, ResourceState,
    SpannedVirInstruction, TransferError, U64Interval, VirCallTarget, VirConstant, VirContractId,
    VirInstruction, VirIntegerPredicate, VirRegionId, VirSignature, VirType, VirValue, VirValueId,
    transfer_instruction, transfer_instruction_sequence, transfer_instruction_sequence_with_memory,
};

#[path = "support/address_program.rs"]
mod address_program;

#[test]
fn dynamic_index_address_retains_one_affine_index_and_nominal_element_type() {
    let validated = address_program::validated();
    let program = validated.runtime();
    let all = &program.functions[0].blocks[0].instructions;
    let instructions = vec![
        all[0].clone(),
        all[1].clone(),
        all[2].clone(),
        all[4].clone(),
    ];
    let mut state = ResourceState::new();
    state
        .define_value(
            VirValueId::new(4),
            AbstractValue::U64(U64Interval::new(0, 3).expect("ordered index interval")),
        )
        .expect("dynamic index is unique");
    let transferred =
        transfer_instruction_sequence_with_memory(&state, &instructions, program.memory)
            .expect("typed address transfer succeeds");
    assert!(transferred.all_obligations_proven());
    let Some(AbstractValue::Pointer(pointer)) =
        transferred.state().value(VirValueId::new(5)).copied()
    else {
        panic!("index address result pointer")
    };
    assert_eq!(
        pointer.offset_bytes(),
        U64Interval::new(8, 32).expect("ordered address interval")
    );
    let expression = pointer
        .offset_expression()
        .expect("dynamic index remains affine");
    assert_eq!(expression.root(), Some(VirValueId::new(4)));
    assert_eq!(expression.scale(), 8);
    assert_eq!(expression.addend(), 8);
    assert_eq!(pointer.memory_access(), Some(address_program::U64_ACCESS));

    let permissions = transferred
        .state()
        .values()
        .values()
        .filter_map(|value| match value {
            AbstractValue::Permission(permission) => Some(permission),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        permissions.len(),
        1,
        "address construction is resource-neutral"
    );
    assert_eq!(
        permissions[0].availability(),
        PermissionAvailability::Available
    );
}

fn span(start: usize) -> ByteSpan {
    ByteSpan::new(start, start + 2).expect("valid test span")
}

fn instruction(start: usize, instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(start),
    }
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

fn constant(start: usize, result: u32, constant: u64) -> SpannedVirInstruction {
    instruction(
        start,
        VirInstruction::Constant {
            result: word(result),
            value: VirConstant::U64(constant),
        },
    )
}

fn allocate(
    start: usize,
    pointer_result: u32,
    permission_result: u32,
    size: u32,
) -> SpannedVirInstruction {
    instruction(
        start,
        VirInstruction::Allocate {
            pointer_result: pointer(pointer_result),
            permission_result: permission(permission_result),
            size_bytes: VirValueId::new(size),
            alignment: 8,
            region: VirRegionId::new(0),
            element: nera::VirMemoryAccess::core_u64(),
        },
    )
}

fn allocation_prefix(size: u64) -> Vec<SpannedVirInstruction> {
    vec![constant(0, 0, size), allocate(2, 1, 2, 0)]
}

fn obligation_status(
    obligations: &[nera::ResourceObligation],
    predicate: impl Fn(ResourceObligationKind) -> bool,
) -> Option<ObligationStatus> {
    obligations
        .iter()
        .find(|obligation| predicate(obligation.kind()))
        .map(nera::ResourceObligation::status)
}

#[test]
fn safe_straight_line_memory_lifecycle_discharges_every_obligation() {
    let mut instructions = allocation_prefix(16);
    instructions.extend([
        constant(4, 3, 41),
        instruction(
            6,
            VirInstruction::Initialize {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
        instruction(
            8,
            VirInstruction::Load {
                result: word(4),
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
        instruction(
            10,
            VirInstruction::Store {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
        instruction(
            12,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);

    let result = transfer_instruction_sequence(&ResourceState::new(), &instructions)
        .expect("valid abstract transfer");

    assert!(result.all_obligations_proven());
    assert!(result.state().path_condition().is_reachable());
    assert!(result.obligations().iter().all(|obligation| {
        instructions
            .iter()
            .any(|instruction| instruction.source_span == obligation.source_span())
    }));
    let allocation = result
        .state()
        .allocation(AbstractAllocationId::vir_allocation_site(VirValueId::new(
            1,
        )))
        .expect("allocation remains tracked after free");
    assert_eq!(allocation.liveness(), LivenessState::Dead);
    assert_eq!(allocation.ownership(), OwnershipState::Unowned);
    let AbstractValue::Permission(permission) = result
        .state()
        .value(VirValueId::new(2))
        .copied()
        .expect("permission fact")
    else {
        panic!("expected permission fact");
    };
    assert_eq!(permission.availability(), PermissionAvailability::Consumed);
}

#[test]
fn initialize_store_and_reinitialize_have_distinct_preconditions() {
    let mut prefix = allocation_prefix(8);
    prefix.push(constant(4, 3, 7));
    let prefix = transfer_instruction_sequence(&ResourceState::new(), &prefix)
        .expect("valid prefix transfer");
    assert!(prefix.all_obligations_proven());

    let store = transfer_instruction(
        prefix.state(),
        &instruction(
            6,
            VirInstruction::Store {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
    )
    .expect("store produces an obligation, not a transfer error");
    assert_eq!(
        obligation_status(store.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::MemoryInitialized { .. }
        )),
        Some(ObligationStatus::Refuted)
    );
    assert!(!store.state().path_condition().is_reachable());

    let initialize_instruction = instruction(
        8,
        VirInstruction::Initialize {
            pointer: VirValueId::new(1),
            value: VirValueId::new(3),
            permission: VirValueId::new(2),
            access: nera::VirMemoryAccess::core_u64(),
        },
    );
    let initialize = transfer_instruction(prefix.state(), &initialize_instruction)
        .expect("valid initialization");
    assert!(initialize.all_obligations_proven());

    let reinitialize = transfer_instruction(initialize.state(), &initialize_instruction)
        .expect("reinitialization produces an obligation");
    assert_eq!(
        obligation_status(reinitialize.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::MemoryUninitialized { .. }
        )),
        Some(ObligationStatus::Refuted)
    );
    assert!(!reinitialize.state().path_condition().is_reachable());
}

#[test]
fn interval_write_preserves_only_definite_initialization_facts() {
    let allocation_id = AbstractAllocationId::new(9);
    let mut state = ResourceState::new();
    state
        .define_allocation(
            allocation_id,
            AbstractAllocation::new(VirRegionId::new(0), 24, 8).expect("valid allocation"),
        )
        .expect("unique allocation");
    state
        .define_value(
            VirValueId::new(1),
            AbstractValue::Pointer(AbstractPointer::new(
                AbstractProvenance::Known(allocation_id),
                U64Interval::new(0, 4).expect("valid interval"),
                GuaranteedAlignment::one(),
            )),
        )
        .expect("unique pointer");
    state
        .define_value(
            VirValueId::new(2),
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(allocation_id),
                AbstractByteRange::Exact(ByteRange::new(0, 24).expect("valid range")),
                AccessPermission::Write,
                FreeCapability::Yes,
            )),
        )
        .expect("unique permission");

    let result = transfer_instruction(
        &state,
        &instruction(
            0,
            VirInstruction::Write {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
    )
    .expect("valid interval transfer");

    assert!(result.state().path_condition().is_reachable());
    assert!(!result.all_obligations_proven());
    assert_eq!(
        obligation_status(result.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::AccessAligned { .. }
        )),
        Some(ObligationStatus::Unknown)
    );
    let initialization = result
        .state()
        .allocation(allocation_id)
        .expect("tracked allocation")
        .initialization();
    assert_eq!(
        initialization.classify(ByteRange::new(4, 8).expect("valid range")),
        InitializationClass::Initialized
    );
    for range in [(0, 4), (8, 12)] {
        assert_eq!(
            initialization.classify(ByteRange::new(range.0, range.1).expect("valid range")),
            InitializationClass::MaybeInitialized
        );
    }
    assert_eq!(
        initialization.classify(ByteRange::new(12, 24).expect("valid range")),
        InitializationClass::Uninitialized
    );
}

#[test]
fn one_access_reports_independent_bounds_alignment_and_permission_faults() {
    let allocation_id = AbstractAllocationId::new(9);
    let other_allocation_id = AbstractAllocationId::new(10);
    let mut state = ResourceState::new();
    state
        .define_allocation(
            allocation_id,
            AbstractAllocation::new(VirRegionId::new(0), 16, 4).expect("valid allocation"),
        )
        .expect("unique allocation");
    state
        .define_value(
            VirValueId::new(1),
            AbstractValue::Pointer(AbstractPointer::new(
                AbstractProvenance::Known(allocation_id),
                U64Interval::exact(12),
                GuaranteedAlignment::new(4).expect("valid alignment"),
            )),
        )
        .expect("unique pointer");
    state
        .define_value(
            VirValueId::new(2),
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(other_allocation_id),
                AbstractByteRange::Exact(ByteRange::new(0, 8).expect("valid range")),
                AccessPermission::Read,
                FreeCapability::No,
            )),
        )
        .expect("unique permission");

    let result = transfer_instruction(
        &state,
        &instruction(
            20,
            VirInstruction::Write {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
    )
    .expect("memory faults remain local obligations");

    for predicate in [
        |kind| matches!(kind, ResourceObligationKind::AccessWithinBounds { .. }),
        |kind| matches!(kind, ResourceObligationKind::AccessAligned { .. }),
        |kind| {
            matches!(
                kind,
                ResourceObligationKind::PermissionMatchesAllocation { .. }
            )
        },
        |kind| matches!(kind, ResourceObligationKind::PermissionCoversAccess { .. }),
        |kind| matches!(kind, ResourceObligationKind::PermissionWritable { .. }),
    ] {
        assert_eq!(
            obligation_status(result.obligations(), predicate),
            Some(ObligationStatus::Refuted)
        );
    }
    assert!(
        result
            .obligations()
            .iter()
            .all(|obligation| obligation.source_span() == span(20))
    );
    assert!(!result.state().path_condition().is_reachable());
}

#[test]
fn partial_permission_coverage_is_unknown_and_keeps_the_successful_subset() {
    let allocation_id = AbstractAllocationId::new(9);
    let mut state = ResourceState::new();
    state
        .define_allocation(
            allocation_id,
            AbstractAllocation::new(VirRegionId::new(0), 16, 8).expect("valid allocation"),
        )
        .expect("unique allocation");
    state
        .define_value(
            VirValueId::new(1),
            AbstractValue::Pointer(AbstractPointer::new(
                AbstractProvenance::Known(allocation_id),
                U64Interval::new(0, 8).expect("valid interval"),
                GuaranteedAlignment::new(8).expect("valid alignment"),
            )),
        )
        .expect("unique pointer");
    state
        .define_value(
            VirValueId::new(2),
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(allocation_id),
                AbstractByteRange::Exact(ByteRange::new(0, 8).expect("valid range")),
                AccessPermission::Write,
                FreeCapability::Yes,
            )),
        )
        .expect("unique permission");

    let result = transfer_instruction(
        &state,
        &instruction(
            0,
            VirInstruction::Write {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
    )
    .expect("partial coverage is an obligation");

    assert_eq!(
        obligation_status(result.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::PermissionCoversAccess { .. }
        )),
        Some(ObligationStatus::Unknown)
    );
    assert!(result.state().path_condition().is_reachable());
    assert!(!result.all_obligations_proven());
}

#[test]
fn maybe_writable_permission_produces_an_unknown_write_obligation() {
    let allocation_id = AbstractAllocationId::new(9);
    let mut state = ResourceState::new();
    state
        .define_allocation(
            allocation_id,
            AbstractAllocation::new(VirRegionId::new(0), 8, 8).expect("valid allocation"),
        )
        .expect("unique allocation");
    state
        .define_value(
            VirValueId::new(1),
            AbstractValue::Pointer(AbstractPointer::new(
                AbstractProvenance::Known(allocation_id),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).expect("valid alignment"),
            )),
        )
        .expect("unique pointer");
    state
        .define_value(
            VirValueId::new(2),
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(allocation_id),
                AbstractByteRange::Exact(ByteRange::new(0, 8).expect("valid range")),
                AccessPermission::MaybeWrite,
                FreeCapability::Maybe,
            )),
        )
        .expect("unique permission");

    let result = transfer_instruction(
        &state,
        &instruction(
            0,
            VirInstruction::Write {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
    )
    .expect("unknown writability remains an obligation");

    assert_eq!(
        obligation_status(result.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::PermissionWritable { .. }
        )),
        Some(ObligationStatus::Unknown)
    );
    assert!(result.state().path_condition().is_reachable());
}

#[test]
fn use_after_free_and_consumed_permission_are_refuted_locally() {
    let mut instructions = allocation_prefix(8);
    instructions.extend([
        constant(4, 3, 1),
        instruction(
            6,
            VirInstruction::Initialize {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
        instruction(
            8,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);
    let freed = transfer_instruction_sequence(&ResourceState::new(), &instructions)
        .expect("safe prefix and free");
    assert!(freed.all_obligations_proven());

    let load = transfer_instruction(
        freed.state(),
        &instruction(
            10,
            VirInstruction::Load {
                result: word(4),
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
    )
    .expect("memory fault remains an obligation");

    assert_eq!(
        obligation_status(load.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::AllocationLive { .. }
        )),
        Some(ObligationStatus::Refuted)
    );
    assert_eq!(
        obligation_status(load.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::PermissionAvailable { .. }
        )),
        Some(ObligationStatus::Refuted)
    );
    assert!(!load.state().path_condition().is_reachable());
}

#[test]
fn pointer_offsets_track_bounds_provenance_and_alignment() {
    let mut safe = allocation_prefix(16);
    safe.extend([
        constant(4, 3, 8),
        instruction(
            6,
            VirInstruction::PointerOffset {
                result: pointer(4),
                base: VirValueId::new(1),
                delta_bytes: VirValueId::new(3),
            },
        ),
    ]);
    let safe =
        transfer_instruction_sequence(&ResourceState::new(), &safe).expect("valid offset transfer");
    assert!(safe.all_obligations_proven());
    let AbstractValue::Pointer(offset_pointer) = safe
        .state()
        .value(VirValueId::new(4))
        .copied()
        .expect("offset result")
    else {
        panic!("expected pointer result");
    };
    assert_eq!(offset_pointer.offset_bytes(), U64Interval::exact(8));
    assert_eq!(offset_pointer.alignment().bytes(), 8);

    let mut out_of_bounds = allocation_prefix(16);
    out_of_bounds.extend([
        constant(4, 3, 24),
        instruction(
            6,
            VirInstruction::PointerOffset {
                result: pointer(4),
                base: VirValueId::new(1),
                delta_bytes: VirValueId::new(3),
            },
        ),
    ]);
    let out_of_bounds = transfer_instruction_sequence(&ResourceState::new(), &out_of_bounds)
        .expect("out-of-bounds offset produces an obligation");
    assert_eq!(
        obligation_status(out_of_bounds.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::PointerOffsetWithinBounds { .. }
        )),
        Some(ObligationStatus::Refuted)
    );
    assert!(!out_of_bounds.state().path_condition().is_reachable());
}

#[test]
fn invalid_free_reports_each_failed_resource_precondition() {
    let allocation_id = AbstractAllocationId::new(9);
    let mut allocation =
        AbstractAllocation::new(VirRegionId::new(0), 16, 8).expect("valid allocation");
    allocation.set_ownership(OwnershipState::Unowned);
    let mut state = ResourceState::new();
    state
        .define_allocation(allocation_id, allocation)
        .expect("unique allocation");
    state
        .define_value(
            VirValueId::new(1),
            AbstractValue::Pointer(AbstractPointer::new(
                AbstractProvenance::Known(allocation_id),
                U64Interval::exact(8),
                GuaranteedAlignment::new(8).expect("valid alignment"),
            )),
        )
        .expect("unique pointer");
    state
        .define_value(
            VirValueId::new(2),
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(allocation_id),
                AbstractByteRange::Exact(ByteRange::new(8, 16).expect("valid range")),
                AccessPermission::Write,
                FreeCapability::No,
            )),
        )
        .expect("unique permission");

    let result = transfer_instruction(
        &state,
        &instruction(
            0,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    )
    .expect("invalid free produces obligations");

    for predicate in [
        |kind| matches!(kind, ResourceObligationKind::PointerAtAllocationBase { .. }),
        |kind| matches!(kind, ResourceObligationKind::AllocationOwned { .. }),
        |kind| matches!(kind, ResourceObligationKind::PermissionCanFree { .. }),
        |kind| {
            matches!(
                kind,
                ResourceObligationKind::PermissionCoversAllocation { .. }
            )
        },
    ] {
        assert_eq!(
            obligation_status(result.obligations(), predicate),
            Some(ObligationStatus::Refuted)
        );
    }
    assert!(!result.state().path_condition().is_reachable());
}

#[test]
fn permissions_split_join_and_move_linearly() {
    let mut instructions = allocation_prefix(16);
    instructions.extend([
        constant(4, 3, 8),
        instruction(
            6,
            VirInstruction::PermissionSplit {
                left_result: permission(4),
                right_result: permission(5),
                source: VirValueId::new(2),
                split_at_bytes: VirValueId::new(3),
            },
        ),
        instruction(
            8,
            VirInstruction::PermissionJoin {
                result: permission(6),
                left: VirValueId::new(4),
                right: VirValueId::new(5),
            },
        ),
        instruction(
            10,
            VirInstruction::PermissionMove {
                result: permission(7),
                source: VirValueId::new(6),
            },
        ),
    ]);

    let result = transfer_instruction_sequence(&ResourceState::new(), &instructions)
        .expect("valid permission transfer");
    assert!(result.all_obligations_proven());
    for id in [2, 4, 5, 6] {
        let AbstractValue::Permission(permission) = result
            .state()
            .value(VirValueId::new(id))
            .copied()
            .expect("permission fact")
        else {
            panic!("expected permission fact");
        };
        assert_eq!(permission.availability(), PermissionAvailability::Consumed);
    }
    let AbstractValue::Permission(moved) = result
        .state()
        .value(VirValueId::new(7))
        .copied()
        .expect("moved permission")
    else {
        panic!("expected permission fact");
    };
    assert_eq!(moved.availability(), PermissionAvailability::Available);
    assert_eq!(
        moved.range(),
        AbstractByteRange::Exact(ByteRange::new(0, 16).expect("valid range"))
    );
}

#[test]
fn joining_one_permission_with_itself_is_explicitly_refuted() {
    let allocation_id = AbstractAllocationId::new(0);
    let mut state = ResourceState::new();
    state
        .define_value(
            VirValueId::new(1),
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(allocation_id),
                AbstractByteRange::Exact(ByteRange::new(0, 8).expect("valid range")),
                AccessPermission::Write,
                FreeCapability::Yes,
            )),
        )
        .expect("unique permission");

    let result = transfer_instruction(
        &state,
        &instruction(
            0,
            VirInstruction::PermissionJoin {
                result: permission(2),
                left: VirValueId::new(1),
                right: VirValueId::new(1),
            },
        ),
    )
    .expect("linear misuse is an obligation");

    assert_eq!(
        obligation_status(result.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::PermissionOperandsDistinct { .. }
        )),
        Some(ObligationStatus::Refuted)
    );
    assert!(!result.state().path_condition().is_reachable());
}

#[test]
fn missing_permission_facts_do_not_imply_linear_availability() {
    let result = transfer_instruction(
        &ResourceState::new(),
        &instruction(
            0,
            VirInstruction::PermissionMove {
                result: permission(1),
                source: VirValueId::new(0),
            },
        ),
    )
    .expect("missing precision produces an obligation");

    assert_eq!(
        obligation_status(result.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::PermissionAvailable { .. }
        )),
        Some(ObligationStatus::Unknown)
    );
    assert!(!result.all_obligations_proven());
    assert!(result.state().path_condition().is_reachable());
    let AbstractValue::Permission(moved) = result
        .state()
        .value(VirValueId::new(1))
        .copied()
        .expect("conditional move result")
    else {
        panic!("expected permission fact");
    };
    assert_eq!(moved.availability(), PermissionAvailability::Available);
}

#[test]
fn scalar_transfer_is_deterministic_and_uses_wrapping_word_arithmetic() {
    let instructions = vec![
        constant(0, 0, u64::MAX),
        constant(2, 1, 1),
        instruction(
            4,
            VirInstruction::WordAdd {
                result: word(2),
                left: VirValueId::new(0),
                right: VirValueId::new(1),
            },
        ),
        instruction(
            6,
            VirInstruction::Compare {
                result: boolean(3),
                predicate: VirIntegerPredicate::Equal,
                left: VirValueId::new(2),
                right: VirValueId::new(2),
            },
        ),
        instruction(
            8,
            VirInstruction::Check {
                condition: VirValueId::new(3),
            },
        ),
    ];

    let first = transfer_instruction_sequence(&ResourceState::new(), &instructions)
        .expect("valid scalar transfer");
    let second = transfer_instruction_sequence(&ResourceState::new(), &instructions)
        .expect("deterministic scalar transfer");
    assert_eq!(first, second);
    assert!(first.all_obligations_proven());
    assert_eq!(
        first.state().value(VirValueId::new(2)),
        Some(&AbstractValue::U64(U64Interval::exact(0)))
    );
}

#[test]
fn potentially_wrapping_word_add_drops_affine_correlation() {
    let mut state = ResourceState::new();
    state
        .define_value(
            VirValueId::new(0),
            AbstractValue::U64(U64Interval::new(u64::MAX - 1, u64::MAX).unwrap()),
        )
        .expect("unique input");

    let transferred = transfer_instruction(
        &state,
        &instruction(
            0,
            VirInstruction::WordAdd {
                result: word(1),
                left: VirValueId::new(0),
                right: VirValueId::new(0),
            },
        ),
    )
    .expect("wrapping addition remains valid runtime VIR");

    assert_eq!(
        transferred.state().value(VirValueId::new(1)),
        Some(&AbstractValue::U64(U64Interval::unknown()))
    );
    assert_eq!(
        transferred.state().word_expression(VirValueId::new(1)),
        None,
        "a mathematical affine term must not describe a potentially wrapping result"
    );
}

#[test]
fn every_integer_predicate_uses_unsigned_interval_semantics() {
    let predicates = [
        (VirIntegerPredicate::Equal, nera::AbstractBool::False),
        (VirIntegerPredicate::NotEqual, nera::AbstractBool::True),
        (VirIntegerPredicate::LessThan, nera::AbstractBool::True),
        (VirIntegerPredicate::LessOrEqual, nera::AbstractBool::True),
        (VirIntegerPredicate::GreaterThan, nera::AbstractBool::False),
        (
            VirIntegerPredicate::GreaterOrEqual,
            nera::AbstractBool::False,
        ),
    ];
    let mut instructions = vec![constant(0, 0, 2), constant(2, 1, 3)];
    for (index, (predicate, _)) in predicates.iter().enumerate() {
        instructions.push(instruction(
            4 + index * 2,
            VirInstruction::Compare {
                result: boolean(2 + u32::try_from(index).expect("small index")),
                predicate: *predicate,
                left: VirValueId::new(0),
                right: VirValueId::new(1),
            },
        ));
    }

    let result = transfer_instruction_sequence(&ResourceState::new(), &instructions)
        .expect("valid comparison transfer");
    for (index, (_, expected)) in predicates.iter().enumerate() {
        assert_eq!(
            result.state().value(VirValueId::new(
                2 + u32::try_from(index).expect("small index")
            )),
            Some(&AbstractValue::Bool(*expected))
        );
    }
}

#[test]
fn comparisons_preserve_same_ssa_value_correlation() {
    let predicates = [
        (VirIntegerPredicate::Equal, nera::AbstractBool::True),
        (VirIntegerPredicate::NotEqual, nera::AbstractBool::False),
        (VirIntegerPredicate::LessThan, nera::AbstractBool::False),
        (VirIntegerPredicate::LessOrEqual, nera::AbstractBool::True),
        (VirIntegerPredicate::GreaterThan, nera::AbstractBool::False),
        (
            VirIntegerPredicate::GreaterOrEqual,
            nera::AbstractBool::True,
        ),
    ];
    let mut state = ResourceState::new();
    state
        .define_value(
            VirValueId::new(0),
            AbstractValue::U64(U64Interval::unknown()),
        )
        .expect("unique unknown value");

    for (index, (predicate, expected)) in predicates.iter().enumerate() {
        let result_id = 1 + u32::try_from(index).expect("small index");
        let result = transfer_instruction(
            &state,
            &instruction(
                index * 2,
                VirInstruction::Compare {
                    result: boolean(result_id),
                    predicate: *predicate,
                    left: VirValueId::new(0),
                    right: VirValueId::new(0),
                },
            ),
        )
        .expect("same-value comparison transfer");
        assert_eq!(
            result.state().value(VirValueId::new(result_id)),
            Some(&AbstractValue::Bool(*expected))
        );
    }
}

#[test]
fn runtime_checks_distinguish_refuted_and_conditional_success_paths() {
    let false_check = transfer_instruction_sequence(
        &ResourceState::new(),
        &[
            instruction(
                0,
                VirInstruction::Constant {
                    result: boolean(0),
                    value: VirConstant::Bool(false),
                },
            ),
            instruction(
                2,
                VirInstruction::Check {
                    condition: VirValueId::new(0),
                },
            ),
        ],
    )
    .expect("false check produces an obligation");
    assert_eq!(
        obligation_status(false_check.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::CheckTrue { .. }
        )),
        Some(ObligationStatus::Refuted)
    );
    assert!(!false_check.state().path_condition().is_reachable());

    let unknown_check = transfer_instruction(
        &ResourceState::new(),
        &instruction(
            4,
            VirInstruction::Check {
                condition: VirValueId::new(1),
            },
        ),
    )
    .expect("unknown check has a conditional continuation");
    assert_eq!(
        unknown_check.obligations()[0].status(),
        ObligationStatus::Unknown
    );
    assert!(unknown_check.state().path_condition().is_reachable());
    assert!(
        unknown_check
            .state()
            .path_condition()
            .implies(nera::PathFact::boolean(VirValueId::new(1), true))
    );
}

#[test]
fn imprecise_and_zero_allocations_are_not_silently_accepted() {
    let mut imprecise_state = ResourceState::new();
    imprecise_state
        .define_value(
            VirValueId::new(0),
            AbstractValue::U64(U64Interval::new(0, 16).expect("valid interval")),
        )
        .expect("unique size value");
    let imprecise = transfer_instruction(&imprecise_state, &allocate(0, 1, 2, 0))
        .expect("imprecision produces unknown obligations");
    assert_eq!(
        obligation_status(imprecise.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::AllocationExtentExact { .. }
        )),
        Some(ObligationStatus::Unknown)
    );
    assert!(imprecise.state().path_condition().is_reachable());
    assert!(!imprecise.all_obligations_proven());

    let zero = transfer_instruction_sequence(&ResourceState::new(), &allocation_prefix(0))
        .expect("zero allocation produces a refuted obligation");
    assert_eq!(
        obligation_status(zero.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::AllocationSizeNonZero { .. }
        )),
        Some(ObligationStatus::Refuted)
    );
    assert!(!zero.state().path_condition().is_reachable());
}

#[test]
fn local_allocation_sites_do_not_collide_with_external_identities() {
    let external = AbstractAllocationId::new(1);
    let local = AbstractAllocationId::vir_allocation_site(VirValueId::new(1));
    let mut state = ResourceState::new();
    state
        .define_allocation(
            external,
            AbstractAllocation::new(VirRegionId::new(0), 8, 8).expect("valid allocation"),
        )
        .expect("unique external allocation");
    state
        .define_value(
            VirValueId::new(0),
            AbstractValue::U64(U64Interval::exact(8)),
        )
        .expect("unique size");

    let result = transfer_instruction(&state, &allocate(0, 1, 2, 0))
        .expect("local allocation namespace is disjoint");

    assert!(result.all_obligations_proven());
    assert!(result.state().allocation(external).is_some());
    assert!(result.state().allocation(local).is_some());
}

#[test]
fn escaped_alias_cannot_use_the_next_instances_fresh_permission() {
    let mut first = allocation_prefix(8);
    first.push(instruction(
        4,
        VirInstruction::Free {
            pointer: VirValueId::new(1),
            permission: VirValueId::new(2),
        },
    ));
    let retired = transfer_instruction_sequence(&ResourceState::new(), &first).unwrap();
    assert!(retired.all_obligations_proven());
    let slot = AbstractAllocationId::vir_allocation_site(VirValueId::new(1));
    // Simulate CFG renaming of escaping values, both with and without the dead
    // allocation tombstone (which an absent-predecessor join may discard).
    for retain_tombstone in [false, true] {
        let mut entry = ResourceState::new();
        if retain_tombstone {
            entry
                .define_allocation(slot, retired.state().allocation(slot).unwrap().clone())
                .unwrap();
        }
        entry
            .define_value(
                VirValueId::new(98),
                *retired.state().value(VirValueId::new(2)).unwrap(),
            )
            .unwrap();
        entry
            .define_value(
                VirValueId::new(99),
                *retired.state().value(VirValueId::new(1)).unwrap(),
            )
            .unwrap();
        let mut next = allocation_prefix(8);
        next.extend([
            constant(6, 3, 42),
            instruction(
                8,
                VirInstruction::Initialize {
                    pointer: VirValueId::new(1),
                    value: VirValueId::new(3),
                    permission: VirValueId::new(2),
                    access: nera::VirMemoryAccess::core_u64(),
                },
            ),
        ]);
        let fresh = transfer_instruction_sequence(&entry, &next).unwrap();
        assert!(fresh.all_obligations_proven());
        let stale_access = transfer_instruction(
            fresh.state(),
            &instruction(
                10,
                VirInstruction::Load {
                    result: word(4),
                    pointer: VirValueId::new(99),
                    permission: VirValueId::new(2),
                    access: nera::VirMemoryAccess::core_u64(),
                },
            ),
        )
        .unwrap();
        assert_eq!(
            obligation_status(stale_access.obligations(), |k| matches!(
                k,
                ResourceObligationKind::PointerProvenanceKnown { .. }
            )),
            Some(ObligationStatus::Unknown)
        );
        let stale_free = transfer_instruction(
            fresh.state(),
            &instruction(
                12,
                VirInstruction::Free {
                    pointer: VirValueId::new(1),
                    permission: VirValueId::new(98),
                },
            ),
        )
        .unwrap();
        assert_eq!(
            obligation_status(stale_free.obligations(), |k| matches!(
                k,
                ResourceObligationKind::PermissionAvailable { .. }
            )),
            Some(ObligationStatus::Refuted)
        );
    }
}

#[test]
fn calls_fail_closed_until_contract_transfer_exists() {
    let call = instruction(
        0,
        VirInstruction::Call {
            results: vec![word(0)],
            target: VirCallTarget {
                symbol: "opaque".to_owned(),
                signature: VirSignature {
                    parameters: Vec::new(),
                    results: vec![VirType::U64],
                },
                contract: VirContractId::new(7),
                abi: None,
            },
            arguments: Vec::new(),
        },
    );

    let result = transfer_instruction(&ResourceState::new(), &call).expect("valid call transfer");
    assert_eq!(result.obligations().len(), 1);
    assert_eq!(result.obligations()[0].status(), ObligationStatus::Unknown);
    assert!(matches!(
        result.obligations()[0].kind(),
        ResourceObligationKind::CallContractAvailable { contract }
            if contract == VirContractId::new(7)
    ));
    assert!(result.state().path_condition().is_reachable());
    assert_eq!(
        result.state().value(VirValueId::new(0)),
        Some(&AbstractValue::U64(U64Interval::unknown()))
    );
}

#[test]
fn calls_move_permission_arguments_before_contract_elaboration() {
    let allocation_id = AbstractAllocationId::new(9);
    let mut state = ResourceState::new();
    state
        .define_value(
            VirValueId::new(0),
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(allocation_id),
                AbstractByteRange::Exact(ByteRange::new(0, 8).expect("valid range")),
                AccessPermission::Write,
                FreeCapability::Yes,
            )),
        )
        .expect("unique permission");
    let call = instruction(
        0,
        VirInstruction::Call {
            results: vec![permission(1)],
            target: VirCallTarget {
                symbol: "move_permission".to_owned(),
                signature: VirSignature {
                    parameters: vec![VirType::Permission],
                    results: vec![VirType::Permission],
                },
                contract: VirContractId::new(7),
                abi: None,
            },
            arguments: vec![VirValueId::new(0)],
        },
    );

    let result = transfer_instruction(&state, &call).expect("valid structural call transfer");

    assert_eq!(
        obligation_status(result.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::PermissionAvailable { permission }
                if permission == VirValueId::new(0)
        )),
        Some(ObligationStatus::Proven)
    );
    let AbstractValue::Permission(argument) = result
        .state()
        .value(VirValueId::new(0))
        .copied()
        .expect("argument permission")
    else {
        panic!("expected permission argument");
    };
    let AbstractValue::Permission(returned) = result
        .state()
        .value(VirValueId::new(1))
        .copied()
        .expect("returned permission")
    else {
        panic!("expected permission result");
    };
    assert_eq!(argument.availability(), PermissionAvailability::Consumed);
    assert_eq!(returned.availability(), PermissionAvailability::Available);
    assert_eq!(returned.access(), AccessPermission::MaybeWrite);
    assert!(!result.all_obligations_proven());
}

#[test]
fn calls_refute_duplicated_permission_arguments() {
    let mut state = ResourceState::new();
    state
        .define_value(
            VirValueId::new(0),
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Unknown,
                AbstractByteRange::Unknown,
                AccessPermission::MaybeWrite,
                FreeCapability::Maybe,
            )),
        )
        .expect("unique permission");
    let call = instruction(
        0,
        VirInstruction::Call {
            results: Vec::new(),
            target: VirCallTarget {
                symbol: "duplicate_permission".to_owned(),
                signature: VirSignature {
                    parameters: vec![VirType::Permission, VirType::Permission],
                    results: Vec::new(),
                },
                contract: VirContractId::new(8),
                abi: None,
            },
            arguments: vec![VirValueId::new(0), VirValueId::new(0)],
        },
    );

    let result = transfer_instruction(&state, &call).expect("duplicate is a local obligation");

    assert_eq!(
        obligation_status(result.obligations(), |kind| matches!(
            kind,
            ResourceObligationKind::PermissionOperandsDistinct { left, right }
                if left == VirValueId::new(0) && right == VirValueId::new(0)
        )),
        Some(ObligationStatus::Refuted)
    );
    assert!(!result.state().path_condition().is_reachable());
}

#[test]
fn calls_reject_abstract_argument_type_contradictions() {
    let mut state = ResourceState::new();
    state
        .define_value(
            VirValueId::new(0),
            AbstractValue::Bool(nera::AbstractBool::True),
        )
        .expect("unique argument fact");
    let call = instruction(
        0,
        VirInstruction::Call {
            results: Vec::new(),
            target: VirCallTarget {
                symbol: "expects_word".to_owned(),
                signature: VirSignature {
                    parameters: vec![VirType::U64],
                    results: Vec::new(),
                },
                contract: VirContractId::new(9),
                abi: None,
            },
            arguments: vec![VirValueId::new(0)],
        },
    );

    let error = transfer_instruction(&state, &call)
        .expect_err("call argument type contradiction must fail closed");

    assert_eq!(
        error,
        TransferError::AbstractValueTypeMismatch {
            value: VirValueId::new(0),
            expected: VirType::U64,
            found: VirType::Bool,
        }
    );
}

#[test]
fn ignored_runtime_values_still_enforce_abstract_state_types() {
    let mut state = ResourceState::new();
    state
        .define_value(
            VirValueId::new(3),
            AbstractValue::Bool(nera::AbstractBool::True),
        )
        .expect("unique mismatched value");

    let error = transfer_instruction(
        &state,
        &instruction(
            0,
            VirInstruction::Write {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: nera::VirMemoryAccess::core_u64(),
            },
        ),
    )
    .expect_err("write value type mismatch must fail closed");

    assert_eq!(
        error,
        TransferError::AbstractValueTypeMismatch {
            value: VirValueId::new(3),
            expected: VirType::U64,
            found: VirType::Bool,
        }
    );
}

#[test]
fn abstract_state_type_contradictions_are_transfer_errors() {
    let mut state = ResourceState::new();
    state
        .define_value(
            VirValueId::new(0),
            AbstractValue::Bool(nera::AbstractBool::True),
        )
        .expect("unique value");
    let error = transfer_instruction(
        &state,
        &instruction(
            0,
            VirInstruction::WordAdd {
                result: word(2),
                left: VirValueId::new(0),
                right: VirValueId::new(1),
            },
        ),
    )
    .expect_err("type contradiction must not become an unknown fact");

    assert_eq!(
        error,
        TransferError::AbstractValueTypeMismatch {
            value: VirValueId::new(0),
            expected: VirType::U64,
            found: VirType::Bool,
        }
    );
}
