#[path = "support/address_program.rs"]
mod address_program;

use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64InstructionPlan, X86_64PlanningErrorKind};
use nera::{
    ByteSpan, ObligationStatus, ResourceObligationKind, ResourceState, SpannedVirInstruction,
    SpannedVirTerminator, VirAbiClass, VirBasicBlock, VirBlockId, VirContractId,
    VirExecutionErrorKind, VirFunction, VirFunctionId, VirInstruction, VirLayout, VirLayoutId,
    VirLocation, VirMemoryAccess, VirMemoryType, VirMemoryTypeKind, VirMutability,
    VirObjectDestinationMode, VirObjectShapeErrorKind, VirObjectSourceMode, VirPointerKind,
    VirSignature, VirTerminator, VirType, VirTypeId, VirUnit, VirValidationErrorKind, VirValue,
    VirValueId, VirVariant, VirVariantCaseLayout, VirVariantId, VirVariantLayout, interpret,
    transfer_instruction_with_memory,
};

const ENUM_ACCESS: VirMemoryAccess = VirMemoryAccess::new(VirTypeId::new(3), VirLayoutId::new(3));

fn span() -> ByteSpan {
    ByteSpan::new(0, 1).expect("ordered span")
}

fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

fn pointer(id: u32, access: VirMemoryAccess) -> VirValue {
    value(id, VirType::Pointer { access })
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

fn function(instructions: Vec<SpannedVirInstruction>) -> VirFunction {
    VirFunction {
        id: VirFunctionId::new(0),
        name: "object_effect".to_owned(),
        signature: VirSignature {
            parameters: vec![],
            results: vec![],
        },
        contract: VirContractId::new(0),
        entry: VirBlockId::new(0),
        blocks: vec![VirBasicBlock {
            id: VirBlockId::new(0),
            parameters: vec![],
            instructions,
            terminator: SpannedVirTerminator {
                terminator: VirTerminator::Return { values: vec![] },
                source_span: span(),
            },
            source_span: span(),
        }],
        source_span: span(),
    }
}

fn unit(instructions: Vec<SpannedVirInstruction>) -> VirUnit {
    VirUnit::from_runtime(
        address_program::schema(),
        VirFunctionId::new(0),
        vec![function(instructions)],
    )
}

fn storage(pointer_id: u32, permission_id: u32, access: VirMemoryAccess) -> SpannedVirInstruction {
    instruction(VirInstruction::LocalStorage {
        pointer_result: pointer(pointer_id, access),
        permission_result: permission(permission_id),
        access,
    })
}

fn transfer(
    destination_mode: VirObjectDestinationMode,
    source_mode: VirObjectSourceMode,
) -> VirInstruction {
    VirInstruction::ObjectTransfer {
        destination: VirValueId::new(0),
        destination_permission: VirValueId::new(1),
        source: VirValueId::new(2),
        source_permission: VirValueId::new(3),
        access: address_program::RECORD_ACCESS,
        destination_mode,
        source_mode,
    }
}

fn transfer_unit(effect: VirInstruction) -> VirUnit {
    unit(vec![
        storage(0, 1, address_program::RECORD_ACCESS),
        storage(2, 3, address_program::RECORD_ACCESS),
        instruction(effect),
    ])
}

#[test]
fn every_object_transfer_mode_has_stable_syntax_and_verifier_transfer() {
    let modes = [
        (
            VirObjectDestinationMode::Initialize,
            VirObjectSourceMode::Copy,
            "object.init.copy",
        ),
        (
            VirObjectDestinationMode::Replace,
            VirObjectSourceMode::Copy,
            "object.replace.copy",
        ),
        (
            VirObjectDestinationMode::Initialize,
            VirObjectSourceMode::Move,
            "object.init.move",
        ),
        (
            VirObjectDestinationMode::Replace,
            VirObjectSourceMode::Move,
            "object.replace.move",
        ),
    ];

    for (destination_mode, source_mode, syntax) in modes {
        let unit = transfer_unit(transfer(destination_mode, source_mode));
        assert!(unit.stable_dump().contains(syntax));
        unit.validate().expect("object effect schema validates");
        let transfer = transfer_instruction_with_memory(
            &ResourceState::new(),
            &unit.runtime.functions[0].blocks[0].instructions[2],
            &unit.memory,
        )
        .expect("object effect has verifier transfer semantics");
        assert!(
            transfer.obligations().iter().any(|obligation| {
                matches!(
                    obligation.kind(),
                    ResourceObligationKind::ObjectNonOverlapping { .. }
                ) && obligation.status() == ObligationStatus::Unknown
            }),
            "unknown input pointers must leave non-overlap unresolved"
        );
        assert!(
            unit.source_map
                .origin_at(VirLocation::Instruction {
                    function: VirFunctionId::new(0),
                    block: VirBlockId::new(0),
                    ordinal: 2,
                })
                .is_some(),
            "object effect must retain a source-map location"
        );
    }
}

#[test]
fn runtime_consumers_accept_object_effects_and_interpreter_checks_initialization() {
    let validated = transfer_unit(transfer(
        VirObjectDestinationMode::Initialize,
        VirObjectSourceMode::Copy,
    ))
    .into_validated()
    .expect("object effect is structurally valid");
    let resolved = validated.resolve().expect("object-effect unit resolves");
    assert_eq!(
        interpret(resolved.runtime())
            .expect_err("partial object source must fault dynamically")
            .kind(),
        &VirExecutionErrorKind::UninitializedObjectLeaf {
            allocation: 1,
            offset_bytes: 8,
            access: address_program::RECORD_ACCESS,
        }
    );
    let plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("native object lowering accepts verifier-supported shapes");
    assert!(matches!(
        plan.function(VirFunctionId::new(0)).unwrap().blocks()[0].instructions()[2],
        X86_64InstructionPlan::ObjectTransfer(_)
    ));
}

#[test]
fn deinitialize_is_typed_dumped_and_validated() {
    let unit = unit(vec![
        storage(0, 1, address_program::RECORD_ACCESS),
        instruction(VirInstruction::ObjectDeinitialize {
            pointer: VirValueId::new(0),
            permission: VirValueId::new(1),
            access: address_program::RECORD_ACCESS,
        }),
    ]);
    assert!(
        unit.stable_dump()
            .contains("object.deinit %0 using %1 access type2/layout2")
    );
    unit.validate().expect("deinitialize schema validates");
}

#[test]
fn object_effect_validation_rejects_alias_shape_and_nominal_mismatches() {
    let mut aliases = transfer(
        VirObjectDestinationMode::Initialize,
        VirObjectSourceMode::Move,
    );
    let VirInstruction::ObjectTransfer { source, .. } = &mut aliases else {
        unreachable!()
    };
    *source = VirValueId::new(0);
    assert_eq!(
        transfer_unit(aliases)
            .validate()
            .expect_err("exact self-move is invalid")
            .kind(),
        &VirValidationErrorKind::ObjectEffectAliases
    );

    let mut wrong_nominal = transfer_unit(transfer(
        VirObjectDestinationMode::Initialize,
        VirObjectSourceMode::Copy,
    ));
    let VirInstruction::LocalStorage {
        pointer_result,
        access,
        ..
    } = &mut wrong_nominal.runtime.functions[0].blocks[0].instructions[1].instruction
    else {
        unreachable!()
    };
    pointer_result.ty = VirType::Pointer {
        access: address_program::U64_ACCESS,
    };
    *access = address_program::U64_ACCESS;
    assert!(matches!(
        wrong_nominal
            .validate()
            .expect_err("source and effect nominal access differ")
            .kind(),
        VirValidationErrorKind::TypeMismatch {
            context: "object transfer source",
            ..
        }
    ));

    let mut invalid_shape = transfer(VirObjectDestinationMode::Replace, VirObjectSourceMode::Copy);
    let VirInstruction::ObjectTransfer { access, .. } = &mut invalid_shape else {
        unreachable!()
    };
    *access = VirMemoryAccess::new(VirTypeId::new(0), VirLayoutId::new(1));
    assert!(matches!(
        transfer_unit(invalid_shape)
            .validate()
            .expect_err("effect shape must resolve canonically")
            .kind(),
        VirValidationErrorKind::InvalidObjectEffectShape(
            VirObjectShapeErrorKind::InvalidAccess { .. }
        )
    ));
}

fn enum_unit(variant: VirVariantId, mode: VirObjectDestinationMode) -> VirUnit {
    enum_unit_with_read(variant, mode, None)
}

fn enum_unit_with_read(
    variant: VirVariantId,
    mode: VirObjectDestinationMode,
    result_type: Option<VirType>,
) -> VirUnit {
    let mut schema = address_program::schema();
    schema.types.push(VirMemoryType {
        id: ENUM_ACCESS.ty,
        kind: VirMemoryTypeKind::Enum {
            variants: vec![VirVariantId::new(0), VirVariantId::new(1)],
        },
        layout: ENUM_ACCESS.layout,
    });
    schema.layouts.push(VirLayout {
        id: ENUM_ACCESS.layout,
        ty: ENUM_ACCESS.ty,
        size_bytes: 8,
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
                    fields: vec![],
                },
                VirVariantCaseLayout {
                    variant: VirVariantId::new(1),
                    payload_offset_bytes: 8,
                    fields: vec![],
                },
            ],
        }),
    });
    schema.variants.extend([
        VirVariant {
            id: VirVariantId::new(0),
            owner: ENUM_ACCESS.ty,
            fields: vec![],
            discriminant: 0,
        },
        VirVariant {
            id: VirVariantId::new(1),
            owner: ENUM_ACCESS.ty,
            fields: vec![],
            discriminant: 1,
        },
    ]);
    schema
        .assign_canonical_type_capabilities()
        .expect("enum capabilities");
    let mut instructions = vec![
        storage(0, 1, ENUM_ACCESS),
        instruction(VirInstruction::EnumSetDiscriminant {
            pointer: VirValueId::new(0),
            permission: VirValueId::new(1),
            access: ENUM_ACCESS,
            variant,
            mode,
        }),
    ];
    if let Some(result_type) = result_type {
        instructions.push(instruction(VirInstruction::EnumDiscriminant {
            result: value(2, result_type),
            pointer: VirValueId::new(0),
            permission: VirValueId::new(1),
            access: ENUM_ACCESS,
        }));
    }
    VirUnit::from_runtime(schema, VirFunctionId::new(0), vec![function(instructions)])
}

#[test]
fn enum_discriminant_effect_uses_the_canonical_enum_variant() {
    for (mode, syntax) in [
        (
            VirObjectDestinationMode::Initialize,
            "enum.init-discriminant",
        ),
        (
            VirObjectDestinationMode::Replace,
            "enum.replace-discriminant",
        ),
    ] {
        let unit = enum_unit(VirVariantId::new(1), mode);
        assert!(unit.stable_dump().contains(syntax));
        unit.validate().expect("enum effect schema validates");
    }

    let invalid = enum_unit(VirVariantId::new(9), VirObjectDestinationMode::Initialize);
    assert_eq!(
        invalid
            .validate()
            .expect_err("foreign enum variant is rejected")
            .kind(),
        &VirValidationErrorKind::InvalidEnumObjectEffect(VirVariantId::new(9))
    );
}

#[test]
fn enum_discriminant_read_is_typed_and_rejects_a_forged_result() {
    let unit = enum_unit_with_read(
        VirVariantId::new(1),
        VirObjectDestinationMode::Initialize,
        Some(VirType::U64),
    );
    assert!(unit.stable_dump().contains("enum.discriminant"));
    let validated = unit
        .into_validated()
        .expect("canonical enum discriminant read validates");
    interpret(
        validated
            .resolve()
            .expect("enum read fixture resolves")
            .runtime(),
    )
    .expect("initialized valid enum tag reads successfully");

    let forged = enum_unit_with_read(
        VirVariantId::new(1),
        VirObjectDestinationMode::Initialize,
        Some(VirType::Bool),
    );
    assert!(matches!(
        forged
            .validate()
            .expect_err("enum tag read result must be u64")
            .kind(),
        VirValidationErrorKind::TypeMismatch {
            context: "enum discriminant result",
            expected: VirType::U64,
            found: VirType::Bool,
        }
    ));
}

#[test]
fn pointer_containing_objects_remain_fail_closed_at_runtime_consumers() {
    let pointer_access = VirMemoryAccess::new(VirTypeId::new(3), VirLayoutId::new(3));
    let object_access = VirMemoryAccess::new(VirTypeId::new(4), VirLayoutId::new(4));
    let mut schema = address_program::schema();
    schema.types.extend([
        VirMemoryType {
            id: pointer_access.ty,
            kind: VirMemoryTypeKind::Pointer {
                pointee: address_program::U64_ACCESS.ty,
                kind: VirPointerKind::Raw,
                mutability: VirMutability::Const,
            },
            layout: pointer_access.layout,
        },
        VirMemoryType {
            id: object_access.ty,
            kind: VirMemoryTypeKind::Struct {
                fields: vec![nera::VirFieldId::new(1)],
            },
            layout: object_access.layout,
        },
    ]);
    schema.layouts.extend([
        VirLayout {
            id: pointer_access.layout,
            ty: pointer_access.ty,
            size_bytes: 8,
            alignment: 8,
            abi: VirAbiClass::Scalar,
            fields: vec![],
            variants: None,
        },
        VirLayout {
            id: object_access.layout,
            ty: object_access.ty,
            size_bytes: 8,
            alignment: 8,
            abi: VirAbiClass::Aggregate,
            fields: vec![nera::VirFieldLayout {
                field: nera::VirFieldId::new(1),
                offset_bytes: 0,
            }],
            variants: None,
        },
    ]);
    schema.fields.push(nera::VirField {
        id: nera::VirFieldId::new(1),
        owner: object_access.ty,
        ty: pointer_access.ty,
    });
    schema
        .assign_canonical_type_capabilities()
        .expect("pointer aggregate capabilities");
    let unit = VirUnit::from_runtime(
        schema,
        VirFunctionId::new(0),
        vec![function(vec![
            storage(0, 1, object_access),
            instruction(VirInstruction::ObjectDeinitialize {
                pointer: VirValueId::new(0),
                permission: VirValueId::new(1),
                access: object_access,
            }),
        ])],
    )
    .into_validated()
    .expect("pointer object effect remains structurally explicit");
    let resolved = unit.resolve().expect("pointer object fixture resolves");
    assert_eq!(
        interpret(resolved.runtime())
            .expect_err("interpreter has no pointer byte representation")
            .kind(),
        &VirExecutionErrorKind::UnsupportedObjectEffectType {
            access: object_access,
        }
    );
    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU
            .plan_program(resolved.runtime())
            .expect_err("native pointer object effects remain gated")
            .kind(),
        &X86_64PlanningErrorKind::UnsupportedObjectEffectType {
            access: object_access,
        }
    );
}

#[test]
fn native_inline_object_transfer_budget_fails_closed() {
    let mut unit = transfer_unit(transfer(
        VirObjectDestinationMode::Initialize,
        VirObjectSourceMode::Copy,
    ));
    let VirMemoryTypeKind::Array { length, .. } = &mut unit.memory.types[1].kind else {
        panic!("address fixture array type")
    };
    *length = 513;
    unit.memory.layouts[1].size_bytes = 4104;
    unit.memory.layouts[2].size_bytes = 4112;
    let validated = unit
        .into_validated()
        .expect("large fixed aggregate remains structurally valid");
    let resolved = validated.resolve().expect("large object fixture resolves");
    assert_eq!(
        interpret(resolved.runtime())
            .expect_err("interpreter object traversal must also remain bounded")
            .kind(),
        &VirExecutionErrorKind::ObjectEffectSizeLimitExceeded {
            requested: 4112,
            limit: 4096,
        }
    );
    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU
            .plan_program(resolved.runtime())
            .expect_err("large transfer must not expand unbounded native code")
            .kind(),
        &X86_64PlanningErrorKind::ObjectEffectSizeExceeded {
            requested: 4112,
            maximum: nera::backend::X86_64_INLINE_OBJECT_COPY_MAX_BYTES,
        }
    );
}
