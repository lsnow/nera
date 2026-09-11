#![allow(dead_code)]

use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, ValidatedVirUnit, VirAbiClass,
    VirBasicBlock, VirBlockId, VirBlockTarget, VirConstant, VirContractId, VirEndianness, VirField,
    VirFieldId, VirFieldLayout, VirFunction, VirFunctionId, VirInstruction, VirIntegerType,
    VirLayout, VirLayoutId, VirMemoryAccess, VirMemorySchema, VirMemoryType, VirMemoryTypeKind,
    VirObjectDestinationMode, VirObjectSourceMode, VirRegionId, VirSignature, VirTargetDataLayout,
    VirTerminator, VirType, VirTypeId, VirUnit, VirValue, VirValueId, VirVariant,
    VirVariantCaseLayout, VirVariantId, VirVariantLayout,
};

pub const U64_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(0), VirLayoutId::new(0));
pub const RECORD_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(1), VirLayoutId::new(1));
pub const ENUM_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(0), VirLayoutId::new(0));

fn span() -> ByteSpan {
    ByteSpan::new(0, 1).expect("ordered span")
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

fn record_schema() -> VirMemorySchema {
    let mut schema = VirMemorySchema {
        target: target_layout(),
        types: vec![
            VirMemoryType {
                id: U64_ACCESS.ty,
                kind: VirMemoryTypeKind::Integer(VirIntegerType::U64),
                layout: U64_ACCESS.layout,
            },
            VirMemoryType {
                id: RECORD_ACCESS.ty,
                kind: VirMemoryTypeKind::Struct {
                    fields: vec![VirFieldId::new(0), VirFieldId::new(1)],
                },
                layout: RECORD_ACCESS.layout,
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
                id: RECORD_ACCESS.layout,
                ty: RECORD_ACCESS.ty,
                size_bytes: 16,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![
                    VirFieldLayout {
                        field: VirFieldId::new(0),
                        offset_bytes: 0,
                    },
                    VirFieldLayout {
                        field: VirFieldId::new(1),
                        offset_bytes: 8,
                    },
                ],
                variants: None,
            },
        ],
        fields: vec![
            VirField {
                id: VirFieldId::new(0),
                owner: RECORD_ACCESS.ty,
                ty: U64_ACCESS.ty,
            },
            VirField {
                id: VirFieldId::new(1),
                owner: RECORD_ACCESS.ty,
                ty: U64_ACCESS.ty,
            },
        ],
        variants: vec![],
    };
    schema
        .assign_canonical_type_capabilities()
        .expect("record schema capabilities");
    schema
}

pub fn record_unit(source_mode: VirObjectSourceMode, complete_source: bool) -> VirUnit {
    record_unit_with_modes(
        VirObjectDestinationMode::Initialize,
        source_mode,
        complete_source,
    )
}

pub fn record_unit_with_modes(
    destination_mode: VirObjectDestinationMode,
    source_mode: VirObjectSourceMode,
    complete_source: bool,
) -> VirUnit {
    let mut entry_instructions = vec![
        instruction(VirInstruction::LocalStorage {
            pointer_result: pointer(0, RECORD_ACCESS),
            permission_result: permission(1),
            access: RECORD_ACCESS,
        }),
        instruction(VirInstruction::LocalStorage {
            pointer_result: pointer(2, RECORD_ACCESS),
            permission_result: permission(3),
            access: RECORD_ACCESS,
        }),
        instruction(VirInstruction::FieldAddress {
            result: pointer(4, U64_ACCESS),
            base: VirValueId::new(0),
            field: VirFieldId::new(0),
            owner: RECORD_ACCESS,
            field_access: U64_ACCESS,
            offset_bytes: 0,
        }),
        instruction(VirInstruction::Constant {
            result: word(5),
            value: VirConstant::U64(17),
        }),
        instruction(VirInstruction::Initialize {
            pointer: VirValueId::new(4),
            value: VirValueId::new(5),
            permission: VirValueId::new(1),
            access: U64_ACCESS,
        }),
        instruction(VirInstruction::FieldAddress {
            result: pointer(6, U64_ACCESS),
            base: VirValueId::new(0),
            field: VirFieldId::new(1),
            owner: RECORD_ACCESS,
            field_access: U64_ACCESS,
            offset_bytes: 8,
        }),
        instruction(VirInstruction::Constant {
            result: word(7),
            value: VirConstant::U64(42),
        }),
    ];
    if complete_source {
        entry_instructions.push(instruction(VirInstruction::Initialize {
            pointer: VirValueId::new(6),
            value: VirValueId::new(7),
            permission: VirValueId::new(1),
            access: U64_ACCESS,
        }));
    }
    if matches!(destination_mode, VirObjectDestinationMode::Replace) {
        entry_instructions.extend([
            instruction(VirInstruction::FieldAddress {
                result: pointer(8, U64_ACCESS),
                base: VirValueId::new(2),
                field: VirFieldId::new(0),
                owner: RECORD_ACCESS,
                field_access: U64_ACCESS,
                offset_bytes: 0,
            }),
            instruction(VirInstruction::Initialize {
                pointer: VirValueId::new(8),
                value: VirValueId::new(5),
                permission: VirValueId::new(3),
                access: U64_ACCESS,
            }),
            instruction(VirInstruction::FieldAddress {
                result: pointer(9, U64_ACCESS),
                base: VirValueId::new(2),
                field: VirFieldId::new(1),
                owner: RECORD_ACCESS,
                field_access: U64_ACCESS,
                offset_bytes: 8,
            }),
            instruction(VirInstruction::Initialize {
                pointer: VirValueId::new(9),
                value: VirValueId::new(7),
                permission: VirValueId::new(3),
                access: U64_ACCESS,
            }),
        ]);
    }
    entry_instructions.extend([
        instruction(VirInstruction::ObjectTransfer {
            destination: VirValueId::new(2),
            destination_permission: VirValueId::new(3),
            source: VirValueId::new(0),
            source_permission: VirValueId::new(1),
            access: RECORD_ACCESS,
            destination_mode,
            source_mode,
        }),
        instruction(VirInstruction::Constant {
            result: boolean(15),
            value: VirConstant::Bool(true),
        }),
    ]);
    if matches!(source_mode, VirObjectSourceMode::Copy) {
        entry_instructions.insert(
            entry_instructions.len() - 1,
            instruction(VirInstruction::ObjectDeinitialize {
                pointer: VirValueId::new(0),
                permission: VirValueId::new(1),
                access: RECORD_ACCESS,
            }),
        );
    }

    VirUnit::from_runtime(
        record_schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "object_effect_record".to_owned(),
            signature: VirSignature {
                parameters: vec![],
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![
                block(
                    0,
                    vec![],
                    entry_instructions,
                    VirTerminator::Branch {
                        condition: VirValueId::new(15),
                        then_target: target(1, &[2, 3]),
                        else_target: target(2, &[2, 3]),
                    },
                ),
                block(
                    1,
                    vec![pointer(20, RECORD_ACCESS), permission(21)],
                    vec![],
                    VirTerminator::Jump {
                        target: target(3, &[20, 21]),
                    },
                ),
                block(
                    2,
                    vec![pointer(30, RECORD_ACCESS), permission(31)],
                    vec![],
                    VirTerminator::Jump {
                        target: target(3, &[30, 31]),
                    },
                ),
                block(
                    3,
                    vec![pointer(40, RECORD_ACCESS), permission(41)],
                    vec![
                        instruction(VirInstruction::FieldAddress {
                            result: pointer(42, U64_ACCESS),
                            base: VirValueId::new(40),
                            field: VirFieldId::new(1),
                            owner: RECORD_ACCESS,
                            field_access: U64_ACCESS,
                            offset_bytes: 8,
                        }),
                        instruction(VirInstruction::Load {
                            result: word(43),
                            pointer: VirValueId::new(42),
                            permission: VirValueId::new(41),
                            access: U64_ACCESS,
                        }),
                    ],
                    VirTerminator::Return {
                        values: vec![VirValueId::new(43)],
                    },
                ),
            ],
            source_span: span(),
        }],
    )
}

pub fn validated_record(source_mode: VirObjectSourceMode) -> ValidatedVirUnit {
    record_unit(source_mode, true)
        .into_validated()
        .expect("record object-effect fixture validates")
}

pub fn validated_record_modes(
    destination_mode: VirObjectDestinationMode,
    source_mode: VirObjectSourceMode,
) -> ValidatedVirUnit {
    record_unit_with_modes(destination_mode, source_mode, true)
        .into_validated()
        .expect("record object-effect mode fixture validates")
}

pub fn overlapping_record_unit() -> VirUnit {
    VirUnit::from_runtime(
        record_schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "overlapping_object_effect".to_owned(),
            signature: VirSignature {
                parameters: vec![],
                results: vec![],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![block(
                0,
                vec![],
                vec![
                    instruction(VirInstruction::Constant {
                        result: word(0),
                        value: VirConstant::U64(24),
                    }),
                    instruction(VirInstruction::Allocate {
                        pointer_result: pointer(1, RECORD_ACCESS),
                        permission_result: permission(2),
                        size_bytes: VirValueId::new(0),
                        alignment: 8,
                        region: VirRegionId::new(0),
                        element: RECORD_ACCESS,
                    }),
                    instruction(VirInstruction::FieldAddress {
                        result: pointer(3, U64_ACCESS),
                        base: VirValueId::new(1),
                        field: VirFieldId::new(0),
                        owner: RECORD_ACCESS,
                        field_access: U64_ACCESS,
                        offset_bytes: 0,
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(4),
                        value: VirConstant::U64(17),
                    }),
                    instruction(VirInstruction::Initialize {
                        pointer: VirValueId::new(3),
                        value: VirValueId::new(4),
                        permission: VirValueId::new(2),
                        access: U64_ACCESS,
                    }),
                    instruction(VirInstruction::FieldAddress {
                        result: pointer(5, U64_ACCESS),
                        base: VirValueId::new(1),
                        field: VirFieldId::new(1),
                        owner: RECORD_ACCESS,
                        field_access: U64_ACCESS,
                        offset_bytes: 8,
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(6),
                        value: VirConstant::U64(42),
                    }),
                    instruction(VirInstruction::Initialize {
                        pointer: VirValueId::new(5),
                        value: VirValueId::new(6),
                        permission: VirValueId::new(2),
                        access: U64_ACCESS,
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(7),
                        value: VirConstant::U64(8),
                    }),
                    instruction(VirInstruction::PointerOffset {
                        result: pointer(8, RECORD_ACCESS),
                        base: VirValueId::new(1),
                        delta_bytes: VirValueId::new(7),
                    }),
                    instruction(VirInstruction::ObjectTransfer {
                        destination: VirValueId::new(8),
                        destination_permission: VirValueId::new(2),
                        source: VirValueId::new(1),
                        source_permission: VirValueId::new(2),
                        access: RECORD_ACCESS,
                        destination_mode: VirObjectDestinationMode::Initialize,
                        source_mode: VirObjectSourceMode::Copy,
                    }),
                ],
                VirTerminator::Return { values: vec![] },
            )],
            source_span: span(),
        }],
    )
}

pub fn enum_unit(source_mode: VirObjectSourceMode) -> VirUnit {
    let mut schema = VirMemorySchema {
        target: target_layout(),
        types: vec![VirMemoryType {
            id: ENUM_ACCESS.ty,
            kind: VirMemoryTypeKind::Enum {
                variants: vec![VirVariantId::new(0), VirVariantId::new(1)],
            },
            layout: ENUM_ACCESS.layout,
        }],
        type_capabilities: vec![],
        layouts: vec![VirLayout {
            id: ENUM_ACCESS.layout,
            ty: ENUM_ACCESS.ty,
            size_bytes: 1,
            alignment: 1,
            abi: VirAbiClass::Aggregate,
            fields: vec![],
            variants: Some(VirVariantLayout {
                tag_size_bytes: 1,
                tag_alignment: 1,
                cases: vec![
                    VirVariantCaseLayout {
                        variant: VirVariantId::new(0),
                        payload_offset_bytes: 1,
                        fields: vec![],
                    },
                    VirVariantCaseLayout {
                        variant: VirVariantId::new(1),
                        payload_offset_bytes: 1,
                        fields: vec![],
                    },
                ],
            }),
        }],
        fields: vec![],
        variants: vec![
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
        ],
    };
    schema
        .assign_canonical_type_capabilities()
        .expect("enum schema capabilities");
    let mut instructions = vec![
        instruction(VirInstruction::LocalStorage {
            pointer_result: pointer(0, ENUM_ACCESS),
            permission_result: permission(1),
            access: ENUM_ACCESS,
        }),
        instruction(VirInstruction::LocalStorage {
            pointer_result: pointer(2, ENUM_ACCESS),
            permission_result: permission(3),
            access: ENUM_ACCESS,
        }),
        instruction(VirInstruction::EnumSetDiscriminant {
            pointer: VirValueId::new(0),
            permission: VirValueId::new(1),
            access: ENUM_ACCESS,
            variant: VirVariantId::new(1),
            mode: VirObjectDestinationMode::Initialize,
        }),
        instruction(VirInstruction::ObjectTransfer {
            destination: VirValueId::new(2),
            destination_permission: VirValueId::new(3),
            source: VirValueId::new(0),
            source_permission: VirValueId::new(1),
            access: ENUM_ACCESS,
            destination_mode: VirObjectDestinationMode::Initialize,
            source_mode,
        }),
    ];
    if matches!(source_mode, VirObjectSourceMode::Copy) {
        instructions.push(instruction(VirInstruction::ObjectDeinitialize {
            pointer: VirValueId::new(0),
            permission: VirValueId::new(1),
            access: ENUM_ACCESS,
        }));
    }
    instructions.push(instruction(VirInstruction::EnumDiscriminant {
        result: word(4),
        pointer: VirValueId::new(2),
        permission: VirValueId::new(3),
        access: ENUM_ACCESS,
    }));

    VirUnit::from_runtime(
        schema,
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "object_effect_enum".to_owned(),
            signature: VirSignature {
                parameters: vec![],
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![block(
                0,
                vec![],
                instructions,
                VirTerminator::Return {
                    values: vec![VirValueId::new(4)],
                },
            )],
            source_span: span(),
        }],
    )
}

pub fn validated_enum(source_mode: VirObjectSourceMode) -> ValidatedVirUnit {
    enum_unit(source_mode)
        .into_validated()
        .expect("enum object-effect fixture validates")
}

fn target_layout() -> VirTargetDataLayout {
    VirTargetDataLayout {
        endianness: VirEndianness::Little,
        pointer_size_bytes: 8,
        pointer_alignment: 8,
        usize_size_bytes: 8,
        usize_alignment: 8,
    }
}
