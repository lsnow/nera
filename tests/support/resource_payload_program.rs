#![allow(dead_code)]

use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, ValidatedVirUnit, VirAbiClass,
    VirBasicBlock, VirBlockId, VirBlockTarget, VirConstant, VirContractId, VirEndianness, VirField,
    VirFieldId, VirFieldLayout, VirFunction, VirFunctionId, VirInstruction, VirIntegerType,
    VirLayout, VirLayoutId, VirMemoryAccess, VirMemorySchema, VirMemoryType, VirMemoryTypeKind,
    VirMutability, VirObjectDestinationMode, VirObjectSourceMode, VirPointerKind, VirRegionId,
    VirSignature, VirTargetDataLayout, VirTerminator, VirType, VirTypeId, VirUnit, VirValue,
    VirValueId,
};

pub const U64_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(0), VirLayoutId::new(0));
pub const OWN_U64_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(1), VirLayoutId::new(1));
pub const OWNER_BOX_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(2), VirLayoutId::new(2));
pub const OWNER_PAIR_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(3), VirLayoutId::new(3));

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

fn target(block: u32, arguments: &[u32]) -> VirBlockTarget {
    VirBlockTarget {
        block: VirBlockId::new(block),
        arguments: arguments.iter().copied().map(VirValueId::new).collect(),
    }
}

fn terminator(terminator: VirTerminator) -> SpannedVirTerminator {
    SpannedVirTerminator {
        terminator,
        source_span: span(),
    }
}

pub fn schema() -> VirMemorySchema {
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
                id: OWN_U64_ACCESS.ty,
                kind: VirMemoryTypeKind::Pointer {
                    pointee: U64_ACCESS.ty,
                    kind: VirPointerKind::Own,
                    mutability: VirMutability::Mutable,
                },
                layout: OWN_U64_ACCESS.layout,
            },
            VirMemoryType {
                id: OWNER_BOX_ACCESS.ty,
                kind: VirMemoryTypeKind::Struct {
                    fields: vec![VirFieldId::new(0)],
                },
                layout: OWNER_BOX_ACCESS.layout,
            },
            VirMemoryType {
                id: OWNER_PAIR_ACCESS.ty,
                kind: VirMemoryTypeKind::Struct {
                    fields: vec![VirFieldId::new(1), VirFieldId::new(2)],
                },
                layout: OWNER_PAIR_ACCESS.layout,
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
                id: OWN_U64_ACCESS.layout,
                ty: OWN_U64_ACCESS.ty,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: vec![],
                variants: None,
            },
            VirLayout {
                id: OWNER_BOX_ACCESS.layout,
                ty: OWNER_BOX_ACCESS.ty,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![VirFieldLayout {
                    field: VirFieldId::new(0),
                    offset_bytes: 0,
                }],
                variants: None,
            },
            VirLayout {
                id: OWNER_PAIR_ACCESS.layout,
                ty: OWNER_PAIR_ACCESS.ty,
                size_bytes: 16,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![
                    VirFieldLayout {
                        field: VirFieldId::new(1),
                        offset_bytes: 0,
                    },
                    VirFieldLayout {
                        field: VirFieldId::new(2),
                        offset_bytes: 8,
                    },
                ],
                variants: None,
            },
        ],
        fields: vec![
            VirField {
                id: VirFieldId::new(0),
                owner: OWNER_BOX_ACCESS.ty,
                ty: OWN_U64_ACCESS.ty,
            },
            VirField {
                id: VirFieldId::new(1),
                owner: OWNER_PAIR_ACCESS.ty,
                ty: OWN_U64_ACCESS.ty,
            },
            VirField {
                id: VirFieldId::new(2),
                owner: OWNER_PAIR_ACCESS.ty,
                ty: OWN_U64_ACCESS.ty,
            },
        ],
        variants: vec![],
    };
    schema
        .assign_canonical_type_capabilities()
        .expect("resource schema capabilities");
    schema
}

pub fn unit() -> VirUnit {
    let instructions = vec![
        instruction(VirInstruction::LocalStorage {
            pointer_result: pointer(0, OWNER_BOX_ACCESS),
            permission_result: permission(1),
            access: OWNER_BOX_ACCESS,
        }),
        instruction(VirInstruction::LocalStorage {
            pointer_result: pointer(2, OWNER_BOX_ACCESS),
            permission_result: permission(3),
            access: OWNER_BOX_ACCESS,
        }),
        instruction(VirInstruction::Constant {
            result: value(4, VirType::U64),
            value: VirConstant::U64(8),
        }),
        instruction(VirInstruction::Allocate {
            pointer_result: pointer(5, U64_ACCESS),
            permission_result: permission(6),
            size_bytes: VirValueId::new(4),
            alignment: 8,
            region: VirRegionId::new(0),
            element: U64_ACCESS,
        }),
        instruction(VirInstruction::FieldAddress {
            result: pointer(7, OWN_U64_ACCESS),
            base: VirValueId::new(0),
            field: VirFieldId::new(0),
            owner: OWNER_BOX_ACCESS,
            field_access: OWN_U64_ACCESS,
            offset_bytes: 0,
        }),
        instruction(VirInstruction::ResourceInitialize {
            destination: VirValueId::new(7),
            destination_permission: VirValueId::new(1),
            value: VirValueId::new(5),
            value_permission: VirValueId::new(6),
            access: OWN_U64_ACCESS,
        }),
        instruction(VirInstruction::ObjectTransfer {
            destination: VirValueId::new(2),
            destination_permission: VirValueId::new(3),
            source: VirValueId::new(0),
            source_permission: VirValueId::new(1),
            access: OWNER_BOX_ACCESS,
            destination_mode: VirObjectDestinationMode::Initialize,
            source_mode: VirObjectSourceMode::Move,
        }),
        instruction(VirInstruction::FieldAddress {
            result: pointer(8, OWN_U64_ACCESS),
            base: VirValueId::new(2),
            field: VirFieldId::new(0),
            owner: OWNER_BOX_ACCESS,
            field_access: OWN_U64_ACCESS,
            offset_bytes: 0,
        }),
        instruction(VirInstruction::ResourceTake {
            pointer_result: pointer(9, U64_ACCESS),
            permission_result: permission(10),
            source: VirValueId::new(8),
            source_permission: VirValueId::new(3),
            access: OWN_U64_ACCESS,
        }),
        instruction(VirInstruction::Free {
            pointer: VirValueId::new(9),
            permission: VirValueId::new(10),
        }),
        instruction(VirInstruction::Constant {
            result: value(11, VirType::U64),
            value: VirConstant::U64(0),
        }),
    ];
    VirUnit::from_runtime(
        schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "resource_payload".to_owned(),
            signature: VirSignature {
                parameters: vec![],
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: vec![],
                instructions,
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return {
                        values: vec![VirValueId::new(11)],
                    },
                    source_span: span(),
                },
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

pub fn validated() -> ValidatedVirUnit {
    unit()
        .into_validated()
        .expect("resource payload VIR validates")
}

pub fn partial_pair_unit(consume_sibling: bool) -> VirUnit {
    let mut instructions = vec![
        instruction(VirInstruction::LocalStorage {
            pointer_result: pointer(0, OWNER_PAIR_ACCESS),
            permission_result: permission(1),
            access: OWNER_PAIR_ACCESS,
        }),
        instruction(VirInstruction::LocalStorage {
            pointer_result: pointer(2, OWNER_PAIR_ACCESS),
            permission_result: permission(3),
            access: OWNER_PAIR_ACCESS,
        }),
        instruction(VirInstruction::Constant {
            result: value(4, VirType::U64),
            value: VirConstant::U64(8),
        }),
        instruction(VirInstruction::Allocate {
            pointer_result: pointer(5, U64_ACCESS),
            permission_result: permission(6),
            size_bytes: VirValueId::new(4),
            alignment: 8,
            region: VirRegionId::new(0),
            element: U64_ACCESS,
        }),
        instruction(VirInstruction::Allocate {
            pointer_result: pointer(7, U64_ACCESS),
            permission_result: permission(8),
            size_bytes: VirValueId::new(4),
            alignment: 8,
            region: VirRegionId::new(0),
            element: U64_ACCESS,
        }),
        instruction(VirInstruction::FieldAddress {
            result: pointer(9, OWN_U64_ACCESS),
            base: VirValueId::new(0),
            field: VirFieldId::new(1),
            owner: OWNER_PAIR_ACCESS,
            field_access: OWN_U64_ACCESS,
            offset_bytes: 0,
        }),
        instruction(VirInstruction::FieldAddress {
            result: pointer(10, OWN_U64_ACCESS),
            base: VirValueId::new(0),
            field: VirFieldId::new(2),
            owner: OWNER_PAIR_ACCESS,
            field_access: OWN_U64_ACCESS,
            offset_bytes: 8,
        }),
        instruction(VirInstruction::ResourceInitialize {
            destination: VirValueId::new(9),
            destination_permission: VirValueId::new(1),
            value: VirValueId::new(5),
            value_permission: VirValueId::new(6),
            access: OWN_U64_ACCESS,
        }),
        instruction(VirInstruction::ResourceInitialize {
            destination: VirValueId::new(10),
            destination_permission: VirValueId::new(1),
            value: VirValueId::new(7),
            value_permission: VirValueId::new(8),
            access: OWN_U64_ACCESS,
        }),
        instruction(VirInstruction::ResourceTake {
            pointer_result: pointer(11, U64_ACCESS),
            permission_result: permission(12),
            source: VirValueId::new(9),
            source_permission: VirValueId::new(1),
            access: OWN_U64_ACCESS,
        }),
        instruction(VirInstruction::Free {
            pointer: VirValueId::new(11),
            permission: VirValueId::new(12),
        }),
    ];
    if consume_sibling {
        instructions.extend([
            instruction(VirInstruction::ResourceTake {
                pointer_result: pointer(13, U64_ACCESS),
                permission_result: permission(14),
                source: VirValueId::new(10),
                source_permission: VirValueId::new(1),
                access: OWN_U64_ACCESS,
            }),
            instruction(VirInstruction::Free {
                pointer: VirValueId::new(13),
                permission: VirValueId::new(14),
            }),
        ]);
    } else {
        instructions.push(instruction(VirInstruction::ObjectTransfer {
            destination: VirValueId::new(2),
            destination_permission: VirValueId::new(3),
            source: VirValueId::new(0),
            source_permission: VirValueId::new(1),
            access: OWNER_PAIR_ACCESS,
            destination_mode: VirObjectDestinationMode::Initialize,
            source_mode: VirObjectSourceMode::Move,
        }));
    }
    instructions.push(instruction(VirInstruction::Constant {
        result: value(15, VirType::U64),
        value: VirConstant::U64(0),
    }));
    VirUnit::from_runtime(
        schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "partial_pair".to_owned(),
            signature: VirSignature {
                parameters: vec![],
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: vec![],
                instructions,
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return {
                        values: vec![VirValueId::new(15)],
                    },
                    source_span: span(),
                },
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConditionalUse {
    MatchingGuard,
    Unconditional,
    UnrelatedGuard,
}

pub fn conditional_unit(conditional_use: ConditionalUse) -> VirUnit {
    let mut join_instructions = Vec::new();
    let join_terminator = match conditional_use {
        ConditionalUse::MatchingGuard | ConditionalUse::UnrelatedGuard => VirTerminator::Branch {
            condition: VirValueId::new(
                if matches!(conditional_use, ConditionalUse::MatchingGuard) {
                    32
                } else {
                    33
                },
            ),
            then_target: target(4, &[30, 31]),
            else_target: target(5, &[30, 31]),
        },
        ConditionalUse::Unconditional => {
            join_instructions.extend([
                instruction(VirInstruction::FieldAddress {
                    result: pointer(34, OWN_U64_ACCESS),
                    base: VirValueId::new(30),
                    field: VirFieldId::new(0),
                    owner: OWNER_BOX_ACCESS,
                    field_access: OWN_U64_ACCESS,
                    offset_bytes: 0,
                }),
                instruction(VirInstruction::ResourceTake {
                    pointer_result: pointer(35, U64_ACCESS),
                    permission_result: permission(36),
                    source: VirValueId::new(34),
                    source_permission: VirValueId::new(31),
                    access: OWN_U64_ACCESS,
                }),
                instruction(VirInstruction::Free {
                    pointer: VirValueId::new(35),
                    permission: VirValueId::new(36),
                }),
                instruction(VirInstruction::Constant {
                    result: value(37, VirType::U64),
                    value: VirConstant::U64(0),
                }),
            ]);
            VirTerminator::Return {
                values: vec![VirValueId::new(37)],
            }
        }
    };

    let blocks = vec![
        VirBasicBlock {
            id: VirBlockId::new(0),
            parameters: vec![value(0, VirType::Bool), value(1, VirType::Bool)],
            instructions: vec![
                instruction(VirInstruction::LocalStorage {
                    pointer_result: pointer(2, OWNER_BOX_ACCESS),
                    permission_result: permission(3),
                    access: OWNER_BOX_ACCESS,
                }),
                instruction(VirInstruction::Constant {
                    result: value(4, VirType::U64),
                    value: VirConstant::U64(8),
                }),
                instruction(VirInstruction::Allocate {
                    pointer_result: pointer(5, U64_ACCESS),
                    permission_result: permission(6),
                    size_bytes: VirValueId::new(4),
                    alignment: 8,
                    region: VirRegionId::new(0),
                    element: U64_ACCESS,
                }),
                instruction(VirInstruction::FieldAddress {
                    result: pointer(7, OWN_U64_ACCESS),
                    base: VirValueId::new(2),
                    field: VirFieldId::new(0),
                    owner: OWNER_BOX_ACCESS,
                    field_access: OWN_U64_ACCESS,
                    offset_bytes: 0,
                }),
                instruction(VirInstruction::ResourceInitialize {
                    destination: VirValueId::new(7),
                    destination_permission: VirValueId::new(3),
                    value: VirValueId::new(5),
                    value_permission: VirValueId::new(6),
                    access: OWN_U64_ACCESS,
                }),
            ],
            terminator: terminator(VirTerminator::Branch {
                condition: VirValueId::new(0),
                then_target: target(1, &[2, 3, 0, 1]),
                else_target: target(2, &[2, 3, 0, 1]),
            }),
            source_span: span(),
        },
        VirBasicBlock {
            id: VirBlockId::new(1),
            parameters: vec![
                pointer(10, OWNER_BOX_ACCESS),
                permission(11),
                value(12, VirType::Bool),
                value(13, VirType::Bool),
            ],
            instructions: vec![
                instruction(VirInstruction::FieldAddress {
                    result: pointer(14, OWN_U64_ACCESS),
                    base: VirValueId::new(10),
                    field: VirFieldId::new(0),
                    owner: OWNER_BOX_ACCESS,
                    field_access: OWN_U64_ACCESS,
                    offset_bytes: 0,
                }),
                instruction(VirInstruction::ResourceTake {
                    pointer_result: pointer(15, U64_ACCESS),
                    permission_result: permission(16),
                    source: VirValueId::new(14),
                    source_permission: VirValueId::new(11),
                    access: OWN_U64_ACCESS,
                }),
                instruction(VirInstruction::Free {
                    pointer: VirValueId::new(15),
                    permission: VirValueId::new(16),
                }),
            ],
            terminator: terminator(VirTerminator::Jump {
                target: target(3, &[10, 11, 12, 13]),
            }),
            source_span: span(),
        },
        VirBasicBlock {
            id: VirBlockId::new(2),
            parameters: vec![
                pointer(20, OWNER_BOX_ACCESS),
                permission(21),
                value(22, VirType::Bool),
                value(23, VirType::Bool),
            ],
            instructions: vec![],
            terminator: terminator(VirTerminator::Jump {
                target: target(3, &[20, 21, 22, 23]),
            }),
            source_span: span(),
        },
        VirBasicBlock {
            id: VirBlockId::new(3),
            parameters: vec![
                pointer(30, OWNER_BOX_ACCESS),
                permission(31),
                value(32, VirType::Bool),
                value(33, VirType::Bool),
            ],
            instructions: join_instructions,
            terminator: terminator(join_terminator),
            source_span: span(),
        },
        VirBasicBlock {
            id: VirBlockId::new(4),
            parameters: vec![pointer(40, OWNER_BOX_ACCESS), permission(41)],
            instructions: vec![instruction(VirInstruction::Constant {
                result: value(42, VirType::U64),
                value: VirConstant::U64(0),
            })],
            terminator: terminator(VirTerminator::Return {
                values: vec![VirValueId::new(42)],
            }),
            source_span: span(),
        },
        VirBasicBlock {
            id: VirBlockId::new(5),
            parameters: vec![pointer(50, OWNER_BOX_ACCESS), permission(51)],
            instructions: vec![
                instruction(VirInstruction::FieldAddress {
                    result: pointer(52, OWN_U64_ACCESS),
                    base: VirValueId::new(50),
                    field: VirFieldId::new(0),
                    owner: OWNER_BOX_ACCESS,
                    field_access: OWN_U64_ACCESS,
                    offset_bytes: 0,
                }),
                instruction(VirInstruction::ResourceTake {
                    pointer_result: pointer(53, U64_ACCESS),
                    permission_result: permission(54),
                    source: VirValueId::new(52),
                    source_permission: VirValueId::new(51),
                    access: OWN_U64_ACCESS,
                }),
                instruction(VirInstruction::Free {
                    pointer: VirValueId::new(53),
                    permission: VirValueId::new(54),
                }),
                instruction(VirInstruction::Constant {
                    result: value(55, VirType::U64),
                    value: VirConstant::U64(0),
                }),
            ],
            terminator: terminator(VirTerminator::Return {
                values: vec![VirValueId::new(55)],
            }),
            source_span: span(),
        },
    ];

    VirUnit::from_runtime(
        schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "conditional_resource_payload".to_owned(),
            signature: VirSignature {
                parameters: vec![VirType::Bool, VirType::Bool],
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks,
            source_span: span(),
        }],
    )
}

pub fn scalar_refinement_unit() -> VirUnit {
    VirUnit::from_runtime(
        schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "scalar_guard_refinement".to_owned(),
            signature: VirSignature {
                parameters: vec![VirType::Bool],
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![
                VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![value(0, VirType::Bool)],
                    instructions: vec![],
                    terminator: terminator(VirTerminator::Branch {
                        condition: VirValueId::new(0),
                        then_target: target(1, &[0]),
                        else_target: target(2, &[0]),
                    }),
                    source_span: span(),
                },
                VirBasicBlock {
                    id: VirBlockId::new(1),
                    parameters: vec![value(10, VirType::Bool)],
                    instructions: vec![],
                    terminator: terminator(VirTerminator::Jump {
                        target: target(3, &[10]),
                    }),
                    source_span: span(),
                },
                VirBasicBlock {
                    id: VirBlockId::new(2),
                    parameters: vec![value(20, VirType::Bool)],
                    instructions: vec![],
                    terminator: terminator(VirTerminator::Jump {
                        target: target(3, &[20]),
                    }),
                    source_span: span(),
                },
                VirBasicBlock {
                    id: VirBlockId::new(3),
                    parameters: vec![value(30, VirType::Bool)],
                    instructions: vec![
                        instruction(VirInstruction::Check {
                            condition: VirValueId::new(30),
                        }),
                        instruction(VirInstruction::Constant {
                            result: value(31, VirType::U64),
                            value: VirConstant::U64(0),
                        }),
                    ],
                    terminator: terminator(VirTerminator::Return {
                        values: vec![VirValueId::new(31)],
                    }),
                    source_span: span(),
                },
            ],
            source_span: span(),
        }],
    )
}
