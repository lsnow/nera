#![allow(dead_code)]

use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, ValidatedVirUnit, VirAbiClass,
    VirBasicBlock, VirBlockId, VirConstant, VirContractId, VirEndianness, VirField, VirFieldId,
    VirFieldLayout, VirFunction, VirFunctionId, VirIndexBounds, VirInstruction, VirIntegerType,
    VirLayout, VirLayoutId, VirMemoryAccess, VirMemorySchema, VirMemoryType, VirMemoryTypeKind,
    VirRegionId, VirSignature, VirTargetDataLayout, VirTerminator, VirType, VirTypeId, VirUnit,
    VirValue, VirValueId,
};

pub const U64_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(0), VirLayoutId::new(0));
pub const ARRAY_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(1), VirLayoutId::new(1));
pub const RECORD_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(2), VirLayoutId::new(2));

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
                id: VirTypeId::new(0),
                kind: VirMemoryTypeKind::Integer(VirIntegerType::U64),
                layout: VirLayoutId::new(0),
            },
            VirMemoryType {
                id: VirTypeId::new(1),
                kind: VirMemoryTypeKind::Array {
                    element: VirTypeId::new(0),
                    length: 4,
                },
                layout: VirLayoutId::new(1),
            },
            VirMemoryType {
                id: VirTypeId::new(2),
                kind: VirMemoryTypeKind::Struct {
                    fields: vec![VirFieldId::new(0)],
                },
                layout: VirLayoutId::new(2),
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
                size_bytes: 32,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![],
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(2),
                ty: VirTypeId::new(2),
                size_bytes: 40,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![VirFieldLayout {
                    field: VirFieldId::new(0),
                    offset_bytes: 8,
                }],
                variants: None,
            },
        ],
        fields: vec![VirField {
            id: VirFieldId::new(0),
            owner: VirTypeId::new(2),
            ty: VirTypeId::new(1),
        }],
        variants: vec![],
    };
    schema
        .assign_canonical_type_capabilities()
        .expect("address schema capabilities");
    schema
}

pub fn validated() -> ValidatedVirUnit {
    VirUnit::from_runtime(
        schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "typed_address".to_owned(),
            signature: VirSignature {
                parameters: vec![],
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: vec![],
                instructions: vec![
                    instruction(VirInstruction::Constant {
                        result: word(0),
                        value: VirConstant::U64(40),
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
                        result: pointer(3, ARRAY_ACCESS),
                        base: VirValueId::new(1),
                        field: VirFieldId::new(0),
                        owner: RECORD_ACCESS,
                        field_access: ARRAY_ACCESS,
                        offset_bytes: 8,
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(4),
                        value: VirConstant::U64(2),
                    }),
                    instruction(VirInstruction::IndexAddress {
                        result: pointer(5, U64_ACCESS),
                        base: VirValueId::new(3),
                        index: VirValueId::new(4),
                        source: ARRAY_ACCESS,
                        element: U64_ACCESS,
                        stride_bytes: 8,
                        bounds: VirIndexBounds::Array { length: 4 },
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(6),
                        value: VirConstant::U64(99),
                    }),
                    instruction(VirInstruction::Write {
                        pointer: VirValueId::new(5),
                        value: VirValueId::new(6),
                        permission: VirValueId::new(2),
                        access: U64_ACCESS,
                    }),
                    instruction(VirInstruction::Load {
                        result: word(7),
                        pointer: VirValueId::new(5),
                        permission: VirValueId::new(2),
                        access: U64_ACCESS,
                    }),
                    instruction(VirInstruction::Free {
                        pointer: VirValueId::new(1),
                        permission: VirValueId::new(2),
                    }),
                ],
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return {
                        values: vec![VirValueId::new(7)],
                    },
                    source_span: span(),
                },
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
    .into_validated()
    .expect("canonical typed-address fixture validates")
}
