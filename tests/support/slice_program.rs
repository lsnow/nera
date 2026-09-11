#![allow(dead_code)]

use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, ValidatedVirUnit, VirAbiClass,
    VirBasicBlock, VirBlockId, VirConstant, VirContractId, VirEndianness, VirFunction,
    VirFunctionId, VirIndexBounds, VirInstruction, VirIntegerType, VirLayout, VirLayoutId,
    VirMemoryAccess, VirMemorySchema, VirMemoryType, VirMemoryTypeKind, VirMutability,
    VirSignature, VirTargetDataLayout, VirTerminator, VirType, VirTypeId, VirUnit, VirValue,
    VirValueId,
};

pub const U64_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(0), VirLayoutId::new(0));
pub const ARRAY_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(VirTypeId::new(1), VirLayoutId::new(1));
pub const SLICE_ACCESS: VirMemoryAccess =
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
                id: U64_ACCESS.ty,
                kind: VirMemoryTypeKind::Integer(VirIntegerType::U64),
                layout: U64_ACCESS.layout,
            },
            VirMemoryType {
                id: ARRAY_ACCESS.ty,
                kind: VirMemoryTypeKind::Array {
                    element: U64_ACCESS.ty,
                    length: 4,
                },
                layout: ARRAY_ACCESS.layout,
            },
            VirMemoryType {
                id: SLICE_ACCESS.ty,
                kind: VirMemoryTypeKind::Slice {
                    element: U64_ACCESS.ty,
                    mutability: VirMutability::Const,
                },
                layout: SLICE_ACCESS.layout,
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
                id: ARRAY_ACCESS.layout,
                ty: ARRAY_ACCESS.ty,
                size_bytes: 32,
                alignment: 8,
                abi: VirAbiClass::Aggregate,
                fields: vec![],
                variants: None,
            },
            VirLayout {
                id: SLICE_ACCESS.layout,
                ty: SLICE_ACCESS.ty,
                size_bytes: 16,
                alignment: 8,
                abi: VirAbiClass::ScalarPair,
                fields: vec![],
                variants: None,
            },
        ],
        fields: vec![],
        variants: vec![],
    };
    schema
        .assign_canonical_type_capabilities()
        .expect("slice schema capabilities");
    schema
}

fn constant(id: u32, value: u64) -> SpannedVirInstruction {
    instruction(VirInstruction::Constant {
        result: word(id),
        value: VirConstant::U64(value),
    })
}

fn initialized_array_prefix() -> Vec<SpannedVirInstruction> {
    let mut instructions = vec![instruction(VirInstruction::LocalStorage {
        pointer_result: pointer(0, ARRAY_ACCESS),
        permission_result: permission(1),
        access: ARRAY_ACCESS,
    })];
    for (ordinal, stored) in [10_u64, 20, 30, 40].into_iter().enumerate() {
        let ordinal = u32::try_from(ordinal).expect("small fixture ordinal");
        let index_id = 2 + ordinal * 3;
        let pointer_id = index_id + 1;
        let value_id = index_id + 2;
        instructions.extend([
            constant(index_id, u64::from(ordinal)),
            instruction(VirInstruction::IndexAddress {
                result: pointer(pointer_id, U64_ACCESS),
                base: VirValueId::new(0),
                index: VirValueId::new(index_id),
                source: ARRAY_ACCESS,
                element: U64_ACCESS,
                stride_bytes: 8,
                bounds: VirIndexBounds::Array { length: 4 },
            }),
            constant(value_id, stored),
            instruction(VirInstruction::Initialize {
                pointer: VirValueId::new(pointer_id),
                value: VirValueId::new(value_id),
                permission: VirValueId::new(1),
                access: U64_ACCESS,
            }),
        ]);
    }
    instructions
}

fn unit(name: &str, instructions: Vec<SpannedVirInstruction>, result: u32) -> VirUnit {
    VirUnit::from_runtime(
        schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: name.to_owned(),
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
                        values: vec![VirValueId::new(result)],
                    },
                    source_span: span(),
                },
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

pub fn full_unit() -> VirUnit {
    let mut instructions = initialized_array_prefix();
    instructions.extend([
        constant(14, 1),
        constant(15, 4),
        instruction(VirInstruction::SliceRange {
            pointer_result: pointer(16, U64_ACCESS),
            length_result: word(17),
            permission_result: permission(18),
            base: VirValueId::new(0),
            permission: VirValueId::new(1),
            start: VirValueId::new(14),
            end: VirValueId::new(15),
            source: ARRAY_ACCESS,
            slice: SLICE_ACCESS,
            element: U64_ACCESS,
            stride_bytes: 8,
            bounds: VirIndexBounds::Array { length: 4 },
        }),
        constant(19, 1),
        constant(20, 3),
        instruction(VirInstruction::SliceRange {
            pointer_result: pointer(21, U64_ACCESS),
            length_result: word(22),
            permission_result: permission(23),
            base: VirValueId::new(16),
            permission: VirValueId::new(18),
            start: VirValueId::new(19),
            end: VirValueId::new(20),
            source: SLICE_ACCESS,
            slice: SLICE_ACCESS,
            element: U64_ACCESS,
            stride_bytes: 8,
            bounds: VirIndexBounds::Slice {
                length: VirValueId::new(17),
            },
        }),
        constant(24, 1),
        instruction(VirInstruction::IndexAddress {
            result: pointer(25, U64_ACCESS),
            base: VirValueId::new(21),
            index: VirValueId::new(24),
            source: SLICE_ACCESS,
            element: U64_ACCESS,
            stride_bytes: 8,
            bounds: VirIndexBounds::Slice {
                length: VirValueId::new(22),
            },
        }),
        instruction(VirInstruction::Load {
            result: word(26),
            pointer: VirValueId::new(25),
            permission: VirValueId::new(23),
            access: U64_ACCESS,
        }),
    ]);
    unit("slice_range", instructions, 26)
}

pub fn validated() -> ValidatedVirUnit {
    full_unit()
        .into_validated()
        .expect("slice range fixture validates")
}

pub fn one_range_unit(start: u64, end: u64) -> VirUnit {
    let mut instructions = initialized_array_prefix();
    instructions.extend([
        constant(14, start),
        constant(15, end),
        instruction(VirInstruction::SliceRange {
            pointer_result: pointer(16, U64_ACCESS),
            length_result: word(17),
            permission_result: permission(18),
            base: VirValueId::new(0),
            permission: VirValueId::new(1),
            start: VirValueId::new(14),
            end: VirValueId::new(15),
            source: ARRAY_ACCESS,
            slice: SLICE_ACCESS,
            element: U64_ACCESS,
            stride_bytes: 8,
            bounds: VirIndexBounds::Array { length: 4 },
        }),
    ]);
    unit("one_slice_range", instructions, 17)
}
