use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, VirAbiClass, VirBasicBlock, VirBlockId,
    VirBorrowEnvironment, VirBorrowRegion, VirBorrowRegionConstraint, VirBorrowRegionConstraintId,
    VirBorrowRegionId, VirBorrowRegionOrigin, VirBorrowRegionScope, VirConstant, VirContractId,
    VirEndianness, VirFunction, VirFunctionId, VirInstruction, VirIntegerType, VirLayout,
    VirLayoutId, VirLoanEffect, VirLoanId, VirLoanKind, VirLoanRange, VirMemoryAccess,
    VirMemorySchema, VirMemoryType, VirMemoryTypeKind, VirMutability, VirOriginId, VirPointerKind,
    VirRegionId, VirSignature, VirTargetDataLayout, VirTerminator, VirType, VirTypeId, VirUnit,
    VirValue, VirValueId,
};

pub const U64_TYPE: VirTypeId = VirTypeId::new(0);
pub const SHARED_REFERENCE_TYPE: VirTypeId = VirTypeId::new(1);
pub const MUTABLE_REFERENCE_TYPE: VirTypeId = VirTypeId::new(2);
pub const U64_ACCESS: VirMemoryAccess = VirMemoryAccess::new(U64_TYPE, VirLayoutId::new(0));
pub const SHARED_REFERENCE_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(SHARED_REFERENCE_TYPE, VirLayoutId::new(1));
pub const MUTABLE_REFERENCE_ACCESS: VirMemoryAccess =
    VirMemoryAccess::new(MUTABLE_REFERENCE_TYPE, VirLayoutId::new(2));

pub fn span(start: usize) -> ByteSpan {
    ByteSpan::new(start, start + 1).expect("valid test span")
}

pub fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

pub fn pointer(id: u32) -> VirValue {
    value(id, VirType::Pointer { access: U64_ACCESS })
}

pub fn permission(id: u32) -> VirValue {
    value(id, VirType::Permission)
}

pub fn spanned(index: usize, instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(10 + index * 2),
    }
}

pub fn effect(
    loan: u32,
    kind: VirLoanKind,
    region: u32,
    parent: Option<u32>,
    source_pointer: u32,
    source_permission: u32,
) -> VirLoanEffect {
    VirLoanEffect {
        loan: VirLoanId::new(loan),
        kind,
        region: VirBorrowRegionId::new(region),
        parent: parent.map(VirLoanId::new),
        source_pointer: VirValueId::new(source_pointer),
        source_permission: VirValueId::new(source_permission),
        reference: match kind {
            VirLoanKind::Shared => SHARED_REFERENCE_ACCESS,
            VirLoanKind::Mutable => MUTABLE_REFERENCE_ACCESS,
        },
        range: VirLoanRange {
            start_bytes: 0,
            end_bytes: 8,
        },
        origin: VirOriginId::new(0),
    }
}

pub fn memory_schema() -> VirMemorySchema {
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
                id: U64_TYPE,
                kind: VirMemoryTypeKind::Integer(VirIntegerType::U64),
                layout: VirLayoutId::new(0),
            },
            VirMemoryType {
                id: SHARED_REFERENCE_TYPE,
                kind: VirMemoryTypeKind::Pointer {
                    pointee: U64_TYPE,
                    kind: VirPointerKind::Reference,
                    mutability: VirMutability::Const,
                },
                layout: VirLayoutId::new(1),
            },
            VirMemoryType {
                id: MUTABLE_REFERENCE_TYPE,
                kind: VirMemoryTypeKind::Pointer {
                    pointee: U64_TYPE,
                    kind: VirPointerKind::Reference,
                    mutability: VirMutability::Mutable,
                },
                layout: VirLayoutId::new(2),
            },
        ],
        type_capabilities: Vec::new(),
        layouts: vec![
            VirLayout {
                id: VirLayoutId::new(0),
                ty: U64_TYPE,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(1),
                ty: SHARED_REFERENCE_TYPE,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            },
            VirLayout {
                id: VirLayoutId::new(2),
                ty: MUTABLE_REFERENCE_TYPE,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: Vec::new(),
                variants: None,
            },
        ],
        fields: Vec::new(),
        variants: Vec::new(),
    };
    schema
        .assign_canonical_type_capabilities()
        .expect("reference capabilities derive");
    schema
}

pub fn unit(instructions: Vec<SpannedVirInstruction>, region_count: u32) -> VirUnit {
    let source_end = 20 + instructions.len() * 2;
    let mut unit = VirUnit::from_runtime(
        memory_schema(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "loan_transfer".to_owned(),
            signature: VirSignature {
                parameters: Vec::new(),
                results: Vec::new(),
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: Vec::new(),
                instructions,
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return { values: Vec::new() },
                    source_span: span(source_end - 2),
                },
                source_span: ByteSpan::new(5, source_end).expect("block span"),
            }],
            source_span: ByteSpan::new(0, source_end + 1).expect("function span"),
        }],
    );
    let regions = (0..region_count)
        .map(|id| VirBorrowRegion {
            id: VirBorrowRegionId::new(id),
            owner: VirFunctionId::new(0),
            origin: VirBorrowRegionOrigin::Inferred,
            scope: VirBorrowRegionScope::Blocks(vec![VirBlockId::new(0)]),
            source_origin: VirOriginId::new(0),
        })
        .collect();
    let constraints = (1..region_count)
        .map(|id| VirBorrowRegionConstraint {
            id: VirBorrowRegionConstraintId::new(id - 1),
            owner: VirFunctionId::new(0),
            subregion: VirBorrowRegionId::new(id),
            superregion: VirBorrowRegionId::new(id - 1),
            source_origin: VirOriginId::new(0),
        })
        .collect();
    unit.borrows = VirBorrowEnvironment::from_tables(regions, constraints);
    unit
}

pub fn allocation_prefix() -> Vec<SpannedVirInstruction> {
    vec![
        spanned(
            0,
            VirInstruction::Constant {
                result: value(0, VirType::U64),
                value: VirConstant::U64(8),
            },
        ),
        spanned(
            1,
            VirInstruction::Allocate {
                pointer_result: pointer(1),
                permission_result: permission(2),
                size_bytes: VirValueId::new(0),
                alignment: 8,
                region: VirRegionId::new(0),
                element: U64_ACCESS,
            },
        ),
        spanned(
            2,
            VirInstruction::Constant {
                result: value(3, VirType::U64),
                value: VirConstant::U64(7),
            },
        ),
        spanned(
            3,
            VirInstruction::Initialize {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: U64_ACCESS,
            },
        ),
    ]
}

pub fn shared_lifecycle() -> VirUnit {
    let mut instructions = allocation_prefix();
    instructions.extend([
        spanned(
            4,
            VirInstruction::LoanBegin {
                effect: effect(0, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: pointer(4),
                permission_result: permission(5),
            },
        ),
        spanned(
            5,
            VirInstruction::Load {
                result: value(6, VirType::U64),
                pointer: VirValueId::new(4),
                permission: VirValueId::new(5),
                access: U64_ACCESS,
            },
        ),
        spanned(
            6,
            VirInstruction::LoanAliasShared {
                effect: effect(0, VirLoanKind::Shared, 0, None, 4, 5),
                reference_result: pointer(7),
                permission_result: permission(8),
            },
        ),
        spanned(
            7,
            VirInstruction::LoanEnd {
                effect: effect(0, VirLoanKind::Shared, 0, None, 7, 8),
            },
        ),
        spanned(
            8,
            VirInstruction::LoanEnd {
                effect: effect(0, VirLoanKind::Shared, 0, None, 4, 5),
            },
        ),
        spanned(
            9,
            VirInstruction::Store {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(2),
                access: U64_ACCESS,
            },
        ),
        spanned(
            10,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);
    unit(instructions, 1)
}
