#![allow(dead_code)]

use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, ValidatedVirUnit, VirBasicBlock,
    VirBlockId, VirBlockTarget, VirCallTarget, VirConstant, VirContractId, VirFunction,
    VirFunctionId, VirInstruction, VirMemorySchema, VirSignature, VirTerminator, VirType, VirUnit,
    VirValue, VirValueId,
};

pub fn span() -> ByteSpan {
    ByteSpan::new(0, 1).expect("ordered fixture span")
}

pub const fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

pub fn word(id: u32) -> VirValue {
    value(id, VirType::U64)
}

pub fn boolean(id: u32) -> VirValue {
    value(id, VirType::Bool)
}

pub fn pointer(id: u32) -> VirValue {
    value(
        id,
        VirType::Pointer {
            access: nera::VirMemoryAccess::core_u64(),
        },
    )
}

pub fn permission(id: u32) -> VirValue {
    value(id, VirType::Permission)
}

pub fn instruction(instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(),
    }
}

pub fn terminator(terminator: VirTerminator) -> SpannedVirTerminator {
    SpannedVirTerminator {
        terminator,
        source_span: span(),
    }
}

pub fn target(block: u32, arguments: &[u32]) -> VirBlockTarget {
    VirBlockTarget {
        block: VirBlockId::new(block),
        arguments: arguments.iter().copied().map(VirValueId::new).collect(),
    }
}

pub fn block(
    id: u32,
    parameters: Vec<VirValue>,
    instructions: Vec<SpannedVirInstruction>,
    terminator_kind: VirTerminator,
) -> VirBasicBlock {
    VirBasicBlock {
        id: VirBlockId::new(id),
        parameters,
        instructions,
        terminator: terminator(terminator_kind),
        source_span: span(),
    }
}

pub fn function(
    id: u32,
    name: &str,
    parameters: Vec<VirType>,
    results: Vec<VirType>,
    blocks: Vec<VirBasicBlock>,
) -> VirFunction {
    VirFunction {
        id: VirFunctionId::new(id),
        name: name.to_owned(),
        signature: VirSignature {
            parameters,
            results,
        },
        contract: VirContractId::new(id),
        entry: VirBlockId::new(0),
        blocks,
        source_span: span(),
    }
}

pub fn local(pointer_id: u32, permission_id: u32) -> SpannedVirInstruction {
    instruction(VirInstruction::LocalStorage {
        pointer_result: pointer(pointer_id),
        permission_result: permission(permission_id),
        access: nera::VirMemoryAccess::core_u64(),
    })
}

pub fn scalar_program(value_to_store: u64) -> VirUnit {
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![function(
            0,
            "local_scalar",
            vec![],
            vec![VirType::U64],
            vec![block(
                0,
                vec![],
                vec![
                    local(0, 1),
                    instruction(VirInstruction::Constant {
                        result: word(2),
                        value: VirConstant::U64(value_to_store),
                    }),
                    instruction(VirInstruction::Initialize {
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
                    instruction(VirInstruction::Store {
                        pointer: VirValueId::new(0),
                        value: VirValueId::new(3),
                        permission: VirValueId::new(1),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                ],
                VirTerminator::Return {
                    values: vec![VirValueId::new(3)],
                },
            )],
        )],
    )
}

pub fn recursive_program() -> ValidatedVirUnit {
    let recursive_signature = VirSignature {
        parameters: vec![VirType::Bool],
        results: vec![VirType::U64],
    };
    let recursive_target = VirCallTarget {
        symbol: "recursive_local".to_owned(),
        signature: recursive_signature.clone(),
        contract: VirContractId::new(1),
        abi: None,
    };
    let main = function(
        0,
        "main",
        vec![],
        vec![VirType::U64],
        vec![block(
            0,
            vec![],
            vec![
                instruction(VirInstruction::Constant {
                    result: boolean(0),
                    value: VirConstant::Bool(true),
                }),
                instruction(VirInstruction::Call {
                    results: vec![word(1)],
                    target: recursive_target.clone(),
                    arguments: vec![VirValueId::new(0)],
                }),
            ],
            VirTerminator::Return {
                values: vec![VirValueId::new(1)],
            },
        )],
    );
    let recursive = function(
        1,
        "recursive_local",
        recursive_signature.parameters.clone(),
        recursive_signature.results.clone(),
        vec![
            block(
                0,
                vec![boolean(100)],
                vec![
                    local(101, 102),
                    instruction(VirInstruction::Constant {
                        result: boolean(103),
                        value: VirConstant::Bool(false),
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(104),
                        value: VirConstant::U64(11),
                    }),
                    instruction(VirInstruction::Constant {
                        result: word(105),
                        value: VirConstant::U64(22),
                    }),
                ],
                VirTerminator::Branch {
                    condition: VirValueId::new(100),
                    then_target: target(1, &[101, 102, 103, 104]),
                    else_target: target(2, &[101, 102, 105]),
                },
            ),
            block(
                1,
                vec![pointer(110), permission(111), boolean(112), word(113)],
                vec![
                    instruction(VirInstruction::Initialize {
                        pointer: VirValueId::new(110),
                        value: VirValueId::new(113),
                        permission: VirValueId::new(111),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Call {
                        results: vec![word(114)],
                        target: recursive_target,
                        arguments: vec![VirValueId::new(112)],
                    }),
                    instruction(VirInstruction::Load {
                        result: word(115),
                        pointer: VirValueId::new(110),
                        permission: VirValueId::new(111),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                ],
                VirTerminator::Return {
                    values: vec![VirValueId::new(115)],
                },
            ),
            block(
                2,
                vec![pointer(120), permission(121), word(122)],
                vec![
                    instruction(VirInstruction::Initialize {
                        pointer: VirValueId::new(120),
                        value: VirValueId::new(122),
                        permission: VirValueId::new(121),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Load {
                        result: word(123),
                        pointer: VirValueId::new(120),
                        permission: VirValueId::new(121),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                ],
                VirTerminator::Return {
                    values: vec![VirValueId::new(123)],
                },
            ),
        ],
    );
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![main, recursive],
    )
    .into_validated()
    .expect("recursive local-storage fixture validates")
}
