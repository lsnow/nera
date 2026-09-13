//! Two dynamic cuts in one allocation. Explicit scalar input ranges are checked
//! at the real caller; no resource/trust premise supplies the allocated memory.
use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, VirBasicBlock, VirBlockId,
    VirCallTarget, VirConstant, VirContractId, VirContractPosition, VirFunction, VirFunctionId,
    VirInstruction, VirMemoryAccess, VirMemorySchema, VirRegionId, VirSignature, VirTerminator,
    VirType, VirUnit, VirValue, VirValueId,
};

#[path = "contract_builder.rs"]
mod contract_builder;

pub const SOURCE: &str = include_str!("../../spec/cases/verify/spec-arena-baseline.nera");

#[derive(Clone, Copy, Debug)]
pub enum Mutation {
    None,
    OutOfBounds,
    OverlappingPermission,
    Uninitialized,
    UseAfterReturn,
    CallerPrecondition,
    DynamicInitialization,
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

fn permission(id: u32) -> VirValue {
    value(id, VirType::Permission)
}

fn pointer(id: u32) -> VirValue {
    value(
        id,
        VirType::Pointer {
            access: VirMemoryAccess::core_u64(),
        },
    )
}

fn constant(id: u32, number: u64) -> VirInstruction {
    VirInstruction::Constant {
        result: word(id),
        value: VirConstant::U64(number),
    }
}

fn function(
    id: u32,
    name: &str,
    parameters: Vec<VirValue>,
    instructions: Vec<VirInstruction>,
    result: u32,
) -> VirFunction {
    let span = ByteSpan::new(0, 1).unwrap();
    VirFunction {
        id: VirFunctionId::new(id),
        name: name.into(),
        signature: VirSignature {
            parameters: parameters.iter().map(|p| p.ty).collect(),
            results: vec![VirType::U64],
        },
        contract: VirContractId::new(id),
        entry: VirBlockId::new(0),
        blocks: vec![VirBasicBlock {
            id: VirBlockId::new(0),
            parameters,
            instructions: instructions
                .into_iter()
                .map(|instruction| SpannedVirInstruction {
                    instruction,
                    source_span: span,
                })
                .collect(),
            terminator: SpannedVirTerminator {
                terminator: VirTerminator::Return {
                    values: vec![VirValueId::new(result)],
                },
                source_span: span,
            },
            source_span: span,
        }],
        source_span: span,
    }
}

pub fn unit(first: u64, second: u64, mutation: Mutation) -> VirUnit {
    let id = VirValueId::new;
    let access = VirMemoryAccess::core_u64();
    let mut body = vec![
        constant(
            2,
            if matches!(mutation, Mutation::OutOfBounds) {
                8
            } else {
                48
            },
        ),
        VirInstruction::Allocate {
            pointer_result: pointer(3),
            permission_result: permission(4),
            size_bytes: id(2),
            alignment: 8,
            region: VirRegionId::new(0),
            element: access,
        },
    ];
    // Scale each scalar parameter by eight without adding an arithmetic theory.
    for (input, base) in [(0, 5), (1, 8)] {
        for (out, operand) in [(base, input), (base + 1, base), (base + 2, base + 1)] {
            body.push(VirInstruction::WordAdd {
                result: word(out),
                left: id(operand),
                right: id(operand),
            });
        }
    }
    body.extend([
        constant(27, 16),
        constant(28, 32),
        VirInstruction::PermissionSplit {
            left_result: permission(11),
            right_result: permission(12),
            source: id(4),
            split_at_bytes: id(7),
        },
        VirInstruction::PermissionSplit {
            left_result: permission(13),
            right_result: permission(14),
            source: id(12),
            split_at_bytes: id(10),
        },
        VirInstruction::PointerOffset {
            result: pointer(15),
            base: id(3),
            delta_bytes: id(if matches!(mutation, Mutation::DynamicInitialization) {
                7
            } else {
                27
            }),
        },
        VirInstruction::PointerOffset {
            result: pointer(16),
            base: id(3),
            delta_bytes: id(if matches!(mutation, Mutation::DynamicInitialization) {
                10
            } else {
                28
            }),
        },
        constant(17, 7),
        VirInstruction::Initialize {
            pointer: id(16),
            value: id(17),
            permission: id(14),
            access,
        },
        constant(18, 12),
        VirInstruction::Initialize {
            pointer: id(3),
            value: id(18),
            permission: id(11),
            access,
        },
        constant(19, 30),
    ]);
    if !matches!(mutation, Mutation::Uninitialized) {
        body.push(VirInstruction::Initialize {
            pointer: id(15),
            value: id(19),
            permission: id(if matches!(mutation, Mutation::OverlappingPermission) {
                11
            } else {
                13
            }),
            access,
        });
    }
    body.extend([
        VirInstruction::Load {
            result: word(20),
            pointer: id(3),
            permission: id(11),
            access,
        },
        VirInstruction::Load {
            result: word(21),
            pointer: id(15),
            permission: id(13),
            access,
        },
        VirInstruction::Load {
            result: word(22),
            pointer: id(16),
            permission: id(14),
            access,
        },
        VirInstruction::WordAdd {
            result: word(23),
            left: id(20),
            right: id(21),
        },
        VirInstruction::WordAdd {
            result: word(24),
            left: id(23),
            right: id(22),
        },
        VirInstruction::PermissionJoin {
            result: permission(25),
            left: id(13),
            right: id(14),
        },
        VirInstruction::PermissionJoin {
            result: permission(26),
            left: id(11),
            right: id(25),
        },
    ]);
    if matches!(mutation, Mutation::UseAfterReturn) {
        body.push(VirInstruction::Load {
            result: word(29),
            pointer: id(15),
            permission: id(13),
            access,
        });
    }
    body.push(VirInstruction::Free {
        pointer: id(3),
        permission: id(26),
    });
    let arena = function(1, "arena_raw", vec![word(0), word(1)], body, 24);
    let caller = function(
        0,
        "main",
        vec![],
        vec![
            constant(
                0,
                if matches!(mutation, Mutation::CallerPrecondition) {
                    0
                } else {
                    first
                },
            ),
            constant(1, second),
            VirInstruction::Call {
                results: vec![word(2)],
                target: VirCallTarget {
                    symbol: arena.name.clone(),
                    signature: arena.signature.clone(),
                    contract: arena.contract,
                    abi: None,
                },
                arguments: vec![id(0), id(1)],
            },
        ],
        2,
    );
    let mut unit = VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![caller, arena],
    );
    let origin = contract_builder::function_origin(&unit, VirFunctionId::new(1));
    for (slot, low, high) in [(0, 1, 2), (1, 3, 4)] {
        contract_builder::add_u64_range(
            &mut unit.specs,
            VirContractId::new(1),
            VirContractPosition::Requires,
            origin,
            slot,
            low,
            high,
        );
    }
    unit
}
