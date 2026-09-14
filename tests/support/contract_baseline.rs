//! Historical 8.2.1 targets; individual features are opened by later steps.
//! Erasure is a test-only baseline builder, never a compiler fallback.
use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, VirBasicBlock, VirBlockId,
    VirCallTarget, VirConstant, VirContractId, VirContractPosition, VirFunction, VirFunctionId,
    VirInstruction, VirLocation, VirMemorySchema, VirSignature, VirSpecClauseKind,
    VirSpecClauseOrigin, VirTerminator, VirType, VirUnit, VirValue, VirValueId,
};

pub const SCALAR: &str = include_str!("../../spec/cases/verify/contract-scalar-target.nera");
pub const CELL: &str = include_str!("../../spec/cases/verify/contract-cell-target.nera");
pub const ARENA: &str = include_str!("../../spec/cases/verify/contract-arena-target.nera");

pub fn is_contract_line(line: &str) -> bool {
    ["requires ", "ensures ", "reads ", "writes "]
        .iter()
        .any(|prefix| line.trim_start().starts_with(prefix))
}

pub fn erased(source: &str) -> String {
    source
        .split('\n')
        .map(|line| {
            if is_contract_line(line) {
                " ".repeat(line.len())
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Independent of frontend lowering: a real main call and a bounded identity
/// interface. Changing the body must defeat publication even with a valid caller.
pub fn scalar_unit(argument: u64, wrong_body: bool) -> VirUnit {
    let span = ByteSpan::new(0, 1).unwrap();
    let id = VirValueId::new;
    let word = |raw| VirValue {
        id: id(raw),
        ty: VirType::U64,
    };
    let signature = VirSignature {
        parameters: vec![VirType::U64],
        results: vec![VirType::U64],
    };
    let function =
        |raw, name: &str, parameters: Vec<VirValue>, instructions: Vec<VirInstruction>, result| {
            VirFunction {
                id: VirFunctionId::new(raw),
                name: name.into(),
                signature: VirSignature {
                    parameters: parameters.iter().map(|v| v.ty).collect(),
                    results: vec![VirType::U64],
                },
                contract: VirContractId::new(raw),
                entry: VirBlockId::new(0),
                source_span: span,
                blocks: vec![VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters,
                    source_span: span,
                    instructions: instructions
                        .into_iter()
                        .map(|instruction| SpannedVirInstruction {
                            instruction,
                            source_span: span,
                        })
                        .collect(),
                    terminator: SpannedVirTerminator {
                        terminator: VirTerminator::Return {
                            values: vec![id(result)],
                        },
                        source_span: span,
                    },
                }],
            }
        };
    let main = function(
        0,
        "main",
        vec![],
        vec![
            VirInstruction::Constant {
                result: word(0),
                value: VirConstant::U64(argument),
            },
            VirInstruction::Call {
                target: VirCallTarget {
                    symbol: "bounded".into(),
                    signature,
                    contract: VirContractId::new(1),
                    abi: None,
                },
                arguments: vec![id(0)],
                results: vec![word(1)],
            },
        ],
        1,
    );
    let body = if wrong_body {
        vec![VirInstruction::Constant {
            result: word(1),
            value: VirConstant::U64(99),
        }]
    } else {
        vec![]
    };
    let bounded = function(1, "bounded", vec![word(0)], body, u32::from(wrong_body));
    let mut unit = VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![main, bounded],
    );
    let origin = unit
        .source_map
        .origin_at(VirLocation::FunctionEntry {
            function: VirFunctionId::new(1),
        })
        .unwrap()
        .id;
    for position in [VirContractPosition::Requires, VirContractPosition::Ensures] {
        let binder = unit
            .specs
            .contract(VirContractId::new(1))
            .unwrap()
            .binder(position, 0)
            .unwrap();
        unit.specs
            .add_contract_clause(
                VirContractId::new(1),
                position,
                VirSpecClauseOrigin::Explicit { origin },
                VirSpecClauseKind::U64Range {
                    binder,
                    lower: 1,
                    upper: 2,
                },
            )
            .unwrap();
    }
    unit
}
