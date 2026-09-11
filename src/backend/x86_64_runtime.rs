use crate::{RuntimeVirView, VirInstruction};

use super::{
    X86_64ConditionCode, X86_64ExternalSymbol, X86_64IntegerRegister, X86_64MachineBlock,
    X86_64MachineFunction, X86_64MachineInstruction, X86_64MachineLabel, X86_64MachineRead,
    X86_64MachineSymbol, X86_64MachineWrite, X86_64RuntimeHelper,
};

/// Builds only the backend-private helpers referenced by this closed program.
pub(super) fn lower_runtime_helpers(runtime: RuntimeVirView<'_>) -> Vec<X86_64MachineFunction> {
    if runtime
        .functions
        .iter()
        .flat_map(|function| &function.blocks)
        .flat_map(|block| &block.instructions)
        .any(|instruction| matches!(&instruction.instruction, VirInstruction::Allocate { .. }))
    {
        vec![lower_alloc_or_abort()]
    } else {
        Vec::new()
    }
}

/// Implements `_nera_alloc_or_abort(size, effective_alignment)`.
///
/// The caller has already applied `max(requested_alignment, 8)`. The helper
/// independently rejects zero sizes and malformed alignments, rounds the size
/// with checked arithmetic, and converts every libc failure into `abort`.
fn lower_alloc_or_abort() -> X86_64MachineFunction {
    let helper = X86_64RuntimeHelper::AllocOrAbort;
    let failure = X86_64MachineLabel::RuntimeFailure(helper);
    let instructions = vec![
        X86_64MachineInstruction::Push64 {
            register: X86_64IntegerRegister::Rbp,
        },
        move_register(X86_64IntegerRegister::Rbp, X86_64IntegerRegister::Rsp),
        X86_64MachineInstruction::Compare64 {
            left: X86_64IntegerRegister::Rdi,
            right: X86_64MachineRead::Immediate(0),
        },
        X86_64MachineInstruction::JumpIf {
            condition: X86_64ConditionCode::Equal,
            target: failure,
        },
        X86_64MachineInstruction::Compare64 {
            left: X86_64IntegerRegister::Rsi,
            right: X86_64MachineRead::Immediate(8),
        },
        X86_64MachineInstruction::JumpIf {
            condition: X86_64ConditionCode::Below,
            target: failure,
        },
        move_register(X86_64IntegerRegister::R10, X86_64IntegerRegister::Rsi),
        X86_64MachineInstruction::Subtract64 {
            destination: X86_64IntegerRegister::R10,
            source: X86_64MachineRead::Immediate(1),
        },
        move_register(X86_64IntegerRegister::R11, X86_64IntegerRegister::Rsi),
        X86_64MachineInstruction::And64 {
            destination: X86_64IntegerRegister::R11,
            source: X86_64MachineRead::Register(X86_64IntegerRegister::R10),
        },
        X86_64MachineInstruction::Compare64 {
            left: X86_64IntegerRegister::R11,
            right: X86_64MachineRead::Immediate(0),
        },
        X86_64MachineInstruction::JumpIf {
            condition: X86_64ConditionCode::NotEqual,
            target: failure,
        },
        move_register(X86_64IntegerRegister::R11, X86_64IntegerRegister::Rdi),
        X86_64MachineInstruction::Add64 {
            destination: X86_64IntegerRegister::R11,
            source: X86_64MachineRead::Register(X86_64IntegerRegister::R10),
        },
        X86_64MachineInstruction::JumpIf {
            condition: X86_64ConditionCode::Carry,
            target: failure,
        },
        move_register(X86_64IntegerRegister::R10, X86_64IntegerRegister::Rsi),
        X86_64MachineInstruction::Negate64 {
            register: X86_64IntegerRegister::R10,
        },
        X86_64MachineInstruction::And64 {
            destination: X86_64IntegerRegister::R11,
            source: X86_64MachineRead::Register(X86_64IntegerRegister::R10),
        },
        move_register(X86_64IntegerRegister::Rdi, X86_64IntegerRegister::Rsi),
        move_register(X86_64IntegerRegister::Rsi, X86_64IntegerRegister::R11),
        X86_64MachineInstruction::CallExternal {
            symbol: X86_64ExternalSymbol::AlignedAlloc,
        },
        X86_64MachineInstruction::Compare64 {
            left: X86_64IntegerRegister::Rax,
            right: X86_64MachineRead::Immediate(0),
        },
        X86_64MachineInstruction::JumpIf {
            condition: X86_64ConditionCode::Equal,
            target: failure,
        },
        X86_64MachineInstruction::Leave,
        X86_64MachineInstruction::Return,
    ];

    X86_64MachineFunction {
        symbol: X86_64MachineSymbol::RuntimeHelper(helper),
        blocks: vec![
            X86_64MachineBlock {
                label: X86_64MachineLabel::RuntimeHelper(helper),
                instructions,
            },
            X86_64MachineBlock {
                label: failure,
                instructions: vec![
                    X86_64MachineInstruction::CallExternal {
                        symbol: X86_64ExternalSymbol::Abort,
                    },
                    X86_64MachineInstruction::Trap,
                ],
            },
        ],
    }
}

const fn move_register(
    destination: X86_64IntegerRegister,
    source: X86_64IntegerRegister,
) -> X86_64MachineInstruction {
    X86_64MachineInstruction::Move64 {
        destination: X86_64MachineWrite::Register(destination),
        source: X86_64MachineRead::Register(source),
    }
}
