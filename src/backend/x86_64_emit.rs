use std::collections::BTreeSet;
use std::error::Error;
use std::fmt::{self, Write};

use super::{
    X86_64BranchArm, X86_64ByteRegister, X86_64ConditionCode, X86_64ExternalSymbol,
    X86_64IntegerRegister, X86_64LinuxTarget, X86_64MachineByteRead, X86_64MachineByteWrite,
    X86_64MachineFunction, X86_64MachineInstruction, X86_64MachineLabel, X86_64MachineMemory,
    X86_64MachineProgram, X86_64MachineRead, X86_64MachineSymbol, X86_64MachineWrite,
    X86_64RuntimeHelper,
};

impl X86_64LinuxTarget {
    /// Emits deterministic GNU assembler text without invoking external tools.
    pub fn emit_assembly(
        self,
        program: &X86_64MachineProgram,
    ) -> Result<String, X86_64AssemblyError> {
        AssemblyEmitter::new().emit(program)
    }
}

/// A structural or x86 encoding error in a compiler-owned machine plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64AssemblyError {
    kind: X86_64AssemblyErrorKind,
    function: Option<X86_64MachineSymbol>,
    block: Option<X86_64MachineLabel>,
    instruction_index: Option<usize>,
}

impl X86_64AssemblyError {
    #[must_use]
    pub const fn kind(&self) -> &X86_64AssemblyErrorKind {
        &self.kind
    }

    #[must_use]
    pub const fn function(&self) -> Option<X86_64MachineSymbol> {
        self.function
    }

    #[must_use]
    pub const fn block(&self) -> Option<X86_64MachineLabel> {
        self.block
    }

    #[must_use]
    pub const fn instruction_index(&self) -> Option<usize> {
        self.instruction_index
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum X86_64AssemblyErrorKind {
    EmptyFunction,
    EntryLabelMismatch {
        expected: X86_64MachineLabel,
        actual: X86_64MachineLabel,
    },
    ForeignBlockLabel(X86_64MachineLabel),
    DuplicateLabel(String),
    MissingJumpTarget(X86_64MachineLabel),
    MissingCallTarget(X86_64MachineSymbol),
    IllegalOperandShape(&'static str),
    ImmediateNotEncodable {
        instruction: &'static str,
        value: u64,
    },
}

impl fmt::Display for X86_64AssemblyError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("x86_64 assembly emission failed")?;
        if let Some(function) = self.function {
            write!(formatter, " in {function:?}")?;
        }
        if let Some(block) = self.block {
            write!(formatter, "/{block:?}")?;
        }
        if let Some(index) = self.instruction_index {
            write!(formatter, "/instruction {index}")?;
        }
        formatter.write_str(": ")?;
        match &self.kind {
            X86_64AssemblyErrorKind::EmptyFunction => {
                formatter.write_str("machine function has no blocks")
            }
            X86_64AssemblyErrorKind::EntryLabelMismatch { expected, actual } => write!(
                formatter,
                "entry label {actual:?} does not match expected {expected:?}"
            ),
            X86_64AssemblyErrorKind::ForeignBlockLabel(label) => {
                write!(
                    formatter,
                    "block label {label:?} belongs to another function"
                )
            }
            X86_64AssemblyErrorKind::DuplicateLabel(label) => {
                write!(formatter, "assembly label `{label}` is duplicated")
            }
            X86_64AssemblyErrorKind::MissingJumpTarget(label) => {
                write!(
                    formatter,
                    "jump target {label:?} is not defined in this function"
                )
            }
            X86_64AssemblyErrorKind::MissingCallTarget(symbol) => {
                write!(
                    formatter,
                    "call target {symbol:?} is not defined in this program"
                )
            }
            X86_64AssemblyErrorKind::IllegalOperandShape(context) => {
                write!(
                    formatter,
                    "instruction has an illegal operand shape: {context}"
                )
            }
            X86_64AssemblyErrorKind::ImmediateNotEncodable { instruction, value } => write!(
                formatter,
                "{instruction} immediate 0x{value:016x} is not a sign-extended imm32"
            ),
        }
    }
}

impl Error for X86_64AssemblyError {}

struct AssemblyEmitter {
    output: String,
    labels: BTreeSet<String>,
}

impl AssemblyEmitter {
    fn new() -> Self {
        Self {
            output: String::new(),
            labels: BTreeSet::new(),
        }
    }

    fn emit(mut self, program: &X86_64MachineProgram) -> Result<String, X86_64AssemblyError> {
        validate_call_targets(program)?;
        writeln!(self.output, ".intel_syntax noprefix").expect("writing to String cannot fail");
        for symbol in external_symbols(program) {
            writeln!(self.output, ".extern {}", external_symbol(symbol))
                .expect("writing to String cannot fail");
        }
        writeln!(self.output, ".text").expect("writing to String cannot fail");

        for function in program
            .functions()
            .iter()
            .chain(program.runtime_functions())
            .chain(std::iter::once(program.executable_entry()))
        {
            self.emit_function(function)?;
        }
        writeln!(self.output, ".section .note.GNU-stack,\"\",@progbits")
            .expect("writing to String cannot fail");
        Ok(self.output)
    }

    fn emit_function(
        &mut self,
        function: &X86_64MachineFunction,
    ) -> Result<(), X86_64AssemblyError> {
        let symbol = function.symbol();
        let Some(entry) = function.blocks().first() else {
            return Err(assembly_error(
                X86_64AssemblyErrorKind::EmptyFunction,
                Some(symbol),
                None,
                None,
            ));
        };
        let expected = entry_label(symbol);
        if entry.label() != expected {
            return Err(assembly_error(
                X86_64AssemblyErrorKind::EntryLabelMismatch {
                    expected,
                    actual: entry.label(),
                },
                Some(symbol),
                Some(entry.label()),
                None,
            ));
        }

        let symbol_text = label(expected);
        writeln!(self.output).expect("writing to String cannot fail");
        writeln!(self.output, ".p2align 4").expect("writing to String cannot fail");
        match symbol {
            X86_64MachineSymbol::ExecutableEntry => {
                writeln!(self.output, ".globl {symbol_text}")
                    .expect("writing to String cannot fail");
            }
            X86_64MachineSymbol::RuntimeHelper(_) => {
                writeln!(self.output, ".local {symbol_text}")
                    .expect("writing to String cannot fail");
            }
            X86_64MachineSymbol::InternalFunction(_) => {}
        }
        writeln!(self.output, ".type {symbol_text}, @function")
            .expect("writing to String cannot fail");

        let mut function_labels = BTreeSet::new();
        for block in function.blocks() {
            if !label_belongs_to(symbol, block.label()) {
                return Err(assembly_error(
                    X86_64AssemblyErrorKind::ForeignBlockLabel(block.label()),
                    Some(symbol),
                    Some(block.label()),
                    None,
                ));
            }
            let block_label = label(block.label());
            if !function_labels.insert(block_label.clone())
                || !self.labels.insert(block_label.clone())
            {
                return Err(assembly_error(
                    X86_64AssemblyErrorKind::DuplicateLabel(block_label),
                    Some(symbol),
                    Some(block.label()),
                    None,
                ));
            }
            for instruction in block.instructions() {
                let X86_64MachineInstruction::Label { label: inline } = instruction else {
                    continue;
                };
                if !label_belongs_to(symbol, *inline) {
                    return Err(assembly_error(
                        X86_64AssemblyErrorKind::ForeignBlockLabel(*inline),
                        Some(symbol),
                        Some(block.label()),
                        None,
                    ));
                }
                let inline = label(*inline);
                if !function_labels.insert(inline.clone()) || !self.labels.insert(inline.clone()) {
                    return Err(assembly_error(
                        X86_64AssemblyErrorKind::DuplicateLabel(inline),
                        Some(symbol),
                        Some(block.label()),
                        None,
                    ));
                }
            }
        }

        for block in function.blocks() {
            let block_label = label(block.label());
            writeln!(self.output, "{block_label}:").expect("writing to String cannot fail");
            for (index, instruction) in block.instructions().iter().enumerate() {
                if let X86_64MachineInstruction::Jump { target }
                | X86_64MachineInstruction::JumpIf { target, .. } = instruction
                    && !function_labels.contains(&label(*target))
                {
                    return Err(assembly_error(
                        X86_64AssemblyErrorKind::MissingJumpTarget(*target),
                        Some(symbol),
                        Some(block.label()),
                        Some(index),
                    ));
                }
                let emitted = emit_instruction(instruction).map_err(|kind| {
                    assembly_error(kind, Some(symbol), Some(block.label()), Some(index))
                })?;
                writeln!(self.output, "    {emitted}").expect("writing to String cannot fail");
            }
        }
        writeln!(self.output, ".size {symbol_text}, .-{symbol_text}")
            .expect("writing to String cannot fail");
        Ok(())
    }
}

fn validate_call_targets(program: &X86_64MachineProgram) -> Result<(), X86_64AssemblyError> {
    let functions = program
        .functions()
        .iter()
        .chain(program.runtime_functions())
        .chain(std::iter::once(program.executable_entry()))
        .collect::<Vec<_>>();
    let defined = functions
        .iter()
        .map(|function| label(entry_label(function.symbol())))
        .collect::<BTreeSet<_>>();
    for function in functions {
        for block in function.blocks() {
            for (index, instruction) in block.instructions().iter().enumerate() {
                let target = match instruction {
                    X86_64MachineInstruction::CallInternal { function } => {
                        Some(X86_64MachineSymbol::InternalFunction(*function))
                    }
                    X86_64MachineInstruction::CallRuntime { helper } => {
                        Some(X86_64MachineSymbol::RuntimeHelper(*helper))
                    }
                    _ => None,
                };
                if let Some(target) = target
                    && !defined.contains(&label(entry_label(target)))
                {
                    return Err(assembly_error(
                        X86_64AssemblyErrorKind::MissingCallTarget(target),
                        Some(function.symbol()),
                        Some(block.label()),
                        Some(index),
                    ));
                }
            }
        }
    }
    Ok(())
}

fn external_symbols(program: &X86_64MachineProgram) -> Vec<X86_64ExternalSymbol> {
    let mut used = [false; 3];
    for instruction in program
        .functions()
        .iter()
        .chain(program.runtime_functions())
        .chain(std::iter::once(program.executable_entry()))
        .flat_map(|function| function.blocks())
        .flat_map(|block| block.instructions())
    {
        if let X86_64MachineInstruction::CallExternal { symbol } = instruction {
            used[external_symbol_index(*symbol)] = true;
        }
    }
    [
        X86_64ExternalSymbol::AlignedAlloc,
        X86_64ExternalSymbol::Free,
        X86_64ExternalSymbol::Abort,
    ]
    .into_iter()
    .filter(|symbol| used[external_symbol_index(*symbol)])
    .collect()
}

const fn external_symbol_index(symbol: X86_64ExternalSymbol) -> usize {
    match symbol {
        X86_64ExternalSymbol::AlignedAlloc => 0,
        X86_64ExternalSymbol::Free => 1,
        X86_64ExternalSymbol::Abort => 2,
    }
}

fn emit_instruction(
    instruction: &X86_64MachineInstruction,
) -> Result<String, X86_64AssemblyErrorKind> {
    let emitted = match instruction {
        X86_64MachineInstruction::Label { label: inline } => format!("{}:", label(*inline)),
        X86_64MachineInstruction::Push64 { register } => {
            format!("push {}", register_name(*register))
        }
        X86_64MachineInstruction::Move64 {
            destination,
            source,
        } => match (destination, source) {
            (X86_64MachineWrite::Register(destination), X86_64MachineRead::Immediate(value)) => {
                format!("mov {}, 0x{value:016x}", register_name(*destination))
            }
            (X86_64MachineWrite::Register(destination), source) => {
                format!(
                    "mov {}, {}",
                    register_name(*destination),
                    read_operand(*source)
                )
            }
            (X86_64MachineWrite::Memory(destination), X86_64MachineRead::Register(source)) => {
                format!(
                    "mov {}, {}",
                    memory_operand(*destination, true),
                    register_name(*source)
                )
            }
            (X86_64MachineWrite::Memory(_), _) => {
                return Err(X86_64AssemblyErrorKind::IllegalOperandShape(
                    "mov to memory requires a register source",
                ));
            }
        },
        X86_64MachineInstruction::Move8 {
            destination,
            source,
        } => match (destination, source) {
            (
                X86_64MachineByteWrite::Register(destination),
                X86_64MachineByteRead::Register(source),
            ) => format!(
                "mov {}, {}",
                byte_register_name(*destination),
                byte_register_name(*source)
            ),
            (X86_64MachineByteWrite::Register(destination), source) => format!(
                "mov {}, {}",
                byte_register_name(*destination),
                byte_read_operand(*source)
            ),
            (
                X86_64MachineByteWrite::Memory(destination),
                X86_64MachineByteRead::Register(source),
            ) => format!(
                "mov {}, {}",
                byte_memory_operand(*destination),
                byte_register_name(*source)
            ),
            (
                X86_64MachineByteWrite::Memory(destination),
                X86_64MachineByteRead::Immediate(value),
            ) => format!("mov {}, 0x{value:02x}", byte_memory_operand(*destination)),
            (X86_64MachineByteWrite::Memory(_), X86_64MachineByteRead::Memory(_)) => {
                return Err(X86_64AssemblyErrorKind::IllegalOperandShape(
                    "byte mov cannot have two memory operands",
                ));
            }
        },
        X86_64MachineInstruction::LoadEffectiveAddress64 {
            destination,
            source,
        } => format!(
            "lea {}, {}",
            register_name(*destination),
            memory_operand(*source, false)
        ),
        X86_64MachineInstruction::Add64 {
            destination,
            source,
        } => format!(
            "add {}, {}",
            register_name(*destination),
            arithmetic_operand("add", *source)?
        ),
        X86_64MachineInstruction::Multiply64 {
            destination,
            source,
        } => format!(
            "imul {}, {}",
            register_name(*destination),
            arithmetic_operand("imul", *source)?
        ),
        X86_64MachineInstruction::Subtract64 {
            destination,
            source,
        } => format!(
            "sub {}, {}",
            register_name(*destination),
            arithmetic_operand("sub", *source)?
        ),
        X86_64MachineInstruction::And64 {
            destination,
            source,
        } => format!(
            "and {}, {}",
            register_name(*destination),
            arithmetic_operand("and", *source)?
        ),
        X86_64MachineInstruction::Negate64 { register } => {
            format!("neg {}", register_name(*register))
        }
        X86_64MachineInstruction::Compare64 { left, right } => format!(
            "cmp {}, {}",
            register_name(*left),
            arithmetic_operand("cmp", *right)?
        ),
        X86_64MachineInstruction::SetCondition8 {
            condition,
            destination,
        } => format!(
            "{} {}",
            set_condition_mnemonic(*condition),
            byte_register_name(*destination)
        ),
        X86_64MachineInstruction::MoveZeroExtend8To64 {
            destination,
            source,
        } => format!(
            "movzx {}, {}",
            register_name(*destination),
            byte_register_name(*source)
        ),
        X86_64MachineInstruction::SubtractStackPointer { bytes } => {
            let bytes = i32::try_from(*bytes).map_err(|_| {
                X86_64AssemblyErrorKind::ImmediateNotEncodable {
                    instruction: "sub rsp",
                    value: u64::from(*bytes),
                }
            })?;
            format!("sub rsp, {bytes}")
        }
        X86_64MachineInstruction::AddStackPointer { bytes } => {
            let bytes = i32::try_from(*bytes).map_err(|_| {
                X86_64AssemblyErrorKind::ImmediateNotEncodable {
                    instruction: "add rsp",
                    value: u64::from(*bytes),
                }
            })?;
            format!("add rsp, {bytes}")
        }
        X86_64MachineInstruction::CallInternal { function } => {
            format!("call {}", internal_function_label(*function))
        }
        X86_64MachineInstruction::CallRuntime { helper } => {
            format!("call {}", runtime_helper_label(*helper))
        }
        X86_64MachineInstruction::CallExternal { symbol } => {
            format!("call {}@PLT", external_symbol(*symbol))
        }
        X86_64MachineInstruction::Jump { target } => format!("jmp {}", label(*target)),
        X86_64MachineInstruction::JumpIf { condition, target } => {
            format!("{} {}", jump_mnemonic(*condition), label(*target))
        }
        X86_64MachineInstruction::Leave => "leave".to_owned(),
        X86_64MachineInstruction::Return => "ret".to_owned(),
        X86_64MachineInstruction::Trap => "ud2".to_owned(),
    };
    Ok(emitted)
}

fn read_operand(read: X86_64MachineRead) -> String {
    match read {
        X86_64MachineRead::Register(register) => register_name(register).to_owned(),
        X86_64MachineRead::Immediate(value) => format!("0x{value:016x}"),
        X86_64MachineRead::Memory(memory) => memory_operand(memory, true),
    }
}

fn byte_read_operand(read: X86_64MachineByteRead) -> String {
    match read {
        X86_64MachineByteRead::Register(register) => byte_register_name(register).to_owned(),
        X86_64MachineByteRead::Immediate(value) => format!("0x{value:02x}"),
        X86_64MachineByteRead::Memory(memory) => byte_memory_operand(memory),
    }
}

fn byte_memory_operand(memory: X86_64MachineMemory) -> String {
    memory_operand_with_prefix(memory, "BYTE PTR ")
}

fn arithmetic_operand(
    instruction: &'static str,
    read: X86_64MachineRead,
) -> Result<String, X86_64AssemblyErrorKind> {
    match read {
        X86_64MachineRead::Immediate(value) => sign_extended_imm32(value)
            .map(|value| value.to_string())
            .ok_or(X86_64AssemblyErrorKind::ImmediateNotEncodable { instruction, value }),
        other => Ok(read_operand(other)),
    }
}

fn sign_extended_imm32(value: u64) -> Option<i32> {
    if let Ok(value) = i32::try_from(value) {
        return Some(value);
    }
    let candidate = value as i32;
    ((i64::from(candidate) as u64) == value).then_some(candidate)
}

fn memory_operand(memory: X86_64MachineMemory, sized: bool) -> String {
    let prefix = if sized { "QWORD PTR " } else { "" };
    memory_operand_with_prefix(memory, prefix)
}

fn memory_operand_with_prefix(memory: X86_64MachineMemory, prefix: &str) -> String {
    let base = register_name(memory.base());
    match memory.displacement() {
        0 => format!("{prefix}[{base}]"),
        displacement if displacement > 0 => format!("{prefix}[{base} + {displacement}]"),
        displacement => format!("{prefix}[{base} - {}]", -i64::from(displacement)),
    }
}

const fn register_name(register: X86_64IntegerRegister) -> &'static str {
    match register {
        X86_64IntegerRegister::Rax => "rax",
        X86_64IntegerRegister::Rbx => "rbx",
        X86_64IntegerRegister::Rdi => "rdi",
        X86_64IntegerRegister::Rsi => "rsi",
        X86_64IntegerRegister::Rdx => "rdx",
        X86_64IntegerRegister::Rcx => "rcx",
        X86_64IntegerRegister::Rbp => "rbp",
        X86_64IntegerRegister::Rsp => "rsp",
        X86_64IntegerRegister::R8 => "r8",
        X86_64IntegerRegister::R9 => "r9",
        X86_64IntegerRegister::R10 => "r10",
        X86_64IntegerRegister::R11 => "r11",
        X86_64IntegerRegister::R12 => "r12",
        X86_64IntegerRegister::R13 => "r13",
        X86_64IntegerRegister::R14 => "r14",
        X86_64IntegerRegister::R15 => "r15",
    }
}

const fn byte_register_name(register: X86_64ByteRegister) -> &'static str {
    match register {
        X86_64ByteRegister::R10b => "r10b",
    }
}

const fn set_condition_mnemonic(condition: X86_64ConditionCode) -> &'static str {
    match condition {
        X86_64ConditionCode::Equal => "sete",
        X86_64ConditionCode::NotEqual => "setne",
        X86_64ConditionCode::Below => "setb",
        X86_64ConditionCode::BelowOrEqual => "setbe",
        X86_64ConditionCode::Above => "seta",
        X86_64ConditionCode::AboveOrEqual => "setae",
        X86_64ConditionCode::Carry => "setc",
    }
}

const fn jump_mnemonic(condition: X86_64ConditionCode) -> &'static str {
    match condition {
        X86_64ConditionCode::Equal => "je",
        X86_64ConditionCode::NotEqual => "jne",
        X86_64ConditionCode::Below => "jb",
        X86_64ConditionCode::BelowOrEqual => "jbe",
        X86_64ConditionCode::Above => "ja",
        X86_64ConditionCode::AboveOrEqual => "jae",
        X86_64ConditionCode::Carry => "jc",
    }
}

const fn external_symbol(symbol: X86_64ExternalSymbol) -> &'static str {
    match symbol {
        X86_64ExternalSymbol::AlignedAlloc => "aligned_alloc",
        X86_64ExternalSymbol::Free => "free",
        X86_64ExternalSymbol::Abort => "abort",
    }
}

fn entry_label(symbol: X86_64MachineSymbol) -> X86_64MachineLabel {
    match symbol {
        X86_64MachineSymbol::InternalFunction(function) => {
            X86_64MachineLabel::InternalFunction(function)
        }
        X86_64MachineSymbol::RuntimeHelper(helper) => X86_64MachineLabel::RuntimeHelper(helper),
        X86_64MachineSymbol::ExecutableEntry => X86_64MachineLabel::ExecutableEntry,
    }
}

fn label_belongs_to(symbol: X86_64MachineSymbol, candidate: X86_64MachineLabel) -> bool {
    match (symbol, candidate) {
        (
            X86_64MachineSymbol::InternalFunction(expected),
            X86_64MachineLabel::InternalFunction(actual)
            | X86_64MachineLabel::FunctionAbort(actual)
            | X86_64MachineLabel::FunctionEpilogue(actual),
        ) => expected == actual,
        (
            X86_64MachineSymbol::InternalFunction(expected),
            X86_64MachineLabel::VirBlock {
                function: actual, ..
            }
            | X86_64MachineLabel::SyntheticEdge {
                function: actual, ..
            }
            | X86_64MachineLabel::Inline {
                function: actual, ..
            },
        ) => expected == actual,
        (
            X86_64MachineSymbol::RuntimeHelper(expected),
            X86_64MachineLabel::RuntimeHelper(actual) | X86_64MachineLabel::RuntimeFailure(actual),
        ) => expected == actual,
        (X86_64MachineSymbol::ExecutableEntry, X86_64MachineLabel::ExecutableEntry) => true,
        _ => false,
    }
}

fn label(label: X86_64MachineLabel) -> String {
    match label {
        X86_64MachineLabel::InternalFunction(function) => internal_function_label(function),
        X86_64MachineLabel::VirBlock { function, block } => {
            format!(".Lnera_v0_fn_{}_bb_{}", function.get(), block.get())
        }
        X86_64MachineLabel::SyntheticEdge { function, edge } => format!(
            ".Lnera_v0_fn_{}_edge_bb_{}_{}",
            function.get(),
            edge.predecessor().get(),
            match edge.arm() {
                X86_64BranchArm::Then => "then",
                X86_64BranchArm::Else => "else",
            }
        ),
        X86_64MachineLabel::Inline {
            function,
            block,
            instruction,
            ordinal,
        } => format!(
            ".Lnera_v0_fn_{}_bb_{}_instruction_{}_inline_{}",
            function.get(),
            block.get(),
            instruction,
            ordinal
        ),
        X86_64MachineLabel::FunctionAbort(function) => {
            format!(".Lnera_v0_fn_{}_abort", function.get())
        }
        X86_64MachineLabel::FunctionEpilogue(function) => {
            format!(".Lnera_v0_fn_{}_epilogue", function.get())
        }
        X86_64MachineLabel::RuntimeHelper(helper) => runtime_helper_label(helper),
        X86_64MachineLabel::RuntimeFailure(helper) => match helper {
            X86_64RuntimeHelper::AllocOrAbort => ".Lnera_v0_alloc_or_abort_failure".to_owned(),
        },
        X86_64MachineLabel::ExecutableEntry => "main".to_owned(),
    }
}

fn internal_function_label(function: crate::VirFunctionId) -> String {
    format!(".Lnera_v0_fn_{}", function.get())
}

fn runtime_helper_label(helper: X86_64RuntimeHelper) -> String {
    match helper {
        X86_64RuntimeHelper::AllocOrAbort => "_nera_alloc_or_abort".to_owned(),
    }
}

fn assembly_error(
    kind: X86_64AssemblyErrorKind,
    function: Option<X86_64MachineSymbol>,
    block: Option<X86_64MachineLabel>,
    instruction_index: Option<usize>,
) -> X86_64AssemblyError {
    X86_64AssemblyError {
        kind,
        function,
        block,
        instruction_index,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic_immediates_require_sign_extended_imm32() {
        assert_eq!(sign_extended_imm32(0), Some(0));
        assert_eq!(sign_extended_imm32(i32::MAX as u64), Some(i32::MAX));
        assert_eq!(sign_extended_imm32(u64::MAX), Some(-1));
        assert_eq!(sign_extended_imm32(i32::MAX as u64 + 1), None);

        let error = emit_instruction(&X86_64MachineInstruction::Add64 {
            destination: X86_64IntegerRegister::Rax,
            source: X86_64MachineRead::Immediate(i32::MAX as u64 + 1),
        })
        .expect_err("x86 add has no arbitrary imm64 encoding");
        assert_eq!(
            error,
            X86_64AssemblyErrorKind::ImmediateNotEncodable {
                instruction: "add",
                value: i32::MAX as u64 + 1,
            }
        );
    }
}
