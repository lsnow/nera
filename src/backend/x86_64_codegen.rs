use std::error::Error;
use std::fmt;

use crate::{
    ByteSpan, ResolvedRuntimeVirView, VirBasicBlock, VirBlockId, VirConstant, VirFunction,
    VirFunctionId, VirInstruction, VirIntegerPredicate, VirMemorySchema, VirMemoryTypeKind,
    VirTerminator, VirValueId,
};

use super::{
    X86_64AbiError, X86_64AbiParameterLocation, X86_64AbiResultLocation, X86_64BlockPlan,
    X86_64BranchArm, X86_64CallPlan, X86_64EdgeCopyPlacement, X86_64EdgePlan, X86_64EntryAbi,
    X86_64EntryResult, X86_64EnumDiscriminantPlan, X86_64FrameRegion, X86_64FrameSlot,
    X86_64FunctionPlan, X86_64InstructionPlan, X86_64IntegerRegister, X86_64LinuxTarget,
    X86_64ObjectTransferPlan, X86_64ParallelCopy, X86_64PlanningError, X86_64ProgramPlan,
    X86_64ReturnValuePlan, X86_64SyntheticEdgeBlock, X86_64TerminatorPlan,
};

const VALUE_SCRATCH: X86_64IntegerRegister = X86_64IntegerRegister::R10;
const ADDRESS_SCRATCH: X86_64IntegerRegister = X86_64IntegerRegister::R11;

impl X86_64LinuxTarget {
    /// Selects resolved VIR into the stage 4.6.4 structured machine plan.
    pub fn codegen_program(
        self,
        program: &ResolvedRuntimeVirView<'_>,
    ) -> Result<X86_64MachineProgram, X86_64CodegenError> {
        let entry_function = program
            .functions
            .iter()
            .find(|function| function.id == program.entry)
            .ok_or_else(|| {
                program_error(X86_64CodegenErrorKind::InconsistentResolvedProgram(
                    "entry function is absent",
                ))
            })?;
        let entry_abi = self
            .classify_entry(&entry_function.signature)
            .map_err(|error| abi_error(entry_function, error))?;
        let plan = self
            .plan_program(program)
            .map_err(X86_64CodegenError::from_planning)?;

        let functions = program
            .functions
            .iter()
            .map(|function| {
                let function_plan = plan.function(function.id).ok_or_else(|| {
                    function_error(
                        function,
                        X86_64CodegenErrorKind::InconsistentPlanning("function plan is absent"),
                    )
                })?;
                FunctionSelector {
                    function,
                    plan: function_plan,
                    memory: program.memory,
                }
                .lower()
            })
            .collect::<Result<Vec<_>, _>>()?;
        let executable_entry = lower_executable_entry(program.entry, &entry_abi);
        let runtime_functions = super::x86_64_runtime::lower_runtime_helpers(program.as_runtime());

        Ok(X86_64MachineProgram {
            entry: program.entry,
            functions,
            runtime_functions,
            executable_entry,
            planning: plan,
        })
    }
}

/// Structured x86_64 instructions ready for the later assembly emitter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64MachineProgram {
    entry: VirFunctionId,
    functions: Vec<X86_64MachineFunction>,
    runtime_functions: Vec<X86_64MachineFunction>,
    executable_entry: X86_64MachineFunction,
    planning: X86_64ProgramPlan,
}

impl X86_64MachineProgram {
    #[must_use]
    pub const fn entry(&self) -> VirFunctionId {
        self.entry
    }

    #[must_use]
    pub fn functions(&self) -> &[X86_64MachineFunction] {
        &self.functions
    }

    #[must_use]
    pub fn function(&self, id: VirFunctionId) -> Option<&X86_64MachineFunction> {
        self.functions
            .iter()
            .find(|function| function.symbol == X86_64MachineSymbol::InternalFunction(id))
    }

    #[must_use]
    pub fn runtime_functions(&self) -> &[X86_64MachineFunction] {
        &self.runtime_functions
    }

    #[must_use]
    pub fn runtime_helper(&self, helper: X86_64RuntimeHelper) -> Option<&X86_64MachineFunction> {
        self.runtime_functions
            .iter()
            .find(|function| function.symbol == X86_64MachineSymbol::RuntimeHelper(helper))
    }

    #[must_use]
    pub const fn executable_entry(&self) -> &X86_64MachineFunction {
        &self.executable_entry
    }

    #[must_use]
    pub const fn planning(&self) -> &X86_64ProgramPlan {
        &self.planning
    }
}

/// One internal Nera function, backend runtime helper, or `main` wrapper.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64MachineFunction {
    pub(super) symbol: X86_64MachineSymbol,
    pub(super) blocks: Vec<X86_64MachineBlock>,
}

impl X86_64MachineFunction {
    #[must_use]
    pub const fn symbol(&self) -> X86_64MachineSymbol {
        self.symbol
    }

    #[must_use]
    pub fn blocks(&self) -> &[X86_64MachineBlock] {
        &self.blocks
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64MachineSymbol {
    InternalFunction(VirFunctionId),
    RuntimeHelper(X86_64RuntimeHelper),
    ExecutableEntry,
}

/// Backend-private functions emitted once when required by the program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64RuntimeHelper {
    AllocOrAbort,
}

/// libc functions referenced by the backend rather than by source-level calls.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64ExternalSymbol {
    AlignedAlloc,
    Free,
    Abort,
}

/// One explicit-label machine block; there is no implicit fallthrough.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64MachineBlock {
    pub(super) label: X86_64MachineLabel,
    pub(super) instructions: Vec<X86_64MachineInstruction>,
}

impl X86_64MachineBlock {
    #[must_use]
    pub const fn label(&self) -> X86_64MachineLabel {
        self.label
    }

    #[must_use]
    pub fn instructions(&self) -> &[X86_64MachineInstruction] {
        &self.instructions
    }
}

/// Labels remain structured until the GNU assembly emitter chooses spelling.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64MachineLabel {
    InternalFunction(VirFunctionId),
    VirBlock {
        function: VirFunctionId,
        block: VirBlockId,
    },
    SyntheticEdge {
        function: VirFunctionId,
        edge: X86_64SyntheticEdgeBlock,
    },
    Inline {
        function: VirFunctionId,
        block: VirBlockId,
        instruction: usize,
        ordinal: usize,
    },
    FunctionAbort(VirFunctionId),
    FunctionEpilogue(VirFunctionId),
    RuntimeHelper(X86_64RuntimeHelper),
    RuntimeFailure(X86_64RuntimeHelper),
    ExecutableEntry,
}

/// One legal 64-bit addressing mode used by native v0.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64MachineMemory {
    base: X86_64IntegerRegister,
    displacement: i32,
}

impl X86_64MachineMemory {
    #[must_use]
    pub const fn base(self) -> X86_64IntegerRegister {
        self.base
    }

    #[must_use]
    pub const fn displacement(self) -> i32 {
        self.displacement
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64MachineRead {
    Register(X86_64IntegerRegister),
    Immediate(u64),
    Memory(X86_64MachineMemory),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64MachineWrite {
    Register(X86_64IntegerRegister),
    Memory(X86_64MachineMemory),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64MachineByteRead {
    Register(X86_64ByteRegister),
    Immediate(u8),
    Memory(X86_64MachineMemory),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64MachineByteWrite {
    Register(X86_64ByteRegister),
    Memory(X86_64MachineMemory),
}

/// Byte registers needed for materializing normalized comparison results.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64ByteRegister {
    R10b,
}

/// x86 condition codes used by comparisons, branches and arithmetic checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64ConditionCode {
    Equal,
    NotEqual,
    Below,
    BelowOrEqual,
    Above,
    AboveOrEqual,
    Carry,
}

/// Restricted actual-instruction vocabulary consumed by stage 4.6.5.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum X86_64MachineInstruction {
    Label {
        label: X86_64MachineLabel,
    },
    Push64 {
        register: X86_64IntegerRegister,
    },
    Move64 {
        destination: X86_64MachineWrite,
        source: X86_64MachineRead,
    },
    Move8 {
        destination: X86_64MachineByteWrite,
        source: X86_64MachineByteRead,
    },
    LoadEffectiveAddress64 {
        destination: X86_64IntegerRegister,
        source: X86_64MachineMemory,
    },
    Add64 {
        destination: X86_64IntegerRegister,
        source: X86_64MachineRead,
    },
    Multiply64 {
        destination: X86_64IntegerRegister,
        source: X86_64MachineRead,
    },
    Subtract64 {
        destination: X86_64IntegerRegister,
        source: X86_64MachineRead,
    },
    And64 {
        destination: X86_64IntegerRegister,
        source: X86_64MachineRead,
    },
    Negate64 {
        register: X86_64IntegerRegister,
    },
    Compare64 {
        left: X86_64IntegerRegister,
        right: X86_64MachineRead,
    },
    SetCondition8 {
        condition: X86_64ConditionCode,
        destination: X86_64ByteRegister,
    },
    MoveZeroExtend8To64 {
        destination: X86_64IntegerRegister,
        source: X86_64ByteRegister,
    },
    SubtractStackPointer {
        bytes: u32,
    },
    AddStackPointer {
        bytes: u32,
    },
    CallInternal {
        function: VirFunctionId,
    },
    CallRuntime {
        helper: X86_64RuntimeHelper,
    },
    CallExternal {
        symbol: X86_64ExternalSymbol,
    },
    Jump {
        target: X86_64MachineLabel,
    },
    JumpIf {
        condition: X86_64ConditionCode,
        target: X86_64MachineLabel,
    },
    Leave,
    Return,
    Trap,
}

/// Source-localized native instruction-selection failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64CodegenError {
    kind: X86_64CodegenErrorKind,
    function: Option<VirFunctionId>,
    block: Option<VirBlockId>,
    instruction_index: Option<usize>,
    source_span: Option<ByteSpan>,
}

impl X86_64CodegenError {
    #[must_use]
    pub const fn kind(&self) -> &X86_64CodegenErrorKind {
        &self.kind
    }

    #[must_use]
    pub const fn function(&self) -> Option<VirFunctionId> {
        self.function
    }

    #[must_use]
    pub const fn block(&self) -> Option<VirBlockId> {
        self.block
    }

    #[must_use]
    pub const fn instruction_index(&self) -> Option<usize> {
        self.instruction_index
    }

    #[must_use]
    pub const fn source_span(&self) -> Option<ByteSpan> {
        self.source_span
    }

    #[must_use]
    pub fn capability_failure_kind(&self) -> Option<crate::CapabilityFailureKind> {
        match &self.kind {
            X86_64CodegenErrorKind::Planning(error) => error.capability_failure_kind(),
            X86_64CodegenErrorKind::EntryAbi(_)
            | X86_64CodegenErrorKind::AddressDisplacementOutOfRange { .. }
            | X86_64CodegenErrorKind::StackAdjustmentOutOfRange { .. } => {
                Some(crate::CapabilityFailureKind::TargetUnsupported)
            }
            X86_64CodegenErrorKind::MissingRuntimeValueSlot(_)
            | X86_64CodegenErrorKind::InconsistentResolvedProgram(_)
            | X86_64CodegenErrorKind::InconsistentPlanning(_) => None,
        }
    }

    fn from_planning(error: X86_64PlanningError) -> Self {
        Self {
            function: Some(error.function()),
            block: error.block(),
            instruction_index: error.instruction_index(),
            source_span: Some(error.source_span()),
            kind: X86_64CodegenErrorKind::Planning(Box::new(error)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum X86_64CodegenErrorKind {
    Planning(Box<X86_64PlanningError>),
    EntryAbi(X86_64AbiError),
    AddressDisplacementOutOfRange { value: i128 },
    StackAdjustmentOutOfRange { bytes: u64 },
    MissingRuntimeValueSlot(VirValueId),
    InconsistentResolvedProgram(&'static str),
    InconsistentPlanning(&'static str),
}

impl fmt::Display for X86_64CodegenError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("x86_64 codegen failed")?;
        if let Some(function) = self.function {
            write!(formatter, " in fn{}", function.get())?;
        }
        if let Some(block) = self.block {
            write!(formatter, "/bb{}", block.get())?;
        }
        if let Some(index) = self.instruction_index {
            write!(formatter, "/instruction {index}")?;
        }
        formatter.write_str(": ")?;
        match &self.kind {
            X86_64CodegenErrorKind::Planning(error) => error.fmt(formatter),
            X86_64CodegenErrorKind::EntryAbi(error) => error.fmt(formatter),
            X86_64CodegenErrorKind::AddressDisplacementOutOfRange { value } => {
                write!(formatter, "address displacement {value} does not fit i32")
            }
            X86_64CodegenErrorKind::StackAdjustmentOutOfRange { bytes } => write!(
                formatter,
                "stack adjustment {bytes} cannot be encoded as a sign-extended imm32"
            ),
            X86_64CodegenErrorKind::MissingRuntimeValueSlot(value) => {
                write!(
                    formatter,
                    "runtime value %{} has no frame slot",
                    value.get()
                )
            }
            X86_64CodegenErrorKind::InconsistentResolvedProgram(context) => {
                write!(
                    formatter,
                    "resolved program invariant was not preserved: {context}"
                )
            }
            X86_64CodegenErrorKind::InconsistentPlanning(context) => {
                write!(
                    formatter,
                    "native planning invariant was not preserved: {context}"
                )
            }
        }
    }
}

impl Error for X86_64CodegenError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            X86_64CodegenErrorKind::Planning(error) => Some(error.as_ref()),
            X86_64CodegenErrorKind::EntryAbi(error) => Some(error),
            _ => None,
        }
    }
}

struct FunctionSelector<'a> {
    function: &'a VirFunction,
    plan: &'a X86_64FunctionPlan,
    memory: &'a VirMemorySchema,
}

impl FunctionSelector<'_> {
    fn lower(&self) -> Result<X86_64MachineFunction, X86_64CodegenError> {
        let mut blocks = vec![self.lower_prologue()?];
        for block in &self.function.blocks {
            let block_plan = self.plan.block(block.id).ok_or_else(|| {
                block_error(
                    self.function,
                    block,
                    block.source_span,
                    X86_64CodegenErrorKind::InconsistentPlanning("block plan is absent"),
                )
            })?;
            let (lowered, synthetic) = self.lower_block(block, block_plan)?;
            blocks.push(lowered);
            blocks.extend(synthetic);
        }
        if self.function.blocks.iter().any(|block| {
            block
                .instructions
                .iter()
                .any(|instruction| matches!(&instruction.instruction, VirInstruction::Check { .. }))
        }) {
            blocks.push(X86_64MachineBlock {
                label: function_abort_label(self.function.id),
                instructions: vec![
                    X86_64MachineInstruction::CallExternal {
                        symbol: X86_64ExternalSymbol::Abort,
                    },
                    X86_64MachineInstruction::Trap,
                ],
            });
        }
        blocks.push(X86_64MachineBlock {
            label: epilogue_label(self.function.id),
            instructions: vec![
                X86_64MachineInstruction::Leave,
                X86_64MachineInstruction::Return,
            ],
        });
        Ok(X86_64MachineFunction {
            symbol: X86_64MachineSymbol::InternalFunction(self.function.id),
            blocks,
        })
    }

    fn lower_prologue(&self) -> Result<X86_64MachineBlock, X86_64CodegenError> {
        let mut instructions = vec![
            X86_64MachineInstruction::Push64 {
                register: X86_64IntegerRegister::Rbp,
            },
            move_register(X86_64IntegerRegister::Rbp, X86_64IntegerRegister::Rsp),
        ];
        if self.plan.frame().size_bytes() != 0 {
            instructions.push(X86_64MachineInstruction::SubtractStackPointer {
                bytes: stack_adjustment(
                    self.function,
                    None,
                    None,
                    self.function.source_span,
                    self.plan.frame().size_bytes(),
                )?,
            });
        }

        match (
            self.plan.signature().result_buffer(),
            self.plan.frame().hidden_result_buffer_pointer(),
        ) {
            (Some(buffer), Some(slot)) => instructions.push(move_to_frame(
                slot,
                X86_64MachineRead::Register(buffer.pointer_register()),
            )),
            (None, None) => {}
            _ => {
                return Err(function_error(
                    self.function,
                    X86_64CodegenErrorKind::InconsistentPlanning(
                        "hidden result-buffer spill disagrees with the ABI",
                    ),
                ));
            }
        }

        for parameter in self.plan.incoming_parameters() {
            match parameter.source() {
                X86_64AbiParameterLocation::Register(register) => {
                    instructions.push(move_to_frame(
                        parameter.destination(),
                        X86_64MachineRead::Register(register),
                    ));
                }
                X86_64AbiParameterLocation::CallerStack(location) => {
                    let displacement = displacement_from_u64(
                        self.function,
                        None,
                        None,
                        self.function.source_span,
                        location.offset_from_callee_frame_pointer_bytes(),
                    )?;
                    instructions.push(move_from_memory(
                        VALUE_SCRATCH,
                        memory(X86_64IntegerRegister::Rbp, displacement),
                    ));
                    instructions.push(move_to_frame(
                        parameter.destination(),
                        X86_64MachineRead::Register(VALUE_SCRATCH),
                    ));
                }
            }
        }
        instructions.push(X86_64MachineInstruction::Jump {
            target: block_label(self.function.id, self.function.entry),
        });
        Ok(X86_64MachineBlock {
            label: X86_64MachineLabel::InternalFunction(self.function.id),
            instructions,
        })
    }

    fn lower_block(
        &self,
        block: &VirBasicBlock,
        block_plan: &X86_64BlockPlan,
    ) -> Result<(X86_64MachineBlock, Vec<X86_64MachineBlock>), X86_64CodegenError> {
        if block.instructions.len() != block_plan.instructions().len() {
            return Err(block_error(
                self.function,
                block,
                block.source_span,
                X86_64CodegenErrorKind::InconsistentPlanning(
                    "instruction-plan cardinality changed",
                ),
            ));
        }
        let mut instructions = Vec::new();
        for (index, (spanned, instruction_plan)) in block
            .instructions
            .iter()
            .zip(block_plan.instructions())
            .enumerate()
        {
            self.lower_instruction(
                block,
                index,
                spanned.source_span,
                &spanned.instruction,
                instruction_plan,
                &mut instructions,
            )?;
        }
        let synthetic = self.lower_terminator(block, block_plan.terminator(), &mut instructions)?;
        Ok((
            X86_64MachineBlock {
                label: block_label(self.function.id, block.id),
                instructions,
            },
            synthetic,
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_instruction(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        instruction: &VirInstruction,
        plan: &X86_64InstructionPlan,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        match (instruction, plan) {
            (
                VirInstruction::LoanBegin {
                    effect,
                    reference_result,
                    ..
                }
                | VirInstruction::LoanAliasShared {
                    effect,
                    reference_result,
                    ..
                }
                | VirInstruction::LoanReborrow {
                    effect,
                    reference_result,
                    ..
                },
                X86_64InstructionPlan::LoanReference,
            ) => {
                output.push(move_from_frame(
                    VALUE_SCRATCH,
                    self.value_slot(block, instruction_index, source_span, effect.source_pointer)?,
                ));
                output.push(move_to_frame(
                    self.value_slot(block, instruction_index, source_span, reference_result.id)?,
                    X86_64MachineRead::Register(VALUE_SCRATCH),
                ));
                Ok(())
            }
            (
                VirInstruction::LoanAliasAuthority {
                    effect,
                    reference_result,
                    ..
                }
                | VirInstruction::LoanReborrowAuthority {
                    effect,
                    reference_result,
                    ..
                },
                X86_64InstructionPlan::LoanReference,
            ) => {
                output.push(move_from_frame(
                    VALUE_SCRATCH,
                    self.value_slot(block, instruction_index, source_span, effect.source_pointer)?,
                ));
                output.push(move_to_frame(
                    self.value_slot(block, instruction_index, source_span, reference_result.id)?,
                    X86_64MachineRead::Register(VALUE_SCRATCH),
                ));
                Ok(())
            }
            (
                VirInstruction::LoanEnd { .. } | VirInstruction::LoanEndAuthority { .. },
                X86_64InstructionPlan::ErasedLoan,
            ) => Ok(()),
            (
                VirInstruction::PermissionSplit { .. }
                | VirInstruction::PermissionJoin { .. }
                | VirInstruction::PermissionMove { .. },
                X86_64InstructionPlan::ErasedPermission,
            ) => Ok(()),
            (
                VirInstruction::ObjectDeinitialize { .. } | VirInstruction::StorageReset { .. },
                X86_64InstructionPlan::ErasedObjectState,
            ) => Ok(()),
            (VirInstruction::Call { .. }, X86_64InstructionPlan::Call(call_plan)) => {
                self.lower_call(block, instruction_index, source_span, call_plan, output)
            }
            (
                VirInstruction::ResourceStorageReset { pointer, .. },
                X86_64InstructionPlan::ResourceStorageReset(offsets),
            ) => self.clear_resource_slots(
                block,
                instruction_index,
                source_span,
                *pointer,
                offsets.iter().copied(),
                output,
            ),
            (
                VirInstruction::LocalStorage {
                    pointer_result,
                    access,
                    ..
                },
                X86_64InstructionPlan::LocalStorage(region),
            ) => {
                output.push(X86_64MachineInstruction::LoadEffectiveAddress64 {
                    destination: VALUE_SCRATCH,
                    source: region_address(
                        *region,
                        0,
                        self.function,
                        block,
                        instruction_index,
                        source_span,
                    )?,
                });
                output.push(move_to_frame(
                    self.value_slot(block, instruction_index, source_span, pointer_result.id)?,
                    X86_64MachineRead::Register(VALUE_SCRATCH),
                ));
                let shape = self.memory.object_shape(*access).map_err(|_| {
                    instruction_error(
                        self.function,
                        block,
                        instruction_index,
                        source_span,
                        X86_64CodegenErrorKind::InconsistentPlanning(
                            "local resource shape is invalid",
                        ),
                    )
                })?;
                if shape.supports_resource_storage_reset() {
                    self.clear_resource_slots(
                        block,
                        instruction_index,
                        source_span,
                        pointer_result.id,
                        shape
                            .resource_leaves()
                            .iter()
                            .map(|leaf| leaf.bytes().start_bytes()),
                        output,
                    )?;
                }
                Ok(())
            }
            (
                VirInstruction::ObjectTransfer {
                    destination,
                    source,
                    ..
                },
                X86_64InstructionPlan::ObjectTransfer(transfer),
            ) => self.lower_object_transfer(
                block,
                instruction_index,
                source_span,
                *destination,
                *source,
                transfer,
                output,
            ),
            (
                VirInstruction::EnumSetDiscriminant { pointer, .. },
                X86_64InstructionPlan::EnumDiscriminant(discriminant),
            ) => self.lower_enum_discriminant(
                block,
                instruction_index,
                source_span,
                *pointer,
                discriminant,
                output,
            ),
            (VirInstruction::Constant { result, value }, X86_64InstructionPlan::Runtime) => {
                let value = match value {
                    VirConstant::U64(value) => *value,
                    VirConstant::Bool(value) => u64::from(*value),
                };
                output.push(X86_64MachineInstruction::Move64 {
                    destination: X86_64MachineWrite::Register(VALUE_SCRATCH),
                    source: X86_64MachineRead::Immediate(value),
                });
                output.push(move_to_frame(
                    self.value_slot(block, instruction_index, source_span, result.id)?,
                    X86_64MachineRead::Register(VALUE_SCRATCH),
                ));
                Ok(())
            }
            (
                VirInstruction::WordAdd {
                    result,
                    left,
                    right,
                },
                X86_64InstructionPlan::Runtime,
            ) => {
                output.push(move_from_frame(
                    VALUE_SCRATCH,
                    self.value_slot(block, instruction_index, source_span, *left)?,
                ));
                output.push(X86_64MachineInstruction::Add64 {
                    destination: VALUE_SCRATCH,
                    source: read_frame(self.value_slot(
                        block,
                        instruction_index,
                        source_span,
                        *right,
                    )?),
                });
                output.push(move_to_frame(
                    self.value_slot(block, instruction_index, source_span, result.id)?,
                    X86_64MachineRead::Register(VALUE_SCRATCH),
                ));
                Ok(())
            }
            (
                VirInstruction::PointerDistance { result, begin, end },
                X86_64InstructionPlan::Runtime,
            ) => {
                output.push(move_from_frame(
                    VALUE_SCRATCH,
                    self.value_slot(block, instruction_index, source_span, *end)?,
                ));
                output.push(X86_64MachineInstruction::Subtract64 {
                    destination: VALUE_SCRATCH,
                    source: read_frame(self.value_slot(
                        block,
                        instruction_index,
                        source_span,
                        *begin,
                    )?),
                });
                output.push(move_to_frame(
                    self.value_slot(block, instruction_index, source_span, result.id)?,
                    X86_64MachineRead::Register(VALUE_SCRATCH),
                ));
                Ok(())
            }
            (
                VirInstruction::PointerCompare {
                    result,
                    predicate,
                    left,
                    right,
                }
                | VirInstruction::Compare {
                    result,
                    predicate,
                    left,
                    right,
                },
                X86_64InstructionPlan::Runtime,
            ) => {
                output.push(move_from_frame(
                    VALUE_SCRATCH,
                    self.value_slot(block, instruction_index, source_span, *left)?,
                ));
                output.push(X86_64MachineInstruction::Compare64 {
                    left: VALUE_SCRATCH,
                    right: read_frame(self.value_slot(
                        block,
                        instruction_index,
                        source_span,
                        *right,
                    )?),
                });
                output.push(X86_64MachineInstruction::SetCondition8 {
                    condition: comparison_condition(*predicate),
                    destination: X86_64ByteRegister::R10b,
                });
                output.push(X86_64MachineInstruction::MoveZeroExtend8To64 {
                    destination: VALUE_SCRATCH,
                    source: X86_64ByteRegister::R10b,
                });
                output.push(move_to_frame(
                    self.value_slot(block, instruction_index, source_span, result.id)?,
                    X86_64MachineRead::Register(VALUE_SCRATCH),
                ));
                Ok(())
            }
            (
                VirInstruction::Allocate {
                    pointer_result,
                    size_bytes,
                    alignment,
                    ..
                },
                allocation_plan @ (X86_64InstructionPlan::Runtime
                | X86_64InstructionPlan::HeapStorage { .. }),
            ) => {
                self.lower_allocate(
                    block,
                    instruction_index,
                    source_span,
                    pointer_result.id,
                    *size_bytes,
                    *alignment,
                    output,
                )?;
                if let X86_64InstructionPlan::HeapStorage {
                    empty_resource_offsets,
                    cleanup_tag,
                } = allocation_plan
                {
                    self.clear_resource_slots(
                        block,
                        instruction_index,
                        source_span,
                        pointer_result.id,
                        empty_resource_offsets.iter().copied(),
                        output,
                    )?;
                    if let Some(tag) = cleanup_tag {
                        // A valid physical cleanup tag with all payload slots
                        // empty is not a semantic constructor or default T.
                        self.lower_enum_discriminant(
                            block,
                            instruction_index,
                            source_span,
                            pointer_result.id,
                            tag,
                            output,
                        )?;
                    }
                }
                Ok(())
            }
            (
                VirInstruction::Initialize {
                    pointer,
                    value,
                    access,
                    ..
                }
                | VirInstruction::Write {
                    pointer,
                    value,
                    access,
                    ..
                }
                | VirInstruction::Store {
                    pointer,
                    value,
                    access,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_memory_write(
                block,
                instruction_index,
                source_span,
                *pointer,
                *value,
                *access,
                output,
            ),
            (
                VirInstruction::ResourceInitialize {
                    destination,
                    value,
                    access,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_memory_write(
                block,
                instruction_index,
                source_span,
                *destination,
                *value,
                *access,
                output,
            ),
            (
                VirInstruction::ResourceTake {
                    pointer_result,
                    source,
                    access,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_resource_take(
                block,
                instruction_index,
                source_span,
                pointer_result.id,
                *source,
                *access,
                output,
            ),
            (
                VirInstruction::Load {
                    result,
                    pointer,
                    access,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_load(
                block,
                instruction_index,
                source_span,
                result.id,
                *pointer,
                *access,
                output,
            ),
            (
                VirInstruction::EnumDiscriminant {
                    result,
                    pointer,
                    access,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_enum_discriminant_read(
                block,
                instruction_index,
                source_span,
                result.id,
                *pointer,
                *access,
                output,
            ),
            (VirInstruction::RawAddress { result, base, .. }, X86_64InstructionPlan::Runtime) => {
                output.push(move_from_frame(
                    VALUE_SCRATCH,
                    self.value_slot(block, instruction_index, source_span, *base)?,
                ));
                output.push(move_to_frame(
                    self.value_slot(block, instruction_index, source_span, result.id)?,
                    X86_64MachineRead::Register(VALUE_SCRATCH),
                ));
                Ok(())
            }
            (
                VirInstruction::PointerOffset {
                    result,
                    base,
                    delta_bytes,
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_pointer_offset(
                block,
                instruction_index,
                source_span,
                result.id,
                *base,
                *delta_bytes,
                output,
            ),
            (
                VirInstruction::FieldAddress {
                    result,
                    base,
                    offset_bytes,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_field_address(
                block,
                instruction_index,
                source_span,
                result.id,
                *base,
                *offset_bytes,
                output,
            ),
            (
                VirInstruction::TupleElementAddress {
                    result,
                    base,
                    offset_bytes,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_field_address(
                block,
                instruction_index,
                source_span,
                result.id,
                *base,
                *offset_bytes,
                output,
            ),
            (
                VirInstruction::ObjectLeafAddress {
                    result,
                    base,
                    offset_bytes,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_field_address(
                block,
                instruction_index,
                source_span,
                result.id,
                *base,
                *offset_bytes,
                output,
            ),
            (
                VirInstruction::IndexAddress {
                    result,
                    base,
                    index,
                    stride_bytes,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_index_address(
                block,
                instruction_index,
                source_span,
                result.id,
                *base,
                *index,
                *stride_bytes,
                output,
            ),
            (
                VirInstruction::SliceRange {
                    pointer_result,
                    length_result,
                    base,
                    start,
                    end,
                    stride_bytes,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_slice_range(
                block,
                instruction_index,
                source_span,
                pointer_result.id,
                length_result.id,
                *base,
                *start,
                *end,
                *stride_bytes,
                output,
            ),
            (
                VirInstruction::SliceAddress {
                    pointer_result,
                    length_result,
                    base,
                    start,
                    end,
                    stride_bytes,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_slice_range(
                block,
                instruction_index,
                source_span,
                pointer_result.id,
                length_result.id,
                *base,
                *start,
                *end,
                *stride_bytes,
                output,
            ),
            (VirInstruction::Free { pointer, .. }, X86_64InstructionPlan::Runtime) => {
                self.lower_free(block, instruction_index, source_span, *pointer, output)
            }
            (
                VirInstruction::DropOwn {
                    pointer, condition, ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_conditional_free(
                block,
                instruction_index,
                source_span,
                *pointer,
                *condition,
                output,
            ),
            (
                VirInstruction::ObjectDrop {
                    pointer,
                    access,
                    condition,
                    ..
                },
                X86_64InstructionPlan::Runtime,
            ) => self.lower_object_drop(
                block,
                instruction_index,
                source_span,
                *pointer,
                *access,
                *condition,
                output,
            ),
            (VirInstruction::Check { condition }, X86_64InstructionPlan::Runtime) => {
                self.lower_assert(block, instruction_index, source_span, *condition, output)
            }
            _ => Err(instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64CodegenErrorKind::InconsistentPlanning(
                    "instruction classification disagrees with VIR",
                ),
            )),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_allocate(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        pointer_result: VirValueId,
        size_bytes: VirValueId,
        alignment: u64,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        if alignment == 0 || !alignment.is_power_of_two() {
            return Err(instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64CodegenErrorKind::InconsistentResolvedProgram(
                    "allocation alignment is not a nonzero power of two",
                ),
            ));
        }
        output.push(move_from_frame(
            X86_64IntegerRegister::Rdi,
            self.value_slot(block, instruction_index, source_span, size_bytes)?,
        ));
        output.push(X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Register(X86_64IntegerRegister::Rsi),
            source: X86_64MachineRead::Immediate(alignment.max(8)),
        });
        output.push(X86_64MachineInstruction::CallRuntime {
            helper: X86_64RuntimeHelper::AllocOrAbort,
        });
        output.push(move_to_frame(
            self.value_slot(block, instruction_index, source_span, pointer_result)?,
            X86_64MachineRead::Register(X86_64IntegerRegister::Rax),
        ));
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_memory_write(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        pointer: VirValueId,
        value: VirValueId,
        access: crate::VirMemoryAccess,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        output.push(move_from_frame(
            ADDRESS_SCRATCH,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        output.push(move_from_frame(
            VALUE_SCRATCH,
            self.value_slot(block, instruction_index, source_span, value)?,
        ));
        if matches!(self.memory.kind(access.ty), Some(VirMemoryTypeKind::Bool)) {
            output.push(X86_64MachineInstruction::Move8 {
                destination: X86_64MachineByteWrite::Memory(memory(ADDRESS_SCRATCH, 0)),
                source: X86_64MachineByteRead::Register(X86_64ByteRegister::R10b),
            });
        } else {
            output.push(X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Memory(memory(ADDRESS_SCRATCH, 0)),
                source: X86_64MachineRead::Register(VALUE_SCRATCH),
            });
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_object_transfer(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        destination: VirValueId,
        source: VirValueId,
        transfer: &X86_64ObjectTransferPlan,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        const DESTINATION: X86_64IntegerRegister = X86_64IntegerRegister::Rax;
        const SOURCE: X86_64IntegerRegister = X86_64IntegerRegister::R11;
        output.push(move_from_frame(
            DESTINATION,
            self.value_slot(block, instruction_index, source_span, destination)?,
        ));
        output.push(move_from_frame(
            SOURCE,
            self.value_slot(block, instruction_index, source_span, source)?,
        ));

        let word_bytes = transfer.size_bytes() / 8 * 8;
        for offset in (0..word_bytes).step_by(8) {
            let displacement =
                object_displacement(offset, self.function, block, instruction_index, source_span)?;
            output.push(move_from_memory(
                VALUE_SCRATCH,
                memory(SOURCE, displacement),
            ));
            output.push(X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Memory(memory(DESTINATION, displacement)),
                source: X86_64MachineRead::Register(VALUE_SCRATCH),
            });
        }
        for offset in word_bytes..transfer.size_bytes() {
            let displacement =
                object_displacement(offset, self.function, block, instruction_index, source_span)?;
            output.push(X86_64MachineInstruction::Move8 {
                destination: X86_64MachineByteWrite::Register(X86_64ByteRegister::R10b),
                source: X86_64MachineByteRead::Memory(memory(SOURCE, displacement)),
            });
            output.push(X86_64MachineInstruction::Move8 {
                destination: X86_64MachineByteWrite::Memory(memory(DESTINATION, displacement)),
                source: X86_64MachineByteRead::Register(X86_64ByteRegister::R10b),
            });
        }
        // Verified Move requires disjoint objects. Retire only resource slots,
        // after the complete copy, so later partial cleanup cannot free stale
        // owner bits. Copy leaves the source intact (shared aliases).
        self.clear_resource_slots(
            block,
            instruction_index,
            source_span,
            source,
            transfer.retired_source_offsets().iter().copied(),
            output,
        )
    }

    /// One physical empty-slot representation for fresh storage, declaration
    /// reset and resource Move. It never initializes ordinary value bytes.
    #[allow(clippy::too_many_arguments)]
    fn clear_resource_slots(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        pointer: VirValueId,
        offsets: impl Iterator<Item = u64>,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        let mut offsets = offsets.peekable();
        if offsets.peek().is_none() {
            return Ok(());
        }
        output.push(move_from_frame(
            ADDRESS_SCRATCH,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        output.push(X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Register(VALUE_SCRATCH),
            source: X86_64MachineRead::Immediate(0),
        });
        for offset in offsets {
            let displacement =
                object_displacement(offset, self.function, block, instruction_index, source_span)?;
            output.push(X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Memory(memory(ADDRESS_SCRATCH, displacement)),
                source: X86_64MachineRead::Register(VALUE_SCRATCH),
            });
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_enum_discriminant(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        pointer: VirValueId,
        discriminant: &X86_64EnumDiscriminantPlan,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        self.clear_resource_slots(
            block,
            instruction_index,
            source_span,
            pointer,
            discriminant.empty_resource_offsets().iter().copied(),
            output,
        )?;
        output.push(move_from_frame(
            ADDRESS_SCRATCH,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        for index in 0..discriminant.size_bytes() {
            let offset = discriminant
                .offset_bytes()
                .checked_add(index)
                .ok_or_else(|| {
                    instruction_error(
                        self.function,
                        block,
                        instruction_index,
                        source_span,
                        X86_64CodegenErrorKind::InconsistentPlanning("enum tag offset overflowed"),
                    )
                })?;
            let displacement =
                object_displacement(offset, self.function, block, instruction_index, source_span)?;
            let byte = if index < 8 {
                ((discriminant.discriminant() >> (index * 8)) & 0xff) as u8
            } else {
                0
            };
            output.push(X86_64MachineInstruction::Move8 {
                destination: X86_64MachineByteWrite::Memory(memory(ADDRESS_SCRATCH, displacement)),
                source: X86_64MachineByteRead::Immediate(byte),
            });
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_load(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        result: VirValueId,
        pointer: VirValueId,
        access: crate::VirMemoryAccess,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        output.push(move_from_frame(
            ADDRESS_SCRATCH,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        if matches!(self.memory.kind(access.ty), Some(VirMemoryTypeKind::Bool)) {
            output.push(X86_64MachineInstruction::Move8 {
                destination: X86_64MachineByteWrite::Register(X86_64ByteRegister::R10b),
                source: X86_64MachineByteRead::Memory(memory(ADDRESS_SCRATCH, 0)),
            });
            output.push(X86_64MachineInstruction::MoveZeroExtend8To64 {
                destination: VALUE_SCRATCH,
                source: X86_64ByteRegister::R10b,
            });
        } else {
            output.push(move_from_memory(VALUE_SCRATCH, memory(ADDRESS_SCRATCH, 0)));
        }
        output.push(move_to_frame(
            self.value_slot(block, instruction_index, source_span, result)?,
            X86_64MachineRead::Register(VALUE_SCRATCH),
        ));
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_resource_take(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        result: VirValueId,
        pointer: VirValueId,
        access: crate::VirMemoryAccess,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        self.lower_load(
            block,
            instruction_index,
            source_span,
            result,
            pointer,
            access,
            output,
        )?;
        output.push(move_from_frame(
            ADDRESS_SCRATCH,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        output.push(X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Register(VALUE_SCRATCH),
            source: X86_64MachineRead::Immediate(0),
        });
        output.push(X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Memory(memory(ADDRESS_SCRATCH, 0)),
            source: X86_64MachineRead::Register(VALUE_SCRATCH),
        });
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_object_drop(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        pointer: VirValueId,
        access: crate::VirMemoryAccess,
        condition: VirValueId,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        let shape = self.memory.object_shape(access).map_err(|_| {
            instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64CodegenErrorKind::InconsistentPlanning("object drop shape is invalid"),
            )
        })?;
        if shape
            .resource_leaves()
            .iter()
            .any(|leaf| leaf.kind() == crate::VirPointerKind::Raw)
        {
            return Err(instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64CodegenErrorKind::InconsistentPlanning("object drop shape is unsupported"),
            ));
        }
        let inline_label = |ordinal| X86_64MachineLabel::Inline {
            function: self.function.id,
            block: block.id,
            instruction: instruction_index,
            ordinal,
        };
        let end = inline_label(0);
        output.push(move_from_frame(
            VALUE_SCRATCH,
            self.value_slot(block, instruction_index, source_span, condition)?,
        ));
        output.push(X86_64MachineInstruction::Compare64 {
            left: VALUE_SCRATCH,
            right: X86_64MachineRead::Immediate(0),
        });
        output.push(X86_64MachineInstruction::JumpIf {
            condition: X86_64ConditionCode::Equal,
            target: end,
        });

        if shape.variants().is_empty() {
            for leaf in shape
                .resource_leaves()
                .iter()
                .filter(|leaf| leaf.kind() == crate::VirPointerKind::Own)
            {
                self.lower_object_drop_leaf(
                    block,
                    instruction_index,
                    source_span,
                    pointer,
                    leaf.bytes().start_bytes(),
                    output,
                )?;
            }
            output.push(X86_64MachineInstruction::Label { label: end });
            return Ok(());
        }

        let tag = shape
            .variants()
            .first()
            .ok_or_else(|| {
                instruction_error(
                    self.function,
                    block,
                    instruction_index,
                    source_span,
                    X86_64CodegenErrorKind::InconsistentPlanning(
                        "object drop enum has no variants",
                    ),
                )
            })?
            .tag();
        let tag_displacement = object_displacement(
            tag.start_bytes(),
            self.function,
            block,
            instruction_index,
            source_span,
        )?;
        output.push(move_from_frame(
            ADDRESS_SCRATCH,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        output.push(X86_64MachineInstruction::Move8 {
            destination: X86_64MachineByteWrite::Register(X86_64ByteRegister::R10b),
            source: X86_64MachineByteRead::Memory(memory(ADDRESS_SCRATCH, tag_displacement)),
        });
        output.push(X86_64MachineInstruction::MoveZeroExtend8To64 {
            destination: VALUE_SCRATCH,
            source: X86_64ByteRegister::R10b,
        });
        for (index, case) in shape.variants().iter().enumerate() {
            output.push(X86_64MachineInstruction::Compare64 {
                left: VALUE_SCRATCH,
                right: X86_64MachineRead::Immediate(case.discriminant()),
            });
            output.push(X86_64MachineInstruction::JumpIf {
                condition: X86_64ConditionCode::Equal,
                target: inline_label(index + 1),
            });
        }
        output.push(X86_64MachineInstruction::Trap);
        for (index, case) in shape.variants().iter().enumerate() {
            output.push(X86_64MachineInstruction::Label {
                label: inline_label(index + 1),
            });
            for leaf in case.leaves().iter().filter(|leaf| {
                matches!(
                    self.memory.kind(leaf.access().ty),
                    Some(crate::VirMemoryTypeKind::Pointer {
                        kind: crate::VirPointerKind::Own,
                        ..
                    })
                )
            }) {
                self.lower_object_drop_leaf(
                    block,
                    instruction_index,
                    source_span,
                    pointer,
                    leaf.bytes().start_bytes(),
                    output,
                )?;
            }
            output.push(X86_64MachineInstruction::Jump { target: end });
        }
        output.push(X86_64MachineInstruction::Label { label: end });
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_object_drop_leaf(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        pointer: VirValueId,
        offset_bytes: u64,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        let displacement = object_displacement(
            offset_bytes,
            self.function,
            block,
            instruction_index,
            source_span,
        )?;
        output.push(move_from_frame(
            ADDRESS_SCRATCH,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        output.push(move_from_memory(
            X86_64IntegerRegister::Rdi,
            memory(ADDRESS_SCRATCH, displacement),
        ));
        output.push(X86_64MachineInstruction::CallExternal {
            symbol: X86_64ExternalSymbol::Free,
        });
        output.push(move_from_frame(
            ADDRESS_SCRATCH,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        output.push(X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Register(VALUE_SCRATCH),
            source: X86_64MachineRead::Immediate(0),
        });
        output.push(X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Memory(memory(ADDRESS_SCRATCH, displacement)),
            source: X86_64MachineRead::Register(VALUE_SCRATCH),
        });
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_conditional_free(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        pointer: VirValueId,
        condition: VirValueId,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        let end = X86_64MachineLabel::Inline {
            function: self.function.id,
            block: block.id,
            instruction: instruction_index,
            ordinal: 0,
        };
        output.push(move_from_frame(
            VALUE_SCRATCH,
            self.value_slot(block, instruction_index, source_span, condition)?,
        ));
        output.push(X86_64MachineInstruction::Compare64 {
            left: VALUE_SCRATCH,
            right: X86_64MachineRead::Immediate(0),
        });
        output.push(X86_64MachineInstruction::JumpIf {
            condition: X86_64ConditionCode::Equal,
            target: end,
        });
        output.push(move_from_frame(
            X86_64IntegerRegister::Rdi,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        output.push(X86_64MachineInstruction::CallExternal {
            symbol: X86_64ExternalSymbol::Free,
        });
        output.push(X86_64MachineInstruction::Label { label: end });
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_enum_discriminant_read(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        result: VirValueId,
        pointer: VirValueId,
        access: crate::VirMemoryAccess,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        let shape = self.memory.object_shape(access).map_err(|_| {
            instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64CodegenErrorKind::InconsistentPlanning(
                    "enum discriminant read shape is invalid",
                ),
            )
        })?;
        let case = shape
            .variants()
            .iter()
            .find(|case| case.path().segments().is_empty())
            .ok_or_else(|| {
                instruction_error(
                    self.function,
                    block,
                    instruction_index,
                    source_span,
                    X86_64CodegenErrorKind::InconsistentPlanning(
                        "enum discriminant read has no root case",
                    ),
                )
            })?;
        let displacement = object_displacement(
            case.tag().start_bytes(),
            self.function,
            block,
            instruction_index,
            source_span,
        )?;
        output.push(move_from_frame(
            ADDRESS_SCRATCH,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        output.push(X86_64MachineInstruction::Move8 {
            destination: X86_64MachineByteWrite::Register(X86_64ByteRegister::R10b),
            source: X86_64MachineByteRead::Memory(memory(ADDRESS_SCRATCH, displacement)),
        });
        output.push(X86_64MachineInstruction::MoveZeroExtend8To64 {
            destination: VALUE_SCRATCH,
            source: X86_64ByteRegister::R10b,
        });
        output.push(move_to_frame(
            self.value_slot(block, instruction_index, source_span, result)?,
            X86_64MachineRead::Register(VALUE_SCRATCH),
        ));
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_pointer_offset(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        result: VirValueId,
        base: VirValueId,
        delta_bytes: VirValueId,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        output.push(move_from_frame(
            VALUE_SCRATCH,
            self.value_slot(block, instruction_index, source_span, base)?,
        ));
        output.push(X86_64MachineInstruction::Add64 {
            destination: VALUE_SCRATCH,
            source: read_frame(self.value_slot(
                block,
                instruction_index,
                source_span,
                delta_bytes,
            )?),
        });
        output.push(move_to_frame(
            self.value_slot(block, instruction_index, source_span, result)?,
            X86_64MachineRead::Register(VALUE_SCRATCH),
        ));
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_field_address(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        result: VirValueId,
        base: VirValueId,
        offset_bytes: u64,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        output.push(move_from_frame(
            VALUE_SCRATCH,
            self.value_slot(block, instruction_index, source_span, base)?,
        ));
        if offset_bytes != 0 {
            output.push(X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Register(ADDRESS_SCRATCH),
                source: X86_64MachineRead::Immediate(offset_bytes),
            });
            output.push(X86_64MachineInstruction::Add64 {
                destination: VALUE_SCRATCH,
                source: X86_64MachineRead::Register(ADDRESS_SCRATCH),
            });
        }
        output.push(move_to_frame(
            self.value_slot(block, instruction_index, source_span, result)?,
            X86_64MachineRead::Register(VALUE_SCRATCH),
        ));
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_index_address(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        result: VirValueId,
        base: VirValueId,
        index: VirValueId,
        stride_bytes: u64,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        output.push(move_from_frame(
            VALUE_SCRATCH,
            self.value_slot(block, instruction_index, source_span, index)?,
        ));
        if stride_bytes != 1 {
            output.push(X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Register(ADDRESS_SCRATCH),
                source: X86_64MachineRead::Immediate(stride_bytes),
            });
            output.push(X86_64MachineInstruction::Multiply64 {
                destination: VALUE_SCRATCH,
                source: X86_64MachineRead::Register(ADDRESS_SCRATCH),
            });
        }
        output.push(X86_64MachineInstruction::Add64 {
            destination: VALUE_SCRATCH,
            source: read_frame(self.value_slot(block, instruction_index, source_span, base)?),
        });
        output.push(move_to_frame(
            self.value_slot(block, instruction_index, source_span, result)?,
            X86_64MachineRead::Register(VALUE_SCRATCH),
        ));
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_slice_range(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        pointer_result: VirValueId,
        length_result: VirValueId,
        base: VirValueId,
        start: VirValueId,
        end: VirValueId,
        stride_bytes: u64,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        output.push(move_from_frame(
            VALUE_SCRATCH,
            self.value_slot(block, instruction_index, source_span, start)?,
        ));
        if stride_bytes != 1 {
            output.push(X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Register(ADDRESS_SCRATCH),
                source: X86_64MachineRead::Immediate(stride_bytes),
            });
            output.push(X86_64MachineInstruction::Multiply64 {
                destination: VALUE_SCRATCH,
                source: X86_64MachineRead::Register(ADDRESS_SCRATCH),
            });
        }
        output.push(X86_64MachineInstruction::Add64 {
            destination: VALUE_SCRATCH,
            source: read_frame(self.value_slot(block, instruction_index, source_span, base)?),
        });
        output.push(move_to_frame(
            self.value_slot(block, instruction_index, source_span, pointer_result)?,
            X86_64MachineRead::Register(VALUE_SCRATCH),
        ));

        output.push(move_from_frame(
            VALUE_SCRATCH,
            self.value_slot(block, instruction_index, source_span, end)?,
        ));
        output.push(X86_64MachineInstruction::Subtract64 {
            destination: VALUE_SCRATCH,
            source: read_frame(self.value_slot(block, instruction_index, source_span, start)?),
        });
        output.push(move_to_frame(
            self.value_slot(block, instruction_index, source_span, length_result)?,
            X86_64MachineRead::Register(VALUE_SCRATCH),
        ));
        Ok(())
    }

    fn lower_free(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        pointer: VirValueId,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        output.push(move_from_frame(
            X86_64IntegerRegister::Rdi,
            self.value_slot(block, instruction_index, source_span, pointer)?,
        ));
        output.push(X86_64MachineInstruction::CallExternal {
            symbol: X86_64ExternalSymbol::Free,
        });
        Ok(())
    }

    fn lower_assert(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        condition: VirValueId,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        output.push(move_from_frame(
            VALUE_SCRATCH,
            self.value_slot(block, instruction_index, source_span, condition)?,
        ));
        output.push(X86_64MachineInstruction::Compare64 {
            left: VALUE_SCRATCH,
            right: X86_64MachineRead::Immediate(0),
        });
        output.push(X86_64MachineInstruction::JumpIf {
            condition: X86_64ConditionCode::Equal,
            target: function_abort_label(self.function.id),
        });
        Ok(())
    }

    fn lower_call(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        call: &X86_64CallPlan,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        let outgoing_size = call.signature().outgoing_stack_size_bytes();
        if call.signature().caller_stack_cleanup_bytes() != outgoing_size {
            return Err(instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64CodegenErrorKind::InconsistentPlanning(
                    "call stack allocation and cleanup disagree",
                ),
            ));
        }
        if outgoing_size != 0 {
            output.push(X86_64MachineInstruction::SubtractStackPointer {
                bytes: stack_adjustment(
                    self.function,
                    Some(block),
                    Some(instruction_index),
                    source_span,
                    outgoing_size,
                )?,
            });
        }
        match (
            call.signature().result_buffer(),
            call.indirect_result_area(),
        ) {
            (Some(buffer), Some(area)) => {
                output.push(X86_64MachineInstruction::LoadEffectiveAddress64 {
                    destination: buffer.pointer_register(),
                    source: region_memory(
                        area,
                        0,
                        self.function,
                        block,
                        instruction_index,
                        source_span,
                    )?,
                });
            }
            (None, None) => {}
            _ => {
                return Err(instruction_error(
                    self.function,
                    block,
                    instruction_index,
                    source_span,
                    X86_64CodegenErrorKind::InconsistentPlanning(
                        "call result buffer disagrees with its ABI",
                    ),
                ));
            }
        }
        for argument in call.arguments() {
            let source =
                self.value_slot(block, instruction_index, source_span, argument.value())?;
            match argument.location() {
                X86_64AbiParameterLocation::Register(register) => {
                    output.push(move_from_frame(register, source));
                }
                X86_64AbiParameterLocation::CallerStack(location) => {
                    output.push(move_from_frame(VALUE_SCRATCH, source));
                    let displacement = displacement_from_u64(
                        self.function,
                        Some(block),
                        Some(instruction_index),
                        source_span,
                        location.offset_from_call_site_rsp_bytes(),
                    )?;
                    output.push(X86_64MachineInstruction::Move64 {
                        destination: X86_64MachineWrite::Memory(memory(
                            X86_64IntegerRegister::Rsp,
                            displacement,
                        )),
                        source: X86_64MachineRead::Register(VALUE_SCRATCH),
                    });
                }
            }
        }
        output.push(X86_64MachineInstruction::CallInternal {
            function: call.callee(),
        });
        if outgoing_size != 0 {
            output.push(X86_64MachineInstruction::AddStackPointer {
                bytes: stack_adjustment(
                    self.function,
                    Some(block),
                    Some(instruction_index),
                    source_span,
                    call.signature().caller_stack_cleanup_bytes(),
                )?,
            });
        }
        for result in call.results() {
            match result.location() {
                X86_64AbiResultLocation::Register(register) => output.push(move_to_frame(
                    result.destination(),
                    X86_64MachineRead::Register(register),
                )),
                X86_64AbiResultLocation::ResultBuffer { offset_bytes } => {
                    let area = call.indirect_result_area().ok_or_else(|| {
                        instruction_error(
                            self.function,
                            block,
                            instruction_index,
                            source_span,
                            X86_64CodegenErrorKind::InconsistentPlanning(
                                "indirect call result area is absent",
                            ),
                        )
                    })?;
                    output.push(move_from_memory(
                        VALUE_SCRATCH,
                        region_memory(
                            area,
                            offset_bytes,
                            self.function,
                            block,
                            instruction_index,
                            source_span,
                        )?,
                    ));
                    output.push(move_to_frame(
                        result.destination(),
                        X86_64MachineRead::Register(VALUE_SCRATCH),
                    ));
                }
            }
        }
        Ok(())
    }

    fn lower_terminator(
        &self,
        block: &VirBasicBlock,
        plan: &X86_64TerminatorPlan,
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<Vec<X86_64MachineBlock>, X86_64CodegenError> {
        match (&block.terminator.terminator, plan) {
            (VirTerminator::Jump { .. }, X86_64TerminatorPlan::Jump { edge }) => {
                match edge.placement() {
                    X86_64EdgeCopyPlacement::Direct => {
                        self.require_empty_edge(block, edge)?;
                    }
                    X86_64EdgeCopyPlacement::InlineBeforeJump => {
                        lower_parallel_copy(edge.copies(), output);
                    }
                    X86_64EdgeCopyPlacement::SplitBlock(_) => {
                        return Err(self.terminator_error(
                            block,
                            X86_64CodegenErrorKind::InconsistentPlanning(
                                "jump edge cannot use a split block",
                            ),
                        ));
                    }
                }
                output.push(X86_64MachineInstruction::Jump {
                    target: block_label(self.function.id, edge.target()),
                });
                Ok(Vec::new())
            }
            (
                VirTerminator::Branch { condition, .. },
                X86_64TerminatorPlan::Branch {
                    then_edge,
                    else_edge,
                },
            ) => {
                let (then_target, then_block) =
                    self.lower_branch_edge(block, then_edge, X86_64BranchArm::Then)?;
                let (else_target, else_block) =
                    self.lower_branch_edge(block, else_edge, X86_64BranchArm::Else)?;
                output.push(move_from_frame(
                    VALUE_SCRATCH,
                    self.terminator_value_slot(block, *condition)?,
                ));
                output.push(X86_64MachineInstruction::Compare64 {
                    left: VALUE_SCRATCH,
                    right: X86_64MachineRead::Immediate(0),
                });
                output.push(X86_64MachineInstruction::JumpIf {
                    condition: X86_64ConditionCode::NotEqual,
                    target: then_target,
                });
                output.push(X86_64MachineInstruction::Jump {
                    target: else_target,
                });
                Ok([then_block, else_block].into_iter().flatten().collect())
            }
            (VirTerminator::Return { .. }, X86_64TerminatorPlan::Return { values }) => {
                self.lower_return(block, values, output)?;
                Ok(Vec::new())
            }
            _ => Err(self.terminator_error(
                block,
                X86_64CodegenErrorKind::InconsistentPlanning("terminator plan disagrees with VIR"),
            )),
        }
    }

    fn lower_branch_edge(
        &self,
        block: &VirBasicBlock,
        edge: &X86_64EdgePlan,
        expected_arm: X86_64BranchArm,
    ) -> Result<(X86_64MachineLabel, Option<X86_64MachineBlock>), X86_64CodegenError> {
        match edge.placement() {
            X86_64EdgeCopyPlacement::Direct => {
                self.require_empty_edge(block, edge)?;
                Ok((block_label(self.function.id, edge.target()), None))
            }
            X86_64EdgeCopyPlacement::SplitBlock(synthetic) => {
                if synthetic.predecessor() != block.id || synthetic.arm() != expected_arm {
                    return Err(self.terminator_error(
                        block,
                        X86_64CodegenErrorKind::InconsistentPlanning(
                            "synthetic edge identity disagrees with its branch",
                        ),
                    ));
                }
                let label = synthetic_label(self.function.id, synthetic);
                let mut instructions = Vec::new();
                lower_parallel_copy(edge.copies(), &mut instructions);
                instructions.push(X86_64MachineInstruction::Jump {
                    target: block_label(self.function.id, edge.target()),
                });
                Ok((
                    label,
                    Some(X86_64MachineBlock {
                        label,
                        instructions,
                    }),
                ))
            }
            X86_64EdgeCopyPlacement::InlineBeforeJump => Err(self.terminator_error(
                block,
                X86_64CodegenErrorKind::InconsistentPlanning(
                    "branch edge cannot execute copies before the branch",
                ),
            )),
        }
    }

    fn lower_return(
        &self,
        block: &VirBasicBlock,
        values: &[X86_64ReturnValuePlan],
        output: &mut Vec<X86_64MachineInstruction>,
    ) -> Result<(), X86_64CodegenError> {
        let uses_result_buffer = values.iter().any(|value| {
            matches!(
                value.destination(),
                X86_64AbiResultLocation::ResultBuffer { .. }
            )
        });
        let result_buffer = if uses_result_buffer {
            let result_buffer = self.plan.signature().result_buffer().ok_or_else(|| {
                self.terminator_error(
                    block,
                    X86_64CodegenErrorKind::InconsistentPlanning(
                        "return destinations need an absent ABI result buffer",
                    ),
                )
            })?;
            let pointer_slot = self
                .plan
                .frame()
                .hidden_result_buffer_pointer()
                .ok_or_else(|| {
                    self.terminator_error(
                        block,
                        X86_64CodegenErrorKind::InconsistentPlanning(
                            "return needs an absent hidden result-buffer pointer",
                        ),
                    )
                })?;
            output.push(move_from_frame(ADDRESS_SCRATCH, pointer_slot));
            Some(result_buffer)
        } else {
            None
        };
        for value in values {
            let source = self.terminator_value_slot(block, value.value())?;
            match value.destination() {
                X86_64AbiResultLocation::Register(register) => {
                    output.push(move_from_frame(register, source));
                }
                X86_64AbiResultLocation::ResultBuffer { offset_bytes } => {
                    let buffer = result_buffer.ok_or_else(|| {
                        self.terminator_error(
                            block,
                            X86_64CodegenErrorKind::InconsistentPlanning(
                                "indirect return has no ABI result buffer",
                            ),
                        )
                    })?;
                    let end = offset_bytes.checked_add(8).ok_or_else(|| {
                        self.terminator_error(
                            block,
                            X86_64CodegenErrorKind::InconsistentPlanning(
                                "return result-buffer offset overflows",
                            ),
                        )
                    })?;
                    if end > buffer.size_bytes() {
                        return Err(self.terminator_error(
                            block,
                            X86_64CodegenErrorKind::InconsistentPlanning(
                                "return result exceeds its ABI result buffer",
                            ),
                        ));
                    }
                    output.push(move_from_frame(VALUE_SCRATCH, source));
                    output.push(X86_64MachineInstruction::Move64 {
                        destination: X86_64MachineWrite::Memory(memory(
                            ADDRESS_SCRATCH,
                            displacement_from_u64(
                                self.function,
                                Some(block),
                                None,
                                block.terminator.source_span,
                                offset_bytes,
                            )?,
                        )),
                        source: X86_64MachineRead::Register(VALUE_SCRATCH),
                    });
                }
            }
        }
        output.push(X86_64MachineInstruction::Jump {
            target: epilogue_label(self.function.id),
        });
        Ok(())
    }

    fn require_empty_edge(
        &self,
        block: &VirBasicBlock,
        edge: &X86_64EdgePlan,
    ) -> Result<(), X86_64CodegenError> {
        if edge.copies().is_empty() {
            Ok(())
        } else {
            Err(self.terminator_error(
                block,
                X86_64CodegenErrorKind::InconsistentPlanning(
                    "direct edge unexpectedly contains copies",
                ),
            ))
        }
    }

    fn value_slot(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        value: VirValueId,
    ) -> Result<X86_64FrameSlot, X86_64CodegenError> {
        self.plan.frame().value_slot(value).ok_or_else(|| {
            instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64CodegenErrorKind::MissingRuntimeValueSlot(value),
            )
        })
    }

    fn terminator_value_slot(
        &self,
        block: &VirBasicBlock,
        value: VirValueId,
    ) -> Result<X86_64FrameSlot, X86_64CodegenError> {
        self.plan.frame().value_slot(value).ok_or_else(|| {
            self.terminator_error(
                block,
                X86_64CodegenErrorKind::MissingRuntimeValueSlot(value),
            )
        })
    }

    fn terminator_error(
        &self,
        block: &VirBasicBlock,
        kind: X86_64CodegenErrorKind,
    ) -> X86_64CodegenError {
        block_error(self.function, block, block.terminator.source_span, kind)
    }
}

fn lower_executable_entry(entry: VirFunctionId, abi: &X86_64EntryAbi) -> X86_64MachineFunction {
    let mut instructions = vec![
        X86_64MachineInstruction::Push64 {
            register: X86_64IntegerRegister::Rbp,
        },
        move_register(X86_64IntegerRegister::Rbp, X86_64IntegerRegister::Rsp),
        X86_64MachineInstruction::CallInternal { function: entry },
    ];
    if abi.result() == X86_64EntryResult::Unit {
        instructions.push(X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Register(X86_64IntegerRegister::Rax),
            source: X86_64MachineRead::Immediate(0),
        });
    }
    instructions.extend([
        X86_64MachineInstruction::Leave,
        X86_64MachineInstruction::Return,
    ]);
    X86_64MachineFunction {
        symbol: X86_64MachineSymbol::ExecutableEntry,
        blocks: vec![X86_64MachineBlock {
            label: X86_64MachineLabel::ExecutableEntry,
            instructions,
        }],
    }
}

fn lower_parallel_copy(copies: &[X86_64ParallelCopy], output: &mut Vec<X86_64MachineInstruction>) {
    for copy in copies {
        output.push(move_from_frame(VALUE_SCRATCH, copy.source()));
        output.push(move_to_frame(
            copy.temporary(),
            X86_64MachineRead::Register(VALUE_SCRATCH),
        ));
    }
    for copy in copies {
        output.push(move_from_frame(VALUE_SCRATCH, copy.temporary()));
        output.push(move_to_frame(
            copy.destination(),
            X86_64MachineRead::Register(VALUE_SCRATCH),
        ));
    }
}

fn object_displacement(
    offset_bytes: u64,
    function: &VirFunction,
    block: &VirBasicBlock,
    instruction_index: usize,
    source_span: ByteSpan,
) -> Result<i32, X86_64CodegenError> {
    i32::try_from(offset_bytes).map_err(|_| {
        instruction_error(
            function,
            block,
            instruction_index,
            source_span,
            X86_64CodegenErrorKind::InconsistentPlanning(
                "object effect displacement is not encodable",
            ),
        )
    })
}

const fn comparison_condition(predicate: VirIntegerPredicate) -> X86_64ConditionCode {
    match predicate {
        VirIntegerPredicate::Equal => X86_64ConditionCode::Equal,
        VirIntegerPredicate::NotEqual => X86_64ConditionCode::NotEqual,
        VirIntegerPredicate::LessThan => X86_64ConditionCode::Below,
        VirIntegerPredicate::LessOrEqual => X86_64ConditionCode::BelowOrEqual,
        VirIntegerPredicate::GreaterThan => X86_64ConditionCode::Above,
        VirIntegerPredicate::GreaterOrEqual => X86_64ConditionCode::AboveOrEqual,
    }
}

const fn memory(base: X86_64IntegerRegister, displacement: i32) -> X86_64MachineMemory {
    X86_64MachineMemory { base, displacement }
}

const fn frame_memory(slot: X86_64FrameSlot) -> X86_64MachineMemory {
    memory(X86_64IntegerRegister::Rbp, slot.offset_from_rbp_bytes())
}

const fn read_frame(slot: X86_64FrameSlot) -> X86_64MachineRead {
    X86_64MachineRead::Memory(frame_memory(slot))
}

const fn move_from_frame(
    destination: X86_64IntegerRegister,
    slot: X86_64FrameSlot,
) -> X86_64MachineInstruction {
    move_from_memory(destination, frame_memory(slot))
}

const fn move_from_memory(
    destination: X86_64IntegerRegister,
    source: X86_64MachineMemory,
) -> X86_64MachineInstruction {
    X86_64MachineInstruction::Move64 {
        destination: X86_64MachineWrite::Register(destination),
        source: X86_64MachineRead::Memory(source),
    }
}

const fn move_to_frame(
    destination: X86_64FrameSlot,
    source: X86_64MachineRead,
) -> X86_64MachineInstruction {
    X86_64MachineInstruction::Move64 {
        destination: X86_64MachineWrite::Memory(frame_memory(destination)),
        source,
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

const fn block_label(function: VirFunctionId, block: VirBlockId) -> X86_64MachineLabel {
    X86_64MachineLabel::VirBlock { function, block }
}

const fn synthetic_label(
    function: VirFunctionId,
    edge: X86_64SyntheticEdgeBlock,
) -> X86_64MachineLabel {
    X86_64MachineLabel::SyntheticEdge { function, edge }
}

const fn epilogue_label(function: VirFunctionId) -> X86_64MachineLabel {
    X86_64MachineLabel::FunctionEpilogue(function)
}

const fn function_abort_label(function: VirFunctionId) -> X86_64MachineLabel {
    X86_64MachineLabel::FunctionAbort(function)
}

fn region_memory(
    region: X86_64FrameRegion,
    offset_bytes: u64,
    function: &VirFunction,
    block: &VirBasicBlock,
    instruction_index: usize,
    source_span: ByteSpan,
) -> Result<X86_64MachineMemory, X86_64CodegenError> {
    let end = offset_bytes.checked_add(8).ok_or_else(|| {
        instruction_error(
            function,
            block,
            instruction_index,
            source_span,
            X86_64CodegenErrorKind::InconsistentPlanning("indirect result offset overflows"),
        )
    })?;
    if end > region.size_bytes() {
        return Err(instruction_error(
            function,
            block,
            instruction_index,
            source_span,
            X86_64CodegenErrorKind::InconsistentPlanning(
                "indirect result offset exceeds its frame area",
            ),
        ));
    }
    region_address(
        region,
        offset_bytes,
        function,
        block,
        instruction_index,
        source_span,
    )
}

fn region_address(
    region: X86_64FrameRegion,
    offset_bytes: u64,
    function: &VirFunction,
    block: &VirBasicBlock,
    instruction_index: usize,
    source_span: ByteSpan,
) -> Result<X86_64MachineMemory, X86_64CodegenError> {
    if offset_bytes > region.size_bytes() {
        return Err(instruction_error(
            function,
            block,
            instruction_index,
            source_span,
            X86_64CodegenErrorKind::InconsistentPlanning("frame-region address exceeds its area"),
        ));
    }
    let displacement = i128::from(region.base_offset_from_rbp_bytes()) + i128::from(offset_bytes);
    let displacement = i32::try_from(displacement).map_err(|_| {
        instruction_error(
            function,
            block,
            instruction_index,
            source_span,
            X86_64CodegenErrorKind::AddressDisplacementOutOfRange {
                value: displacement,
            },
        )
    })?;
    Ok(memory(X86_64IntegerRegister::Rbp, displacement))
}

fn stack_adjustment(
    function: &VirFunction,
    block: Option<&VirBasicBlock>,
    instruction_index: Option<usize>,
    source_span: ByteSpan,
    bytes: u64,
) -> Result<u32, X86_64CodegenError> {
    i32::try_from(bytes).map(|bytes| bytes as u32).map_err(|_| {
        contextual_error(
            function,
            block,
            instruction_index,
            source_span,
            X86_64CodegenErrorKind::StackAdjustmentOutOfRange { bytes },
        )
    })
}

fn displacement_from_u64(
    function: &VirFunction,
    block: Option<&VirBasicBlock>,
    instruction_index: Option<usize>,
    source_span: ByteSpan,
    value: u64,
) -> Result<i32, X86_64CodegenError> {
    i32::try_from(value).map_err(|_| {
        contextual_error(
            function,
            block,
            instruction_index,
            source_span,
            X86_64CodegenErrorKind::AddressDisplacementOutOfRange {
                value: i128::from(value),
            },
        )
    })
}

fn program_error(kind: X86_64CodegenErrorKind) -> X86_64CodegenError {
    X86_64CodegenError {
        kind,
        function: None,
        block: None,
        instruction_index: None,
        source_span: None,
    }
}

fn abi_error(function: &VirFunction, error: X86_64AbiError) -> X86_64CodegenError {
    function_error(function, X86_64CodegenErrorKind::EntryAbi(error))
}

fn function_error(function: &VirFunction, kind: X86_64CodegenErrorKind) -> X86_64CodegenError {
    contextual_error(function, None, None, function.source_span, kind)
}

fn block_error(
    function: &VirFunction,
    block: &VirBasicBlock,
    source_span: ByteSpan,
    kind: X86_64CodegenErrorKind,
) -> X86_64CodegenError {
    contextual_error(function, Some(block), None, source_span, kind)
}

fn instruction_error(
    function: &VirFunction,
    block: &VirBasicBlock,
    instruction_index: usize,
    source_span: ByteSpan,
    kind: X86_64CodegenErrorKind,
) -> X86_64CodegenError {
    contextual_error(
        function,
        Some(block),
        Some(instruction_index),
        source_span,
        kind,
    )
}

fn contextual_error(
    function: &VirFunction,
    block: Option<&VirBasicBlock>,
    instruction_index: Option<usize>,
    source_span: ByteSpan,
    kind: X86_64CodegenErrorKind,
) -> X86_64CodegenError {
    X86_64CodegenError {
        kind,
        function: Some(function.id),
        block: block.map(|block| block.id),
        instruction_index,
        source_span: Some(source_span),
    }
}
