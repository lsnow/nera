//! Native target, ABI and lowering plans shared by machine-code backends.
//!
//! Stage 4.6.1 freezes the x86_64 Linux target and classifies VIR signatures.
//! Stage 4.6.2 adds deterministic ghost erasure, frame layout and CFG edge
//! planning. Stage 4.6.3 selects scalar operations, explicit CFG and local
//! calls into a structured machine plan. Stage 4.6.4 adds memory operations
//! and the minimal libc runtime boundary. Stage 4.6.5 emits GNU assembly and
//! invokes the system assembler and C linker driver without a shell. Stage
//! 6.5.6 adds bounded pointer-free object copy and enum-tag lowering without
//! expanding the libc trust boundary. Stage 6.5.7 adds canonical tuple-address
//! selection and byte-width bool memory operations for aggregate HIR output.

mod x86_64_codegen;
mod x86_64_emit;
mod x86_64_linux;
mod x86_64_plan;
mod x86_64_runtime;
mod x86_64_tools;

pub use x86_64_codegen::{
    X86_64ByteRegister, X86_64CodegenError, X86_64CodegenErrorKind, X86_64ConditionCode,
    X86_64ExternalSymbol, X86_64MachineBlock, X86_64MachineByteRead, X86_64MachineByteWrite,
    X86_64MachineFunction, X86_64MachineInstruction, X86_64MachineLabel, X86_64MachineMemory,
    X86_64MachineProgram, X86_64MachineRead, X86_64MachineSymbol, X86_64MachineWrite,
    X86_64RuntimeHelper,
};
pub use x86_64_emit::{X86_64AssemblyError, X86_64AssemblyErrorKind};

pub use x86_64_linux::{
    GnuAssemblySyntax, NativeEndianness, NativeObjectFormat, NativeTargetError,
    X86_64_UNKNOWN_LINUX_GNU, X86_64AbiComponent, X86_64AbiError, X86_64AbiErrorKind,
    X86_64AbiParameter, X86_64AbiParameterLocation, X86_64AbiResult, X86_64AbiResultLocation,
    X86_64CallerStackLocation, X86_64EntryAbi, X86_64EntryResult, X86_64IntegerRegister,
    X86_64IsaBaseline, X86_64LinuxTarget, X86_64ResultBuffer, X86_64RuntimeSignature,
    X86_64RuntimeType,
};
pub use x86_64_plan::{
    X86_64_INLINE_OBJECT_COPY_MAX_BYTES, X86_64BlockPlan, X86_64BranchArm, X86_64CallArgumentPlan,
    X86_64CallPlan, X86_64CallResultPlan, X86_64EdgeCopyPlacement, X86_64EdgePlan,
    X86_64EnumDiscriminantPlan, X86_64FramePlan, X86_64FrameRegion, X86_64FrameSlot,
    X86_64FunctionPlan, X86_64IncomingParameterPlan, X86_64InstructionPlan,
    X86_64ObjectTransferPlan, X86_64ParallelCopy, X86_64PlanningError, X86_64PlanningErrorKind,
    X86_64ProgramPlan, X86_64ReturnValuePlan, X86_64SyntheticEdgeBlock, X86_64TerminatorPlan,
};
pub use x86_64_tools::{
    X86_64SystemToolchain, X86_64ToolError, X86_64ToolErrorKind, X86_64ToolOperation,
    X86_64ToolStage,
};
