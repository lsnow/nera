use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

use crate::{
    ByteSpan, ResolvedRuntimeVirView, VirBasicBlock, VirBlockId, VirBlockTarget, VirEndianness,
    VirFunction, VirFunctionId, VirInstruction, VirMemoryAccess, VirMemorySchema, VirTerminator,
    VirType, VirValue, VirValueId,
};

use super::{
    X86_64AbiError, X86_64AbiParameterLocation, X86_64AbiResultLocation, X86_64LinuxTarget,
    X86_64RuntimeSignature, X86_64RuntimeType,
};

const WORD_BYTES: u64 = 8;
const MAX_FRAME_SIZE_BYTES: u64 = 2_147_483_632;
const MAX_OUTGOING_STACK_SIZE_BYTES: u64 = MAX_FRAME_SIZE_BYTES;
/// Maximum fixed object copied inline by native v0. Larger objects remain a
/// fail-closed backend boundary until a private copy helper is specified.
pub const X86_64_INLINE_OBJECT_COPY_MAX_BYTES: u64 = 4096;

impl X86_64LinuxTarget {
    /// Largest fixed frame representable by the v0 prologue and rbp-relative
    /// addressing discipline. The value is the largest 16-byte multiple below
    /// `i32::MAX`.
    #[must_use]
    pub const fn maximum_frame_size_bytes(self) -> u64 {
        MAX_FRAME_SIZE_BYTES
    }

    /// Largest per-call outgoing argument area admitted by native v0.
    #[must_use]
    pub const fn maximum_outgoing_stack_size_bytes(self) -> u64 {
        MAX_OUTGOING_STACK_SIZE_BYTES
    }

    /// Lowers resolved VIR into a deterministic, instruction-selection-neutral
    /// x86_64 frame and control-flow plan.
    pub fn plan_program(
        self,
        program: &ResolvedRuntimeVirView<'_>,
    ) -> Result<X86_64ProgramPlan, X86_64PlanningError> {
        let memory_target = program.memory.target;
        if memory_target.endianness != VirEndianness::Little
            || memory_target.pointer_size_bytes != 8
            || memory_target.pointer_alignment != 8
            || memory_target.usize_size_bytes != 8
            || memory_target.usize_alignment != 8
        {
            let entry = program
                .functions
                .iter()
                .find(|function| function.id == program.entry)
                .expect("resolved validated VIR contains its entry function");
            return Err(function_error(
                entry,
                X86_64PlanningErrorKind::UnsupportedMemoryTarget,
            ));
        }
        let functions = program
            .functions
            .iter()
            .map(|function| plan_function(self, program, function))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(X86_64ProgramPlan {
            entry: program.entry,
            functions,
        })
    }
}

/// Complete deterministic planning result for one closed, resolved VIR program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64ProgramPlan {
    entry: VirFunctionId,
    functions: Vec<X86_64FunctionPlan>,
}

impl X86_64ProgramPlan {
    #[must_use]
    pub const fn entry(&self) -> VirFunctionId {
        self.entry
    }

    #[must_use]
    pub fn functions(&self) -> &[X86_64FunctionPlan] {
        &self.functions
    }

    #[must_use]
    pub fn function(&self, id: VirFunctionId) -> Option<&X86_64FunctionPlan> {
        self.functions.iter().find(|function| function.id == id)
    }
}

/// Native planning data for one VIR function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64FunctionPlan {
    id: VirFunctionId,
    symbol: String,
    signature: X86_64RuntimeSignature,
    frame: X86_64FramePlan,
    incoming_parameters: Vec<X86_64IncomingParameterPlan>,
    blocks: Vec<X86_64BlockPlan>,
    maximum_outgoing_stack_size_bytes: u64,
}

impl X86_64FunctionPlan {
    #[must_use]
    pub const fn id(&self) -> VirFunctionId {
        self.id
    }

    #[must_use]
    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    #[must_use]
    pub const fn signature(&self) -> &X86_64RuntimeSignature {
        &self.signature
    }

    #[must_use]
    pub const fn frame(&self) -> &X86_64FramePlan {
        &self.frame
    }

    #[must_use]
    pub fn incoming_parameters(&self) -> &[X86_64IncomingParameterPlan] {
        &self.incoming_parameters
    }

    #[must_use]
    pub fn blocks(&self) -> &[X86_64BlockPlan] {
        &self.blocks
    }

    #[must_use]
    pub fn block(&self, id: VirBlockId) -> Option<&X86_64BlockPlan> {
        self.blocks.iter().find(|block| block.id == id)
    }

    #[must_use]
    pub const fn maximum_outgoing_stack_size_bytes(&self) -> u64 {
        self.maximum_outgoing_stack_size_bytes
    }
}

/// Fixed rbp-relative frame. Every retained SSA value has a distinct word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64FramePlan {
    size_bytes: u64,
    used_bytes: u64,
    value_slots: BTreeMap<VirValueId, X86_64FrameSlot>,
    local_storage_regions: BTreeMap<VirValueId, X86_64FrameRegion>,
    hidden_result_buffer_pointer: Option<X86_64FrameSlot>,
    indirect_call_result_area: Option<X86_64FrameRegion>,
    parallel_copy_temporaries: Vec<X86_64FrameSlot>,
}

impl X86_64FramePlan {
    /// Bytes subtracted from `%rsp` after `push rbp; mov rbp, rsp`.
    #[must_use]
    pub const fn size_bytes(&self) -> u64 {
        self.size_bytes
    }

    /// Bytes occupied before final 16-byte frame padding.
    #[must_use]
    pub const fn used_bytes(&self) -> u64 {
        self.used_bytes
    }

    #[must_use]
    pub fn value_slot(&self, value: VirValueId) -> Option<X86_64FrameSlot> {
        self.value_slots.get(&value).copied()
    }

    #[must_use]
    pub fn value_slots(&self) -> &BTreeMap<VirValueId, X86_64FrameSlot> {
        &self.value_slots
    }

    #[must_use]
    pub fn local_storage_region(&self, pointer: VirValueId) -> Option<X86_64FrameRegion> {
        self.local_storage_regions.get(&pointer).copied()
    }

    #[must_use]
    pub fn local_storage_regions(&self) -> &BTreeMap<VirValueId, X86_64FrameRegion> {
        &self.local_storage_regions
    }

    #[must_use]
    pub const fn hidden_result_buffer_pointer(&self) -> Option<X86_64FrameSlot> {
        self.hidden_result_buffer_pointer
    }

    #[must_use]
    pub const fn indirect_call_result_area(&self) -> Option<X86_64FrameRegion> {
        self.indirect_call_result_area
    }

    #[must_use]
    pub fn parallel_copy_temporaries(&self) -> &[X86_64FrameSlot] {
        &self.parallel_copy_temporaries
    }
}

/// One 8-byte word at a negative offset from `%rbp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64FrameSlot {
    offset_from_rbp_bytes: i32,
}

impl X86_64FrameSlot {
    #[must_use]
    pub const fn offset_from_rbp_bytes(self) -> i32 {
        self.offset_from_rbp_bytes
    }
}

/// Contiguous, increasing-address frame area used as an indirect result buffer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64FrameRegion {
    base_offset_from_rbp_bytes: i32,
    size_bytes: u64,
    alignment_bytes: u64,
}

impl X86_64FrameRegion {
    #[must_use]
    pub const fn base_offset_from_rbp_bytes(self) -> i32 {
        self.base_offset_from_rbp_bytes
    }

    #[must_use]
    pub const fn size_bytes(self) -> u64 {
        self.size_bytes
    }

    #[must_use]
    pub const fn alignment_bytes(self) -> u64 {
        self.alignment_bytes
    }
}

/// Prologue transfer from one ABI parameter location into its SSA frame slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64IncomingParameterPlan {
    vir_index: usize,
    value: VirValueId,
    ty: X86_64RuntimeType,
    source: X86_64AbiParameterLocation,
    destination: X86_64FrameSlot,
}

impl X86_64IncomingParameterPlan {
    #[must_use]
    pub const fn vir_index(self) -> usize {
        self.vir_index
    }

    #[must_use]
    pub const fn value(self) -> VirValueId {
        self.value
    }

    #[must_use]
    pub const fn ty(self) -> X86_64RuntimeType {
        self.ty
    }

    #[must_use]
    pub const fn source(self) -> X86_64AbiParameterLocation {
        self.source
    }

    #[must_use]
    pub const fn destination(self) -> X86_64FrameSlot {
        self.destination
    }
}

/// One original VIR block plus its lowering-only annotations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64BlockPlan {
    id: VirBlockId,
    instructions: Vec<X86_64InstructionPlan>,
    terminator: X86_64TerminatorPlan,
}

impl X86_64BlockPlan {
    #[must_use]
    pub const fn id(&self) -> VirBlockId {
        self.id
    }

    /// Same cardinality and order as the source VIR instruction list.
    #[must_use]
    pub fn instructions(&self) -> &[X86_64InstructionPlan] {
        &self.instructions
    }

    #[must_use]
    pub const fn terminator(&self) -> &X86_64TerminatorPlan {
        &self.terminator
    }
}

/// Planning classification paired positionally with a VIR instruction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum X86_64InstructionPlan {
    Runtime,
    /// Physical empty resource representation, not initialized language values.
    HeapStorage {
        empty_resource_offsets: Vec<u64>,
        cleanup_tag: Option<X86_64EnumDiscriminantPlan>,
    },
    ErasedPermission,
    /// Keeps the reference pointer copy while erasing loan/region metadata and permission.
    LoanReference,
    /// Completely erased loan lifecycle event with no runtime result.
    ErasedLoan,
    ErasedObjectState,
    LocalStorage(X86_64FrameRegion),
    ObjectTransfer(X86_64ObjectTransferPlan),
    /// Canonical resource pointer slots initialized to the empty sentinel.
    ResourceStorageReset(Vec<u64>),
    EnumDiscriminant(X86_64EnumDiscriminantPlan),
    Call(X86_64CallPlan),
}

/// Fixed-size physical transfer selected for a statically verified object
/// effect. Padding may be copied but remains unobservable in VIR.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct X86_64ObjectTransferPlan {
    size_bytes: u64,
    /// Unconditional resource slots retired by Move. Tagged payload partial
    /// cleanup remains outside the native profile; whole enum moves use flags.
    retired_source_offsets: Vec<u64>,
}

impl X86_64ObjectTransferPlan {
    #[must_use]
    pub const fn size_bytes(&self) -> u64 {
        self.size_bytes
    }

    #[must_use]
    pub fn retired_source_offsets(&self) -> &[u64] {
        &self.retired_source_offsets
    }
}

/// Canonical enum tag encoding selected from the memory schema.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct X86_64EnumDiscriminantPlan {
    offset_bytes: u64,
    size_bytes: u64,
    discriminant: u64,
    empty_resource_offsets: Vec<u64>,
}

impl X86_64EnumDiscriminantPlan {
    #[must_use]
    pub const fn offset_bytes(&self) -> u64 {
        self.offset_bytes
    }

    #[must_use]
    pub const fn size_bytes(&self) -> u64 {
        self.size_bytes
    }

    #[must_use]
    pub const fn discriminant(&self) -> u64 {
        self.discriminant
    }

    /// Physically empty slots in the selected construction representation.
    /// Zero is not a valid safe pointer and does not initialize a language value.
    #[must_use]
    pub fn empty_resource_offsets(&self) -> &[u64] {
        &self.empty_resource_offsets
    }
}

/// A resolved local call after verifier-only arguments and results are erased.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64CallPlan {
    callee: VirFunctionId,
    signature: X86_64RuntimeSignature,
    arguments: Vec<X86_64CallArgumentPlan>,
    results: Vec<X86_64CallResultPlan>,
    indirect_result_area: Option<X86_64FrameRegion>,
}

impl X86_64CallPlan {
    #[must_use]
    pub const fn callee(&self) -> VirFunctionId {
        self.callee
    }

    #[must_use]
    pub const fn signature(&self) -> &X86_64RuntimeSignature {
        &self.signature
    }

    #[must_use]
    pub fn arguments(&self) -> &[X86_64CallArgumentPlan] {
        &self.arguments
    }

    #[must_use]
    pub fn results(&self) -> &[X86_64CallResultPlan] {
        &self.results
    }

    #[must_use]
    pub const fn indirect_result_area(&self) -> Option<X86_64FrameRegion> {
        self.indirect_result_area
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64CallArgumentPlan {
    vir_index: usize,
    value: VirValueId,
    ty: X86_64RuntimeType,
    location: X86_64AbiParameterLocation,
}

impl X86_64CallArgumentPlan {
    #[must_use]
    pub const fn vir_index(self) -> usize {
        self.vir_index
    }

    #[must_use]
    pub const fn value(self) -> VirValueId {
        self.value
    }

    #[must_use]
    pub const fn ty(self) -> X86_64RuntimeType {
        self.ty
    }

    #[must_use]
    pub const fn location(self) -> X86_64AbiParameterLocation {
        self.location
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64CallResultPlan {
    vir_index: usize,
    value: VirValueId,
    ty: X86_64RuntimeType,
    location: X86_64AbiResultLocation,
    destination: X86_64FrameSlot,
}

impl X86_64CallResultPlan {
    #[must_use]
    pub const fn vir_index(self) -> usize {
        self.vir_index
    }

    #[must_use]
    pub const fn value(self) -> VirValueId {
        self.value
    }

    #[must_use]
    pub const fn ty(self) -> X86_64RuntimeType {
        self.ty
    }

    #[must_use]
    pub const fn location(self) -> X86_64AbiResultLocation {
        self.location
    }

    #[must_use]
    pub const fn destination(self) -> X86_64FrameSlot {
        self.destination
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum X86_64TerminatorPlan {
    Jump {
        edge: X86_64EdgePlan,
    },
    Branch {
        then_edge: X86_64EdgePlan,
        else_edge: X86_64EdgePlan,
    },
    Return {
        values: Vec<X86_64ReturnValuePlan>,
    },
}

/// One runtime return transfer to `%rax` or the incoming hidden buffer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64ReturnValuePlan {
    vir_index: usize,
    value: VirValueId,
    ty: X86_64RuntimeType,
    destination: X86_64AbiResultLocation,
}

impl X86_64ReturnValuePlan {
    #[must_use]
    pub const fn vir_index(self) -> usize {
        self.vir_index
    }

    #[must_use]
    pub const fn value(self) -> VirValueId {
        self.value
    }

    #[must_use]
    pub const fn ty(self) -> X86_64RuntimeType {
        self.ty
    }

    #[must_use]
    pub const fn destination(self) -> X86_64AbiResultLocation {
        self.destination
    }
}

/// Planned transfer of runtime block arguments on one CFG edge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64EdgePlan {
    target: VirBlockId,
    placement: X86_64EdgeCopyPlacement,
    copies: Vec<X86_64ParallelCopy>,
}

impl X86_64EdgePlan {
    #[must_use]
    pub const fn target(&self) -> VirBlockId {
        self.target
    }

    #[must_use]
    pub const fn placement(&self) -> X86_64EdgeCopyPlacement {
        self.placement
    }

    /// Emit every source-to-temporary move before any temporary-to-destination
    /// move. This two-phase schedule preserves arbitrary cycles.
    #[must_use]
    pub fn copies(&self) -> &[X86_64ParallelCopy] {
        &self.copies
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64EdgeCopyPlacement {
    Direct,
    InlineBeforeJump,
    SplitBlock(X86_64SyntheticEdgeBlock),
}

/// Stable identity for a branch-only lowering block.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64SyntheticEdgeBlock {
    predecessor: VirBlockId,
    arm: X86_64BranchArm,
}

impl X86_64SyntheticEdgeBlock {
    #[must_use]
    pub const fn predecessor(self) -> VirBlockId {
        self.predecessor
    }

    #[must_use]
    pub const fn arm(self) -> X86_64BranchArm {
        self.arm
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum X86_64BranchArm {
    Then,
    Else,
}

/// One member of a two-phase parallel-copy schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct X86_64ParallelCopy {
    source_value: VirValueId,
    source: X86_64FrameSlot,
    temporary: X86_64FrameSlot,
    destination_value: VirValueId,
    destination: X86_64FrameSlot,
}

impl X86_64ParallelCopy {
    #[must_use]
    pub const fn source_value(self) -> VirValueId {
        self.source_value
    }

    #[must_use]
    pub const fn source(self) -> X86_64FrameSlot {
        self.source
    }

    #[must_use]
    pub const fn temporary(self) -> X86_64FrameSlot {
        self.temporary
    }

    #[must_use]
    pub const fn destination_value(self) -> VirValueId {
        self.destination_value
    }

    #[must_use]
    pub const fn destination(self) -> X86_64FrameSlot {
        self.destination
    }
}

/// Deterministic, source-localized failure during native planning.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct X86_64PlanningError {
    kind: X86_64PlanningErrorKind,
    function: VirFunctionId,
    block: Option<VirBlockId>,
    instruction_index: Option<usize>,
    source_span: ByteSpan,
}

impl X86_64PlanningError {
    #[must_use]
    pub const fn kind(&self) -> &X86_64PlanningErrorKind {
        &self.kind
    }

    #[must_use]
    pub const fn function(&self) -> VirFunctionId {
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
    pub const fn source_span(&self) -> ByteSpan {
        self.source_span
    }

    /// Reports target capability limits without conflating them with invalid
    /// VIR or internal producer/consumer inconsistencies.
    #[must_use]
    pub const fn capability_failure_kind(&self) -> Option<crate::CapabilityFailureKind> {
        match &self.kind {
            X86_64PlanningErrorKind::Abi(_)
            | X86_64PlanningErrorKind::UnsupportedMemoryTarget
            | X86_64PlanningErrorKind::UnsupportedLocalStorageAlignment { .. }
            | X86_64PlanningErrorKind::FrameSizeExceeded { .. }
            | X86_64PlanningErrorKind::OutgoingStackSizeExceeded { .. }
            | X86_64PlanningErrorKind::UnsupportedObjectEffectType { .. }
            | X86_64PlanningErrorKind::ObjectEffectSizeExceeded { .. } => {
                Some(crate::CapabilityFailureKind::TargetUnsupported)
            }
            X86_64PlanningErrorKind::MissingRuntimeValueSlot(_)
            | X86_64PlanningErrorKind::MissingTargetBlock(_)
            | X86_64PlanningErrorKind::MissingResolvedCall(_)
            | X86_64PlanningErrorKind::InconsistentValidatedVir(_) => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum X86_64PlanningErrorKind {
    Abi(X86_64AbiError),
    UnsupportedMemoryTarget,
    UnsupportedLocalStorageAlignment { requested: u64, maximum: u64 },
    FrameSizeExceeded { requested: u64, maximum: u64 },
    OutgoingStackSizeExceeded { requested: u64, maximum: u64 },
    MissingRuntimeValueSlot(VirValueId),
    MissingTargetBlock(VirBlockId),
    MissingResolvedCall(String),
    UnsupportedObjectEffectType { access: VirMemoryAccess },
    ObjectEffectSizeExceeded { requested: u64, maximum: u64 },
    InconsistentValidatedVir(&'static str),
}

impl fmt::Display for X86_64PlanningError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "x86_64 planning failed in fn{}",
            self.function.get()
        )?;
        if let Some(block) = self.block {
            write!(formatter, "/bb{}", block.get())?;
        }
        if let Some(index) = self.instruction_index {
            write!(formatter, "/instruction {index}")?;
        }
        write!(formatter, ": ")?;
        match &self.kind {
            X86_64PlanningErrorKind::Abi(error) => error.fmt(formatter),
            X86_64PlanningErrorKind::UnsupportedMemoryTarget => formatter.write_str(
                "VIR memory target is not x86_64 little-endian with 64-bit pointer/usize layout",
            ),
            X86_64PlanningErrorKind::UnsupportedLocalStorageAlignment { requested, maximum } => {
                write!(
                    formatter,
                    "local storage alignment {requested} exceeds the native frame guarantee of {maximum}"
                )
            }
            X86_64PlanningErrorKind::FrameSizeExceeded { requested, maximum } => write!(
                formatter,
                "frame requires {requested} bytes; native v0 permits at most {maximum}"
            ),
            X86_64PlanningErrorKind::OutgoingStackSizeExceeded { requested, maximum } => write!(
                formatter,
                "call requires {requested} outgoing stack bytes; native v0 permits at most {maximum}"
            ),
            X86_64PlanningErrorKind::MissingRuntimeValueSlot(value) => {
                write!(
                    formatter,
                    "runtime value %{} has no frame slot",
                    value.get()
                )
            }
            X86_64PlanningErrorKind::MissingTargetBlock(block) => {
                write!(
                    formatter,
                    "target bb{} is absent from the function",
                    block.get()
                )
            }
            X86_64PlanningErrorKind::MissingResolvedCall(symbol) => {
                write!(formatter, "call `{symbol}` has no resolved local target")
            }
            X86_64PlanningErrorKind::UnsupportedObjectEffectType { access } => write!(
                formatter,
                "object effect for type{}/layout{} has no native representation",
                access.ty.get(),
                access.layout.get()
            ),
            X86_64PlanningErrorKind::ObjectEffectSizeExceeded { requested, maximum } => write!(
                formatter,
                "object effect requires {requested} bytes; native inline object transfer permits at most {maximum}"
            ),
            X86_64PlanningErrorKind::InconsistentValidatedVir(context) => {
                write!(
                    formatter,
                    "validated VIR invariant was not preserved: {context}"
                )
            }
        }
    }
}

impl Error for X86_64PlanningError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            X86_64PlanningErrorKind::Abi(error) => Some(error),
            _ => None,
        }
    }
}

struct FunctionPlanner<'a> {
    target: X86_64LinuxTarget,
    memory: &'a VirMemorySchema,
    function: &'a VirFunction,
    signature: X86_64RuntimeSignature,
    frame: X86_64FramePlan,
    analysis: FunctionAnalysis,
}

#[derive(Clone, Debug)]
struct FunctionAnalysis {
    calls: BTreeMap<(VirBlockId, usize), AnalyzedCall>,
    constant_words: BTreeMap<VirValueId, u64>,
    maximum_outgoing_stack_size_bytes: u64,
    maximum_indirect_result_size_bytes: u64,
    maximum_parallel_copy_count: usize,
}

#[derive(Clone, Debug)]
struct AnalyzedCall {
    callee: VirFunctionId,
    signature: X86_64RuntimeSignature,
}

fn plan_function(
    target: X86_64LinuxTarget,
    program: &ResolvedRuntimeVirView<'_>,
    function: &VirFunction,
) -> Result<X86_64FunctionPlan, X86_64PlanningError> {
    let signature = target
        .classify_signature(&function.signature)
        .map_err(|error| function_error(function, X86_64PlanningErrorKind::Abi(error)))?;
    let analysis = analyze_function(target, program, function)?;
    let frame = plan_frame(target, program.memory, function, &signature, &analysis)?;
    let planner = FunctionPlanner {
        target,
        memory: program.memory,
        function,
        signature,
        frame,
        analysis,
    };
    planner.finish()
}

impl FunctionPlanner<'_> {
    fn finish(self) -> Result<X86_64FunctionPlan, X86_64PlanningError> {
        let entry = self
            .function
            .blocks
            .iter()
            .find(|block| block.id == self.function.entry)
            .ok_or_else(|| {
                function_error(
                    self.function,
                    X86_64PlanningErrorKind::MissingTargetBlock(self.function.entry),
                )
            })?;
        let incoming_parameters = self.plan_incoming_parameters(entry)?;
        let blocks = self
            .function
            .blocks
            .iter()
            .map(|block| self.plan_block(block))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(X86_64FunctionPlan {
            id: self.function.id,
            symbol: self.target.internal_function_symbol(self.function.id),
            signature: self.signature,
            frame: self.frame,
            incoming_parameters,
            blocks,
            maximum_outgoing_stack_size_bytes: self.analysis.maximum_outgoing_stack_size_bytes,
        })
    }

    fn plan_incoming_parameters(
        &self,
        entry: &VirBasicBlock,
    ) -> Result<Vec<X86_64IncomingParameterPlan>, X86_64PlanningError> {
        self.signature
            .parameters()
            .iter()
            .map(|parameter| {
                let value = entry
                    .parameters
                    .get(parameter.vir_index())
                    .ok_or_else(|| {
                        block_error(
                            self.function,
                            entry,
                            entry.source_span,
                            X86_64PlanningErrorKind::InconsistentValidatedVir(
                                "entry parameter is absent",
                            ),
                        )
                    })?
                    .id;
                Ok(X86_64IncomingParameterPlan {
                    vir_index: parameter.vir_index(),
                    value,
                    ty: parameter.ty(),
                    source: parameter.location(),
                    destination: self.value_slot(value, entry, None)?,
                })
            })
            .collect()
    }

    fn plan_block(&self, block: &VirBasicBlock) -> Result<X86_64BlockPlan, X86_64PlanningError> {
        let instructions = block
            .instructions
            .iter()
            .enumerate()
            .map(|(index, spanned)| match &spanned.instruction {
                VirInstruction::LoanBegin { .. }
                | VirInstruction::LoanAliasShared { .. }
                | VirInstruction::LoanReborrow { .. }
                | VirInstruction::LoanAliasAuthority { .. }
                | VirInstruction::LoanReborrowAuthority { .. } => {
                    Ok(X86_64InstructionPlan::LoanReference)
                }
                VirInstruction::LoanEnd { .. } | VirInstruction::LoanEndAuthority { .. } => {
                    Ok(X86_64InstructionPlan::ErasedLoan)
                }
                VirInstruction::PermissionSplit { .. }
                | VirInstruction::PermissionJoin { .. }
                | VirInstruction::PermissionMove { .. } => {
                    Ok(X86_64InstructionPlan::ErasedPermission)
                }
                VirInstruction::Allocate {
                    element,
                    size_bytes,
                    ..
                } => {
                    let shape = self.native_object_observation_shape(
                        block,
                        index,
                        spanned.source_span,
                        *element,
                    )?;
                    if shape.resource_leaves().is_empty() {
                        return Ok(X86_64InstructionPlan::Runtime);
                    }
                    let exact_size = self.analysis.constant_words.get(size_bytes).copied();
                    if exact_size != Some(shape.size_bytes())
                        || shape.variants().iter().any(|case| {
                            !case.path().segments().is_empty() || case.tag().len_bytes() != 1
                        })
                    {
                        return Err(instruction_error(
                            self.function,
                            block,
                            index,
                            spanned.source_span,
                            X86_64PlanningErrorKind::UnsupportedObjectEffectType {
                                access: *element,
                            },
                        ));
                    }
                    self.check_inline_object_size(
                        block,
                        index,
                        spanned.source_span,
                        shape.size_bytes(),
                    )?;
                    let cleanup_tag =
                        shape
                            .variants()
                            .first()
                            .map(|case| X86_64EnumDiscriminantPlan {
                                offset_bytes: case.tag().start_bytes(),
                                size_bytes: case.tag().len_bytes(),
                                discriminant: case.discriminant(),
                                empty_resource_offsets: Vec::new(),
                            });
                    Ok(X86_64InstructionPlan::HeapStorage {
                        empty_resource_offsets: shape
                            .resource_leaves()
                            .iter()
                            .map(|leaf| leaf.bytes().start_bytes())
                            .collect(),
                        cleanup_tag,
                    })
                }
                VirInstruction::DropOwn { .. } => Ok(X86_64InstructionPlan::Runtime),
                VirInstruction::LocalStorage { pointer_result, .. } => self
                    .frame
                    .local_storage_region(pointer_result.id)
                    .map(X86_64InstructionPlan::LocalStorage)
                    .ok_or_else(|| {
                        instruction_error(
                            self.function,
                            block,
                            index,
                            spanned.source_span,
                            X86_64PlanningErrorKind::InconsistentValidatedVir(
                                "local storage frame region is absent",
                            ),
                        )
                    }),
                VirInstruction::ObjectTransfer {
                    access,
                    destination_mode,
                    source_mode,
                    ..
                } => self
                    .native_object_transfer_shape(
                        block,
                        index,
                        spanned.source_span,
                        *access,
                        *destination_mode,
                        *source_mode,
                    )
                    .and_then(|shape| {
                        self.check_inline_object_size(
                            block,
                            index,
                            spanned.source_span,
                            shape.size_bytes(),
                        )?;
                        Ok(X86_64InstructionPlan::ObjectTransfer(
                            X86_64ObjectTransferPlan {
                                size_bytes: shape.size_bytes(),
                                retired_source_offsets: if *source_mode
                                    == crate::VirObjectSourceMode::Move
                                {
                                    shape
                                        .resource_leaves()
                                        .iter()
                                        .map(|leaf| leaf.bytes().start_bytes())
                                        .collect()
                                } else {
                                    Vec::new()
                                },
                            },
                        ))
                    }),
                VirInstruction::ObjectDeinitialize { access, .. }
                | VirInstruction::StorageReset { access, .. } => self
                    .native_object_shape(block, index, spanned.source_span, *access)
                    .map(|_| X86_64InstructionPlan::ErasedObjectState),
                VirInstruction::ResourceStorageReset { access, .. } => {
                    let shape = self.native_object_observation_shape(
                        block,
                        index,
                        spanned.source_span,
                        *access,
                    )?;
                    if !shape.supports_resource_storage_reset() {
                        return Err(instruction_error(
                            self.function,
                            block,
                            index,
                            spanned.source_span,
                            X86_64PlanningErrorKind::UnsupportedObjectEffectType {
                                access: *access,
                            },
                        ));
                    }
                    self.check_inline_object_size(
                        block,
                        index,
                        spanned.source_span,
                        shape.size_bytes(),
                    )?;
                    Ok(X86_64InstructionPlan::ResourceStorageReset(
                        shape
                            .resource_leaves()
                            .iter()
                            .map(|leaf| leaf.bytes().start_bytes())
                            .collect(),
                    ))
                }
                VirInstruction::ObjectDrop { access, .. } => {
                    let shape = self.native_object_observation_shape(
                        block,
                        index,
                        spanned.source_span,
                        *access,
                    )?;
                    if shape.variants().iter().any(|case| {
                        !case.path().segments().is_empty() || case.tag().len_bytes() != 1
                    }) {
                        return Err(instruction_error(
                            self.function,
                            block,
                            index,
                            spanned.source_span,
                            X86_64PlanningErrorKind::UnsupportedObjectEffectType {
                                access: *access,
                            },
                        ));
                    }
                    Ok(X86_64InstructionPlan::Runtime)
                }
                VirInstruction::EnumDiscriminant { access, .. } => {
                    let shape = self.native_object_observation_shape(
                        block,
                        index,
                        spanned.source_span,
                        *access,
                    )?;
                    let Some(case) = shape
                        .variants()
                        .iter()
                        .find(|case| case.path().segments().is_empty())
                    else {
                        return Err(instruction_error(
                            self.function,
                            block,
                            index,
                            spanned.source_span,
                            X86_64PlanningErrorKind::InconsistentValidatedVir(
                                "enum discriminant shape has no root case",
                            ),
                        ));
                    };
                    if case.tag().len_bytes() != 1
                        || shape.variants().iter().any(|candidate| {
                            candidate.path().segments().is_empty() && candidate.tag() != case.tag()
                        })
                    {
                        return Err(instruction_error(
                            self.function,
                            block,
                            index,
                            spanned.source_span,
                            X86_64PlanningErrorKind::UnsupportedObjectEffectType {
                                access: *access,
                            },
                        ));
                    }
                    Ok(X86_64InstructionPlan::Runtime)
                }
                VirInstruction::EnumSetDiscriminant {
                    access,
                    variant,
                    mode,
                    ..
                } => {
                    let shape = if *mode == crate::VirObjectDestinationMode::Initialize {
                        self.native_object_observation_shape(
                            block,
                            index,
                            spanned.source_span,
                            *access,
                        )?
                    } else {
                        self.native_object_shape(block, index, spanned.source_span, *access)?
                    };
                    if !shape.resource_leaves().is_empty()
                        && shape.variants().iter().any(|case| {
                            !case.path().segments().is_empty() || case.tag().len_bytes() != 1
                        })
                    {
                        return Err(instruction_error(
                            self.function,
                            block,
                            index,
                            spanned.source_span,
                            X86_64PlanningErrorKind::UnsupportedObjectEffectType {
                                access: *access,
                            },
                        ));
                    }
                    let case = shape
                        .variants()
                        .iter()
                        .find(|case| {
                            case.path().segments().is_empty() && case.variant() == *variant
                        })
                        .ok_or_else(|| {
                            instruction_error(
                                self.function,
                                block,
                                index,
                                spanned.source_span,
                                X86_64PlanningErrorKind::InconsistentValidatedVir(
                                    "enum object effect variant is absent from its shape",
                                ),
                            )
                        })?;
                    self.check_inline_object_size(
                        block,
                        index,
                        spanned.source_span,
                        case.tag().len_bytes(),
                    )?;
                    Ok(X86_64InstructionPlan::EnumDiscriminant(
                        X86_64EnumDiscriminantPlan {
                            offset_bytes: case.tag().start_bytes(),
                            size_bytes: case.tag().len_bytes(),
                            discriminant: case.discriminant(),
                            empty_resource_offsets: case
                                .leaves()
                                .iter()
                                .filter(|leaf| {
                                    matches!(
                                        self.memory.kind(leaf.access().ty),
                                        Some(crate::VirMemoryTypeKind::Pointer {
                                            kind: crate::VirPointerKind::Own
                                                | crate::VirPointerKind::Reference,
                                            ..
                                        })
                                    )
                                })
                                .map(|leaf| leaf.bytes().start_bytes())
                                .collect(),
                        },
                    ))
                }
                VirInstruction::Call {
                    results, arguments, ..
                } => {
                    let analyzed =
                        self.analysis.calls.get(&(block.id, index)).ok_or_else(|| {
                            instruction_error(
                                self.function,
                                block,
                                index,
                                spanned.source_span,
                                X86_64PlanningErrorKind::InconsistentValidatedVir(
                                    "call analysis is absent",
                                ),
                            )
                        })?;
                    let call = self.plan_call(
                        block,
                        index,
                        spanned.source_span,
                        analyzed.callee,
                        analyzed.signature.clone(),
                        arguments,
                        results,
                    )?;
                    Ok(X86_64InstructionPlan::Call(call))
                }
                _ => Ok(X86_64InstructionPlan::Runtime),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let terminator = self.plan_terminator(block)?;
        Ok(X86_64BlockPlan {
            id: block.id,
            instructions,
            terminator,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn plan_call(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        callee: VirFunctionId,
        signature: X86_64RuntimeSignature,
        argument_values: &[VirValueId],
        result_values: &[VirValue],
    ) -> Result<X86_64CallPlan, X86_64PlanningError> {
        let arguments = signature
            .parameters()
            .iter()
            .map(|parameter| {
                let value = *argument_values.get(parameter.vir_index()).ok_or_else(|| {
                    instruction_error(
                        self.function,
                        block,
                        instruction_index,
                        source_span,
                        X86_64PlanningErrorKind::InconsistentValidatedVir(
                            "call argument is absent",
                        ),
                    )
                })?;
                Ok(X86_64CallArgumentPlan {
                    vir_index: parameter.vir_index(),
                    value,
                    ty: parameter.ty(),
                    location: parameter.location(),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let results = signature
            .results()
            .iter()
            .map(|result| {
                let value = result_values
                    .get(result.vir_index())
                    .ok_or_else(|| {
                        instruction_error(
                            self.function,
                            block,
                            instruction_index,
                            source_span,
                            X86_64PlanningErrorKind::InconsistentValidatedVir(
                                "call result is absent",
                            ),
                        )
                    })?
                    .id;
                Ok(X86_64CallResultPlan {
                    vir_index: result.vir_index(),
                    value,
                    ty: result.ty(),
                    location: result.location(),
                    destination: self.value_slot_at(
                        value,
                        block,
                        instruction_index,
                        source_span,
                    )?,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let indirect_result_area = if signature.result_buffer().is_some() {
            Some(self.frame.indirect_call_result_area.ok_or_else(|| {
                instruction_error(
                    self.function,
                    block,
                    instruction_index,
                    source_span,
                    X86_64PlanningErrorKind::InconsistentValidatedVir(
                        "indirect call result area is absent",
                    ),
                )
            })?)
        } else {
            None
        };
        Ok(X86_64CallPlan {
            callee,
            signature,
            arguments,
            results,
            indirect_result_area,
        })
    }

    fn native_object_shape(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        access: VirMemoryAccess,
    ) -> Result<crate::VirObjectShape, X86_64PlanningError> {
        let shape = self.memory.object_shape(access).map_err(|_| {
            instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64PlanningErrorKind::InconsistentValidatedVir("object effect shape is invalid"),
            )
        })?;
        if !self
            .memory
            .type_capabilities(access.ty)
            .is_some_and(crate::TypeCapabilities::pointer_free_trivial)
        {
            return Err(instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64PlanningErrorKind::UnsupportedObjectEffectType { access },
            ));
        }
        Ok(shape)
    }

    fn native_object_observation_shape(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        access: VirMemoryAccess,
    ) -> Result<crate::VirObjectShape, X86_64PlanningError> {
        let shape = self.memory.object_shape(access).map_err(|_| {
            instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64PlanningErrorKind::InconsistentValidatedVir("object effect shape is invalid"),
            )
        })?;
        let supported = self
            .memory
            .type_capabilities(access.ty)
            .is_some_and(|capability| capability.size == crate::SizeCapability::Sized)
            && shape
                .resource_leaves()
                .iter()
                .all(|leaf| leaf.kind() != crate::VirPointerKind::Raw);
        if !supported {
            return Err(instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64PlanningErrorKind::UnsupportedObjectEffectType { access },
            ));
        }
        Ok(shape)
    }

    #[allow(clippy::too_many_arguments)]
    fn native_object_transfer_shape(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        access: VirMemoryAccess,
        destination_mode: crate::VirObjectDestinationMode,
        source_mode: crate::VirObjectSourceMode,
    ) -> Result<crate::VirObjectShape, X86_64PlanningError> {
        let shape = self.memory.object_shape(access).map_err(|_| {
            instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64PlanningErrorKind::InconsistentValidatedVir("object effect shape is invalid"),
            )
        })?;
        let capability = self.memory.type_capabilities(access.ty);
        let supported = match source_mode {
            crate::VirObjectSourceMode::Copy => {
                capability.is_some_and(|capability| {
                    capability.value == crate::ValueCapability::Copy
                        && capability.size == crate::SizeCapability::Sized
                }) && shape.resource_leaves().iter().all(|leaf| {
                    leaf.kind() == crate::VirPointerKind::Reference
                        && leaf.mutability() == crate::VirMutability::Const
                })
            }
            crate::VirObjectSourceMode::Move => {
                capability.is_some_and(|capability| capability.size == crate::SizeCapability::Sized)
                    && shape
                        .resource_leaves()
                        .iter()
                        .all(|leaf| leaf.kind() != crate::VirPointerKind::Raw)
                    && (matches!(
                        destination_mode,
                        crate::VirObjectDestinationMode::Initialize
                    ) || capability.is_some_and(crate::TypeCapabilities::pointer_free_trivial))
            }
        };
        if !supported {
            return Err(instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64PlanningErrorKind::UnsupportedObjectEffectType { access },
            ));
        }
        Ok(shape)
    }

    fn check_inline_object_size(
        &self,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
        size_bytes: u64,
    ) -> Result<(), X86_64PlanningError> {
        if size_bytes > X86_64_INLINE_OBJECT_COPY_MAX_BYTES {
            return Err(instruction_error(
                self.function,
                block,
                instruction_index,
                source_span,
                X86_64PlanningErrorKind::ObjectEffectSizeExceeded {
                    requested: size_bytes,
                    maximum: X86_64_INLINE_OBJECT_COPY_MAX_BYTES,
                },
            ));
        }
        Ok(())
    }

    fn plan_terminator(
        &self,
        block: &VirBasicBlock,
    ) -> Result<X86_64TerminatorPlan, X86_64PlanningError> {
        match &block.terminator.terminator {
            VirTerminator::Jump { target } => Ok(X86_64TerminatorPlan::Jump {
                edge: self.plan_edge(block, target, None)?,
            }),
            VirTerminator::Branch {
                then_target,
                else_target,
                ..
            } => Ok(X86_64TerminatorPlan::Branch {
                then_edge: self.plan_edge(block, then_target, Some(X86_64BranchArm::Then))?,
                else_edge: self.plan_edge(block, else_target, Some(X86_64BranchArm::Else))?,
            }),
            VirTerminator::Return { values } => {
                let values = self
                    .signature
                    .results()
                    .iter()
                    .map(|result| {
                        let value = *values.get(result.vir_index()).ok_or_else(|| {
                            block_error(
                                self.function,
                                block,
                                block.terminator.source_span,
                                X86_64PlanningErrorKind::InconsistentValidatedVir(
                                    "return value is absent",
                                ),
                            )
                        })?;
                        Ok(X86_64ReturnValuePlan {
                            vir_index: result.vir_index(),
                            value,
                            ty: result.ty(),
                            destination: result.location(),
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(X86_64TerminatorPlan::Return { values })
            }
        }
    }

    fn plan_edge(
        &self,
        source_block: &VirBasicBlock,
        target: &VirBlockTarget,
        branch_arm: Option<X86_64BranchArm>,
    ) -> Result<X86_64EdgePlan, X86_64PlanningError> {
        let target_block = self
            .function
            .blocks
            .iter()
            .find(|block| block.id == target.block)
            .ok_or_else(|| {
                block_error(
                    self.function,
                    source_block,
                    source_block.terminator.source_span,
                    X86_64PlanningErrorKind::MissingTargetBlock(target.block),
                )
            })?;
        let mut copies = Vec::new();
        for (argument, parameter) in target.arguments.iter().zip(&target_block.parameters) {
            if parameter.ty == VirType::Permission || *argument == parameter.id {
                continue;
            }
            let temporary = *self
                .frame
                .parallel_copy_temporaries
                .get(copies.len())
                .ok_or_else(|| {
                    block_error(
                        self.function,
                        source_block,
                        source_block.terminator.source_span,
                        X86_64PlanningErrorKind::InconsistentValidatedVir(
                            "parallel-copy temporary is absent",
                        ),
                    )
                })?;
            copies.push(X86_64ParallelCopy {
                source_value: *argument,
                source: self.value_slot(*argument, source_block, None)?,
                temporary,
                destination_value: parameter.id,
                destination: self.value_slot(parameter.id, source_block, None)?,
            });
        }
        let placement = match (copies.is_empty(), branch_arm) {
            (true, _) => X86_64EdgeCopyPlacement::Direct,
            (false, None) => X86_64EdgeCopyPlacement::InlineBeforeJump,
            (false, Some(arm)) => X86_64EdgeCopyPlacement::SplitBlock(X86_64SyntheticEdgeBlock {
                predecessor: source_block.id,
                arm,
            }),
        };
        Ok(X86_64EdgePlan {
            target: target.block,
            placement,
            copies,
        })
    }

    fn value_slot(
        &self,
        value: VirValueId,
        block: &VirBasicBlock,
        instruction_index: Option<usize>,
    ) -> Result<X86_64FrameSlot, X86_64PlanningError> {
        self.frame.value_slot(value).ok_or(X86_64PlanningError {
            kind: X86_64PlanningErrorKind::MissingRuntimeValueSlot(value),
            function: self.function.id,
            block: Some(block.id),
            instruction_index,
            source_span: block.source_span,
        })
    }

    fn value_slot_at(
        &self,
        value: VirValueId,
        block: &VirBasicBlock,
        instruction_index: usize,
        source_span: ByteSpan,
    ) -> Result<X86_64FrameSlot, X86_64PlanningError> {
        self.frame.value_slot(value).ok_or(X86_64PlanningError {
            kind: X86_64PlanningErrorKind::MissingRuntimeValueSlot(value),
            function: self.function.id,
            block: Some(block.id),
            instruction_index: Some(instruction_index),
            source_span,
        })
    }
}

fn analyze_function(
    target: X86_64LinuxTarget,
    program: &ResolvedRuntimeVirView<'_>,
    function: &VirFunction,
) -> Result<FunctionAnalysis, X86_64PlanningError> {
    let mut calls = BTreeMap::new();
    let mut constant_words = BTreeMap::new();
    let mut maximum_outgoing_stack_size_bytes = 0;
    let mut maximum_indirect_result_size_bytes = 0;
    let mut maximum_parallel_copy_count = 0;

    for block in &function.blocks {
        for (instruction_index, spanned) in block.instructions.iter().enumerate() {
            if let VirInstruction::Constant {
                result,
                value: crate::VirConstant::U64(value),
            } = spanned.instruction
            {
                constant_words.insert(result.id, value);
            }
            let VirInstruction::Call {
                target: call_target,
                ..
            } = &spanned.instruction
            else {
                continue;
            };
            let signature = target
                .classify_signature(&call_target.signature)
                .map_err(|error| {
                    instruction_error(
                        function,
                        block,
                        instruction_index,
                        spanned.source_span,
                        X86_64PlanningErrorKind::Abi(error),
                    )
                })?;
            let outgoing = signature.outgoing_stack_size_bytes();
            if outgoing > target.maximum_outgoing_stack_size_bytes() {
                return Err(instruction_error(
                    function,
                    block,
                    instruction_index,
                    spanned.source_span,
                    X86_64PlanningErrorKind::OutgoingStackSizeExceeded {
                        requested: outgoing,
                        maximum: target.maximum_outgoing_stack_size_bytes(),
                    },
                ));
            }
            let callee = program.call_target_id(call_target).ok_or_else(|| {
                instruction_error(
                    function,
                    block,
                    instruction_index,
                    spanned.source_span,
                    X86_64PlanningErrorKind::MissingResolvedCall(call_target.symbol.clone()),
                )
            })?;
            maximum_outgoing_stack_size_bytes = maximum_outgoing_stack_size_bytes.max(outgoing);
            maximum_indirect_result_size_bytes = maximum_indirect_result_size_bytes.max(
                signature
                    .result_buffer()
                    .map_or(0, |buffer| buffer.size_bytes()),
            );
            calls.insert(
                (block.id, instruction_index),
                AnalyzedCall { callee, signature },
            );
        }

        match &block.terminator.terminator {
            VirTerminator::Jump { target } => {
                maximum_parallel_copy_count = maximum_parallel_copy_count.max(
                    nontrivial_runtime_copy_count(function, target).map_err(|kind| {
                        block_error(function, block, block.terminator.source_span, kind)
                    })?,
                );
            }
            VirTerminator::Branch {
                then_target,
                else_target,
                ..
            } => {
                for target in [then_target, else_target] {
                    maximum_parallel_copy_count = maximum_parallel_copy_count.max(
                        nontrivial_runtime_copy_count(function, target).map_err(|kind| {
                            block_error(function, block, block.terminator.source_span, kind)
                        })?,
                    );
                }
            }
            VirTerminator::Return { .. } => {}
        }
    }

    Ok(FunctionAnalysis {
        calls,
        constant_words,
        maximum_outgoing_stack_size_bytes,
        maximum_indirect_result_size_bytes,
        maximum_parallel_copy_count,
    })
}

fn plan_frame(
    target: X86_64LinuxTarget,
    memory: &VirMemorySchema,
    function: &VirFunction,
    signature: &X86_64RuntimeSignature,
    analysis: &FunctionAnalysis,
) -> Result<X86_64FramePlan, X86_64PlanningError> {
    let mut builder = FrameBuilder::new(target.maximum_frame_size_bytes());
    let hidden_result_buffer_pointer = signature
        .result_buffer()
        .map(|_| builder.reserve_word())
        .transpose()
        .map_err(|kind| function_error(function, kind))?;
    let mut local_storage_regions = BTreeMap::new();
    for block in &function.blocks {
        for (instruction_index, spanned) in block.instructions.iter().enumerate() {
            if let VirInstruction::LocalStorage {
                pointer_result,
                access,
                ..
            } = &spanned.instruction
            {
                let shape = memory.object_shape(*access).map_err(|_| {
                    instruction_error(
                        function,
                        block,
                        instruction_index,
                        spanned.source_span,
                        X86_64PlanningErrorKind::InconsistentValidatedVir(
                            "local storage object shape is invalid",
                        ),
                    )
                })?;
                if shape.alignment() > u64::from(target.call_stack_alignment_bytes()) {
                    return Err(instruction_error(
                        function,
                        block,
                        instruction_index,
                        spanned.source_span,
                        X86_64PlanningErrorKind::UnsupportedLocalStorageAlignment {
                            requested: shape.alignment(),
                            maximum: u64::from(target.call_stack_alignment_bytes()),
                        },
                    ));
                }
                let region = builder
                    .reserve_region_aligned(shape.size_bytes(), shape.alignment())
                    .map_err(|kind| {
                        instruction_error(
                            function,
                            block,
                            instruction_index,
                            spanned.source_span,
                            kind,
                        )
                    })?;
                local_storage_regions.insert(pointer_result.id, region);
            }
        }
    }

    let mut value_slots = BTreeMap::new();
    for block in &function.blocks {
        for value in &block.parameters {
            reserve_runtime_value(&mut builder, &mut value_slots, *value)
                .map_err(|kind| function_error(function, kind))?;
        }
        for spanned in &block.instructions {
            for value in instruction_results(&spanned.instruction) {
                reserve_runtime_value(&mut builder, &mut value_slots, value)
                    .map_err(|kind| function_error(function, kind))?;
            }
        }
    }

    let indirect_call_result_area = (analysis.maximum_indirect_result_size_bytes != 0)
        .then(|| builder.reserve_region(analysis.maximum_indirect_result_size_bytes))
        .transpose()
        .map_err(|kind| function_error(function, kind))?;

    let mut parallel_copy_temporaries = Vec::with_capacity(analysis.maximum_parallel_copy_count);
    for _ in 0..analysis.maximum_parallel_copy_count {
        parallel_copy_temporaries.push(
            builder
                .reserve_word()
                .map_err(|kind| function_error(function, kind))?,
        );
    }

    let used_bytes = builder.used_bytes;
    let size_bytes = checked_align_up(used_bytes, target.call_stack_alignment_bytes().into())
        .ok_or_else(|| {
            function_error(
                function,
                X86_64PlanningErrorKind::FrameSizeExceeded {
                    requested: u64::MAX,
                    maximum: target.maximum_frame_size_bytes(),
                },
            )
        })?;
    if size_bytes > target.maximum_frame_size_bytes() {
        return Err(function_error(
            function,
            X86_64PlanningErrorKind::FrameSizeExceeded {
                requested: size_bytes,
                maximum: target.maximum_frame_size_bytes(),
            },
        ));
    }
    Ok(X86_64FramePlan {
        size_bytes,
        used_bytes,
        value_slots,
        local_storage_regions,
        hidden_result_buffer_pointer,
        indirect_call_result_area,
        parallel_copy_temporaries,
    })
}

fn reserve_runtime_value(
    builder: &mut FrameBuilder,
    slots: &mut BTreeMap<VirValueId, X86_64FrameSlot>,
    value: VirValue,
) -> Result<(), X86_64PlanningErrorKind> {
    if value.ty != VirType::Permission {
        slots.insert(value.id, builder.reserve_word()?);
    }
    Ok(())
}

fn instruction_results(instruction: &VirInstruction) -> Vec<VirValue> {
    match instruction {
        VirInstruction::Constant { result, .. }
        | VirInstruction::WordAdd { result, .. }
        | VirInstruction::Compare { result, .. }
        | VirInstruction::PointerCompare { result, .. }
        | VirInstruction::PointerDistance { result, .. }
        | VirInstruction::Load { result, .. }
        | VirInstruction::EnumDiscriminant { result, .. }
        | VirInstruction::FieldAddress { result, .. }
        | VirInstruction::TupleElementAddress { result, .. }
        | VirInstruction::ObjectLeafAddress { result, .. }
        | VirInstruction::IndexAddress { result, .. }
        | VirInstruction::PointerOffset { result, .. }
        | VirInstruction::RawAddress { result, .. }
        | VirInstruction::PermissionJoin { result, .. }
        | VirInstruction::PermissionMove { result, .. } => vec![*result],
        VirInstruction::ResourceTake {
            pointer_result,
            permission_result,
            ..
        } => vec![*pointer_result, *permission_result],
        VirInstruction::Allocate {
            pointer_result,
            permission_result,
            ..
        }
        | VirInstruction::LocalStorage {
            pointer_result,
            permission_result,
            ..
        } => vec![*pointer_result, *permission_result],
        VirInstruction::SliceRange {
            pointer_result,
            length_result,
            permission_result,
            ..
        } => vec![*pointer_result, *length_result, *permission_result],
        VirInstruction::SliceAddress {
            pointer_result,
            length_result,
            ..
        } => vec![*pointer_result, *length_result],
        VirInstruction::PermissionSplit {
            left_result,
            right_result,
            ..
        } => vec![*left_result, *right_result],
        VirInstruction::Call { results, .. } => results.clone(),
        VirInstruction::LoanBegin {
            reference_result,
            permission_result,
            ..
        }
        | VirInstruction::LoanAliasShared {
            reference_result,
            permission_result,
            ..
        }
        | VirInstruction::LoanReborrow {
            reference_result,
            permission_result,
            ..
        }
        | VirInstruction::LoanAliasAuthority {
            reference_result,
            permission_result,
            ..
        }
        | VirInstruction::LoanReborrowAuthority {
            reference_result,
            permission_result,
            ..
        } => vec![*reference_result, *permission_result],
        VirInstruction::Initialize { .. }
        | VirInstruction::Write { .. }
        | VirInstruction::Store { .. }
        | VirInstruction::ResourceInitialize { .. }
        | VirInstruction::DropOwn { .. }
        | VirInstruction::ObjectTransfer { .. }
        | VirInstruction::ObjectDeinitialize { .. }
        | VirInstruction::StorageReset { .. }
        | VirInstruction::ResourceStorageReset { .. }
        | VirInstruction::ObjectDrop { .. }
        | VirInstruction::EnumSetDiscriminant { .. }
        | VirInstruction::Free { .. }
        | VirInstruction::LoanEnd { .. }
        | VirInstruction::LoanEndAuthority { .. }
        | VirInstruction::Check { .. } => Vec::new(),
    }
}

fn nontrivial_runtime_copy_count(
    function: &VirFunction,
    target: &VirBlockTarget,
) -> Result<usize, X86_64PlanningErrorKind> {
    let target_block = function
        .blocks
        .iter()
        .find(|block| block.id == target.block)
        .ok_or(X86_64PlanningErrorKind::MissingTargetBlock(target.block))?;
    Ok(target
        .arguments
        .iter()
        .zip(&target_block.parameters)
        .filter(|(argument, parameter)| {
            parameter.ty != VirType::Permission && **argument != parameter.id
        })
        .count())
}

struct FrameBuilder {
    used_bytes: u64,
    maximum: u64,
}

impl FrameBuilder {
    const fn new(maximum: u64) -> Self {
        Self {
            used_bytes: 0,
            maximum,
        }
    }

    fn reserve_word(&mut self) -> Result<X86_64FrameSlot, X86_64PlanningErrorKind> {
        let region = self.reserve_region(WORD_BYTES)?;
        Ok(X86_64FrameSlot {
            offset_from_rbp_bytes: region.base_offset_from_rbp_bytes,
        })
    }

    fn reserve_region(
        &mut self,
        size_bytes: u64,
    ) -> Result<X86_64FrameRegion, X86_64PlanningErrorKind> {
        self.reserve_region_aligned(size_bytes, WORD_BYTES)
    }

    fn reserve_region_aligned(
        &mut self,
        size_bytes: u64,
        alignment_bytes: u64,
    ) -> Result<X86_64FrameRegion, X86_64PlanningErrorKind> {
        let unaligned = self.used_bytes.checked_add(size_bytes).ok_or(
            X86_64PlanningErrorKind::FrameSizeExceeded {
                requested: u64::MAX,
                maximum: self.maximum,
            },
        )?;
        let requested = checked_align_up(unaligned, alignment_bytes).ok_or(
            X86_64PlanningErrorKind::FrameSizeExceeded {
                requested: u64::MAX,
                maximum: self.maximum,
            },
        )?;
        if requested > self.maximum {
            return Err(X86_64PlanningErrorKind::FrameSizeExceeded {
                requested,
                maximum: self.maximum,
            });
        }
        self.used_bytes = requested;
        let offset = i32::try_from(requested)
            .map(|offset| -offset)
            .map_err(|_| X86_64PlanningErrorKind::FrameSizeExceeded {
                requested,
                maximum: self.maximum,
            })?;
        Ok(X86_64FrameRegion {
            base_offset_from_rbp_bytes: offset,
            size_bytes,
            alignment_bytes,
        })
    }
}

const fn checked_align_up(value: u64, alignment: u64) -> Option<u64> {
    let remainder = value % alignment;
    if remainder == 0 {
        Some(value)
    } else {
        value.checked_add(alignment - remainder)
    }
}

fn function_error(function: &VirFunction, kind: X86_64PlanningErrorKind) -> X86_64PlanningError {
    X86_64PlanningError {
        kind,
        function: function.id,
        block: None,
        instruction_index: None,
        source_span: function.source_span,
    }
}

fn block_error(
    function: &VirFunction,
    block: &VirBasicBlock,
    source_span: ByteSpan,
    kind: X86_64PlanningErrorKind,
) -> X86_64PlanningError {
    X86_64PlanningError {
        kind,
        function: function.id,
        block: Some(block.id),
        instruction_index: None,
        source_span,
    }
}

fn instruction_error(
    function: &VirFunction,
    block: &VirBasicBlock,
    instruction_index: usize,
    source_span: ByteSpan,
    kind: X86_64PlanningErrorKind,
) -> X86_64PlanningError {
    X86_64PlanningError {
        kind,
        function: function.id,
        block: Some(block.id),
        instruction_index: Some(instruction_index),
        source_span,
    }
}

#[cfg(test)]
mod tests {
    use super::{FrameBuilder, X86_64PlanningErrorKind};

    #[test]
    fn frame_builder_fails_closed_at_its_limit_and_on_overflow() {
        let mut builder = FrameBuilder::new(16);
        assert!(builder.reserve_region(16).is_ok());
        assert_eq!(
            builder.reserve_word(),
            Err(X86_64PlanningErrorKind::FrameSizeExceeded {
                requested: 24,
                maximum: 16,
            })
        );

        let mut builder = FrameBuilder {
            used_bytes: u64::MAX - 3,
            maximum: u64::MAX,
        };
        assert_eq!(
            builder.reserve_word(),
            Err(X86_64PlanningErrorKind::FrameSizeExceeded {
                requested: u64::MAX,
                maximum: u64::MAX,
            })
        );
    }
}
