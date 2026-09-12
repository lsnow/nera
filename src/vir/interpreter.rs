use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

#[cfg(test)]
mod address_model_tests;
mod allocation_instance;
mod interface;
mod loan_shadow;
use interface::RuntimeResultBuffer;

use loan_shadow::{
    RuntimeLoanAccess, RuntimeLoanAccessRequest, RuntimeLoanAuthority, RuntimeLoanLimits,
    RuntimeLoanShadow,
};

use super::{
    ResolvedRuntimeVirView, SpannedVirInstruction, VirBasicBlock, VirBlockId, VirBlockTarget,
    VirConstant, VirEndianness, VirFunctionId, VirIndexBounds, VirInstruction, VirMemoryAccess,
    VirMemorySchema, VirMemoryTypeKind, VirObjectDestinationMode, VirObjectPath,
    VirObjectPathSegment, VirObjectShape, VirObjectSourceMode, VirTerminator, VirType, VirValue,
    VirValueId, VirVariantId,
};
use crate::ByteSpan;

/// Maximum enum-bearing object roots tracked in one runtime allocation.
pub const VIR_INTERPRETER_MAX_OBJECT_ROOTS: usize = 4096;

/// Maximum typed owning payloads tracked in one runtime allocation.
pub const VIR_INTERPRETER_MAX_RESOURCE_PAYLOADS: usize = 1024;

/// Maximum simultaneously live loan records in one interpreted function call.
pub const VIR_INTERPRETER_MAX_ACTIVE_LOANS: usize = 256;

/// Maximum live authority aliases retained by one interpreted loan.
pub const VIR_INTERPRETER_MAX_ALIASES_PER_LOAN: usize = 256;

/// Maximum parent chain accepted by the runtime reborrow shadow.
pub const VIR_INTERPRETER_MAX_REBORROW_DEPTH: usize = 64;

/// Resource limits for deterministic VIR execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VirInterpreterConfig {
    pub max_steps: u64,
    pub max_call_depth: u32,
    pub max_allocation_bytes: u64,
    pub max_object_effect_bytes: u64,
    pub max_active_loans: usize,
    pub max_aliases_per_loan: usize,
    pub max_reborrow_depth: usize,
}

impl Default for VirInterpreterConfig {
    fn default() -> Self {
        Self {
            max_steps: 1_000_000,
            max_call_depth: 128,
            max_allocation_bytes: 4096,
            max_object_effect_bytes: 4096,
            max_active_loans: VIR_INTERPRETER_MAX_ACTIVE_LOANS,
            max_aliases_per_loan: VIR_INTERPRETER_MAX_ALIASES_PER_LOAN,
            max_reborrow_depth: VIR_INTERPRETER_MAX_REBORROW_DEPTH,
        }
    }
}

/// Successful, explicitly unverified VIR execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirExecution {
    values: Vec<VirRuntimeValue>,
    steps: u64,
    trace: Vec<VirTraceEvent>,
}

impl VirExecution {
    #[must_use]
    pub fn values(&self) -> &[VirRuntimeValue] {
        &self.values
    }

    #[must_use]
    pub const fn steps(&self) -> u64 {
        self.steps
    }

    /// Exact runtime program points executed in order. A faulting instruction
    /// or terminator is included after it consumes its execution step.
    #[must_use]
    pub fn trace(&self) -> &[VirTraceEvent] {
        &self.trace
    }
}

/// One observable interpreter step. It contains runtime IDs only and cannot
/// name a specification entity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirTraceEvent {
    pub function: VirFunctionId,
    pub block: VirBlockId,
    pub point: VirTracePoint,
}

/// Runtime position represented by an interpreter trace event.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirTracePoint {
    Instruction(u64),
    Terminator,
}

/// Logical runtime pointer; allocation identities are never reconstructed from integers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirRuntimePointer {
    pub paths: crate::VirPointerPaths,
    pub allocation: u64,
    pub offset_bytes: u64,
    /// Canonical object type at this address; never reconstructed from bytes.
    pub access: VirMemoryAccess,
    /// Concrete slice selection calculated from actual runtime endpoints.
    /// This is observation metadata, never permission or trusted VIR input.
    pub view_range: Option<super::VirLoanRange>,
    /// Arithmetic extent only; never grants authority or proves initialization.
    pub domain: crate::VirPointerDomain<super::VirLoanRange>,
}

/// Runtime representation of a verifier-only permission token.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirRuntimePermission {
    pub allocation: u64,
    pub start_bytes: u64,
    pub end_bytes: u64,
    pub can_free_when_complete: bool,
}

/// Values observable while interpreting VIR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirRuntimeValue {
    U64(u64),
    Bool(bool),
    Pointer(VirRuntimePointer),
    Permission(VirRuntimePermission),
}

/// A deterministic interpreter failure and its originating source range.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirExecutionError {
    kind: VirExecutionErrorKind,
    source_span: ByteSpan,
    trace: Vec<VirTraceEvent>,
}

impl VirExecutionError {
    #[must_use]
    pub const fn kind(&self) -> &VirExecutionErrorKind {
        &self.kind
    }

    #[must_use]
    pub const fn source_span(&self) -> ByteSpan {
        self.source_span
    }

    /// Runtime trace through and including the faulting program point, when
    /// execution had begun.
    #[must_use]
    pub fn trace(&self) -> &[VirTraceEvent] {
        &self.trace
    }
}

/// Runtime faults, unsupported boundaries and execution-resource exhaustion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirExecutionErrorKind {
    PointerDomainViolation {
        allocation: u64,
        start_bytes: u64,
        end_bytes: u64,
    },
    StepLimitExceeded,
    CallDepthExceeded,
    EntryPointParametersUnsupported {
        count: usize,
    },
    ActiveLoanLimitExceeded {
        limit: usize,
    },
    LoanAliasLimitExceeded {
        loan: super::VirLoanId,
        limit: usize,
    },
    LoanReborrowDepthLimitExceeded {
        loan: super::VirLoanId,
        limit: usize,
    },
    LoanAlreadyDefined {
        loan: super::VirLoanId,
    },
    MissingLoan {
        loan: super::VirLoanId,
    },
    LoanMetadataMismatch {
        loan: super::VirLoanId,
    },
    LoanRangeViolation {
        loan: super::VirLoanId,
    },
    LoanConflict {
        loan: super::VirLoanId,
    },
    LoanInactive {
        loan: super::VirLoanId,
    },
    LoanParentMismatch {
        loan: super::VirLoanId,
        parent: super::VirLoanId,
    },
    LoanHasActiveChild {
        loan: super::VirLoanId,
    },
    LoanAuthorityMismatch {
        loan: super::VirLoanId,
        permission: VirValueId,
    },
    LoanAccessConflict {
        loan: super::VirLoanId,
        permission: VirValueId,
    },
    LoanNotEnded {
        loan: super::VirLoanId,
    },
    LoanAuthorityAcrossCall {
        permission: VirValueId,
    },
    UnsupportedObjectEffectType {
        access: VirMemoryAccess,
    },
    ObjectEffectSizeLimitExceeded {
        requested: u64,
        limit: u64,
    },
    ObjectRootLimitExceeded {
        allocation: u64,
        limit: usize,
    },
    ResourcePayloadLimitExceeded {
        allocation: u64,
        limit: usize,
    },
    MissingResourcePayload {
        allocation: u64,
        offset_bytes: u64,
        access: VirMemoryAccess,
    },
    AllocationContainsResourcePayload {
        allocation: u64,
    },
    InvalidRuntimeState,
    AddressTypeMismatch {
        found: VirMemoryAccess,
        expected: VirMemoryAccess,
    },
    IndexOutOfBounds {
        index: u64,
        length: u64,
    },
    InvalidSliceRange {
        start: u64,
        end: u64,
        length: u64,
    },
    AddressCalculationOverflow,
    AddressOutOfBounds {
        allocation: u64,
        offset_bytes: u64,
        object_bytes: u64,
        size_bytes: u64,
    },
    AllocationFailure {
        size_bytes: u64,
        limit_bytes: u64,
    },
    AllocationIdentityExhausted,
    UseAfterFree {
        allocation: u64,
    },
    UseAfterLifetimeEnd {
        allocation: u64,
    },
    DoubleFree {
        allocation: u64,
    },
    PointerRelationIncompatible,
    PointerDistanceNegative,
    PointerOffsetOutOfBounds {
        allocation: u64,
        offset_bytes: u64,
        size_bytes: u64,
    },
    MisalignedAccess {
        allocation: u64,
        offset_bytes: u64,
        required_alignment: u64,
    },
    OutOfBoundsAccess {
        allocation: u64,
        offset_bytes: u64,
        access_bytes: u64,
        size_bytes: u64,
    },
    UninitializedRead {
        allocation: u64,
        offset_bytes: u64,
    },
    UninitializedObjectLeaf {
        allocation: u64,
        offset_bytes: u64,
        access: VirMemoryAccess,
    },
    InactiveVariantAccess {
        allocation: u64,
        offset_bytes: u64,
        enum_access: VirMemoryAccess,
        active: VirVariantId,
        required: VirVariantId,
    },
    InvalidObjectRepresentation {
        allocation: u64,
        offset_bytes: u64,
        access: VirMemoryAccess,
    },
    OverlappingObjectTransfer {
        allocation: u64,
        destination_offset_bytes: u64,
        source_offset_bytes: u64,
        size_bytes: u64,
    },
    InitializeAlreadyInitialized {
        allocation: u64,
        offset_bytes: u64,
    },
    StoreToUninitialized {
        allocation: u64,
        offset_bytes: u64,
    },
    InvalidFree {
        allocation: u64,
        offset_bytes: u64,
    },
    PermissionAlreadyConsumed(VirValueId),
    PermissionDuplicated(VirValueId),
    PermissionMismatch {
        allocation: u64,
        permission_allocation: u64,
    },
    PermissionOutOfRange {
        start_bytes: u64,
        end_bytes: u64,
        access_start_bytes: u64,
        access_end_bytes: u64,
    },
    InvalidPermissionSplit {
        split_at_bytes: u64,
        start_bytes: u64,
        end_bytes: u64,
    },
    InvalidPermissionJoin,
    CheckFailed,
}

impl fmt::Display for VirExecutionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.kind)
    }
}

impl Error for VirExecutionError {}

impl fmt::Display for VirExecutionErrorKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PointerDomainViolation {
                allocation,
                start_bytes,
                end_bytes,
            } => write!(
                formatter,
                "address range {start_bytes}..{end_bytes} escapes pointer arithmetic domain in allocation {allocation}"
            ),
            Self::StepLimitExceeded => formatter.write_str("VIR execution step limit exceeded"),
            Self::CallDepthExceeded => formatter.write_str("VIR call depth limit exceeded"),
            Self::EntryPointParametersUnsupported { count } => write!(
                formatter,
                "VIR entry function has {count} parameters; source execution requires a zero-parameter entry"
            ),
            Self::ActiveLoanLimitExceeded { limit } => write!(
                formatter,
                "runtime loan shadow exceeds its limit of {limit} active loans"
            ),
            Self::LoanAliasLimitExceeded { loan, limit } => write!(
                formatter,
                "loan{} exceeds its runtime limit of {limit} active aliases",
                loan.get()
            ),
            Self::LoanReborrowDepthLimitExceeded { loan, limit } => write!(
                formatter,
                "loan{} exceeds its runtime reborrow depth limit of {limit}",
                loan.get()
            ),
            Self::LoanAlreadyDefined { loan } => {
                write!(
                    formatter,
                    "loan{} was already defined in this call",
                    loan.get()
                )
            }
            Self::MissingLoan { loan } => {
                write!(formatter, "loan{} has no runtime shadow record", loan.get())
            }
            Self::LoanMetadataMismatch { loan } => write!(
                formatter,
                "loan{} effect disagrees with its runtime shadow metadata",
                loan.get()
            ),
            Self::LoanRangeViolation { loan } => write!(
                formatter,
                "loan{} range is not covered by its runtime pointer and permission",
                loan.get()
            ),
            Self::LoanConflict { loan } => write!(
                formatter,
                "loan{} conflicts with an active runtime loan",
                loan.get()
            ),
            Self::LoanInactive { loan } => {
                write!(formatter, "loan{} is not active", loan.get())
            }
            Self::LoanParentMismatch { loan, parent } => write!(
                formatter,
                "loan{} is not authorized by parent loan{}",
                loan.get(),
                parent.get()
            ),
            Self::LoanHasActiveChild { loan } => write!(
                formatter,
                "loan{} still has an active child loan",
                loan.get()
            ),
            Self::LoanAuthorityMismatch { loan, permission } => write!(
                formatter,
                "permission %{} is not a live authority for loan{}",
                permission.get(),
                loan.get()
            ),
            Self::LoanAccessConflict { loan, permission } => write!(
                formatter,
                "permission %{} cannot access memory protected by loan{}",
                permission.get(),
                loan.get()
            ),
            Self::LoanNotEnded { loan } => write!(
                formatter,
                "loan{} is still live when its function returns",
                loan.get()
            ),
            Self::LoanAuthorityAcrossCall { permission } => write!(
                formatter,
                "permission %{} carries a loan authority across an unsupported call boundary",
                permission.get()
            ),
            Self::UnsupportedObjectEffectType { access } => write!(
                formatter,
                "object effect for type{}/layout{} has no runtime representation",
                access.ty.get(),
                access.layout.get()
            ),
            Self::ObjectEffectSizeLimitExceeded { requested, limit } => write!(
                formatter,
                "object effect requires {requested} bytes; interpreter limit is {limit}"
            ),
            Self::ObjectRootLimitExceeded { allocation, limit } => write!(
                formatter,
                "allocation {allocation} exceeds the interpreter limit of {limit} tracked enum object roots"
            ),
            Self::ResourcePayloadLimitExceeded { allocation, limit } => write!(
                formatter,
                "allocation {allocation} exceeds the interpreter limit of {limit} typed resource payloads"
            ),
            Self::MissingResourcePayload {
                allocation,
                offset_bytes,
                access,
            } => write!(
                formatter,
                "resource type{}/layout{} at byte {offset_bytes} of allocation {allocation} has no available typed payload",
                access.ty.get(),
                access.layout.get()
            ),
            Self::AllocationContainsResourcePayload { allocation } => write!(
                formatter,
                "allocation {allocation} still contains an owning resource payload"
            ),
            Self::InvalidRuntimeState => formatter.write_str("invalid VIR runtime state"),
            Self::AddressTypeMismatch { found, expected } => write!(
                formatter,
                "address has type{}/layout{}; expected type{}/layout{}",
                found.ty.get(),
                found.layout.get(),
                expected.ty.get(),
                expected.layout.get()
            ),
            Self::IndexOutOfBounds { index, length } => {
                write!(formatter, "index {index} is outside array length {length}")
            }
            Self::InvalidSliceRange { start, end, length } => write!(
                formatter,
                "slice range {start}..{end} is outside source length {length}"
            ),
            Self::AddressCalculationOverflow => {
                formatter.write_str("field/index address calculation overflowed u64")
            }
            Self::AddressOutOfBounds {
                allocation,
                offset_bytes,
                object_bytes,
                size_bytes,
            } => write!(
                formatter,
                "{object_bytes}-byte object at byte {offset_bytes} is outside allocation {allocation} of {size_bytes} bytes"
            ),
            Self::AllocationFailure {
                size_bytes,
                limit_bytes,
            } => write!(
                formatter,
                "cannot allocate {size_bytes} bytes (per-allocation limit is {limit_bytes})"
            ),
            Self::AllocationIdentityExhausted => {
                formatter.write_str("VIR allocation identity space exhausted")
            }
            Self::UseAfterFree { allocation } => {
                write!(formatter, "use after free of allocation {allocation}")
            }
            Self::UseAfterLifetimeEnd { allocation } => {
                write!(
                    formatter,
                    "use after function-local lifetime of allocation {allocation}"
                )
            }
            Self::DoubleFree { allocation } => {
                write!(formatter, "double free of allocation {allocation}")
            }
            Self::PointerRelationIncompatible => write!(
                formatter,
                "pointer relation requires the same live instance and canonical domain"
            ),
            Self::PointerDistanceNegative => write!(formatter, "pointer byte distance is negative"),
            Self::PointerOffsetOutOfBounds {
                allocation,
                offset_bytes,
                size_bytes,
            } => write!(
                formatter,
                "pointer offset {offset_bytes} is outside allocation {allocation} of {size_bytes} bytes"
            ),
            Self::MisalignedAccess {
                allocation,
                offset_bytes,
                required_alignment,
            } => write!(
                formatter,
                "access at byte {offset_bytes} of allocation {allocation} is not aligned to {required_alignment} bytes"
            ),
            Self::OutOfBoundsAccess {
                allocation,
                offset_bytes,
                access_bytes,
                size_bytes,
            } => write!(
                formatter,
                "{access_bytes}-byte access at byte {offset_bytes} is outside allocation {allocation} of {size_bytes} bytes"
            ),
            Self::UninitializedRead {
                allocation,
                offset_bytes,
            } => write!(
                formatter,
                "read of uninitialized byte {offset_bytes} in allocation {allocation}"
            ),
            Self::UninitializedObjectLeaf {
                allocation,
                offset_bytes,
                access,
            } => write!(
                formatter,
                "object type{}/layout{} reads uninitialized byte {offset_bytes} in allocation {allocation}",
                access.ty.get(),
                access.layout.get()
            ),
            Self::InactiveVariantAccess {
                allocation,
                offset_bytes,
                enum_access,
                active,
                required,
            } => write!(
                formatter,
                "access at byte {offset_bytes} of allocation {allocation} requires variant{} of enum type{}/layout{}, but variant{} is active",
                required.get(),
                enum_access.ty.get(),
                enum_access.layout.get(),
                active.get()
            ),
            Self::InvalidObjectRepresentation {
                allocation,
                offset_bytes,
                access,
            } => write!(
                formatter,
                "invalid representation for type{}/layout{} at byte {offset_bytes} of allocation {allocation}",
                access.ty.get(),
                access.layout.get()
            ),
            Self::OverlappingObjectTransfer {
                allocation,
                destination_offset_bytes,
                source_offset_bytes,
                size_bytes,
            } => write!(
                formatter,
                "{size_bytes}-byte object transfer overlaps within allocation {allocation}: destination byte {destination_offset_bytes}, source byte {source_offset_bytes}"
            ),
            Self::InitializeAlreadyInitialized {
                allocation,
                offset_bytes,
            } => write!(
                formatter,
                "initialize targets initialized byte {offset_bytes} in allocation {allocation}"
            ),
            Self::StoreToUninitialized {
                allocation,
                offset_bytes,
            } => write!(
                formatter,
                "store targets uninitialized byte {offset_bytes} in allocation {allocation}"
            ),
            Self::InvalidFree {
                allocation,
                offset_bytes,
            } => write!(
                formatter,
                "invalid free at byte {offset_bytes} of allocation {allocation}"
            ),
            Self::PermissionAlreadyConsumed(value) => {
                write!(
                    formatter,
                    "permission %{} was already consumed",
                    value.get()
                )
            }
            Self::PermissionDuplicated(value) => {
                write!(
                    formatter,
                    "permission %{} is transferred more than once",
                    value.get()
                )
            }
            Self::PermissionMismatch {
                allocation,
                permission_allocation,
            } => write!(
                formatter,
                "allocation {allocation} is accessed with permission for allocation {permission_allocation}"
            ),
            Self::PermissionOutOfRange {
                start_bytes,
                end_bytes,
                access_start_bytes,
                access_end_bytes,
            } => write!(
                formatter,
                "permission [{start_bytes}, {end_bytes}) does not cover access [{access_start_bytes}, {access_end_bytes})"
            ),
            Self::InvalidPermissionSplit {
                split_at_bytes,
                start_bytes,
                end_bytes,
            } => write!(
                formatter,
                "permission [{start_bytes}, {end_bytes}) cannot be split at byte {split_at_bytes}"
            ),
            Self::InvalidPermissionJoin => {
                formatter.write_str("permissions are not adjacent parts of one allocation")
            }
            Self::CheckFailed => formatter.write_str("VIR runtime check failed"),
        }
    }
}

/// Executes resolved VIR with deterministic default limits.
pub fn interpret(program: &ResolvedRuntimeVirView<'_>) -> Result<VirExecution, VirExecutionError> {
    interpret_with_config(program, VirInterpreterConfig::default())
}

/// Executes resolved VIR with caller-selected limits.
pub fn interpret_with_config(
    program: &ResolvedRuntimeVirView<'_>,
    config: VirInterpreterConfig,
) -> Result<VirExecution, VirExecutionError> {
    Interpreter::new(config).run(program)
}

#[derive(Clone, Debug)]
struct Allocation {
    size_bytes: u64,
    alignment: u64,
    kind: RuntimeAllocationKind,
    live: bool,
    bytes: BTreeMap<u64, u8>,
    objects: Vec<RuntimeObject>,
    resource_payloads: BTreeMap<RuntimeResourcePayloadKey, RuntimeOwnedPayload>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct RuntimeResourcePayloadKey {
    offset_bytes: u64,
    access: VirMemoryAccess,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RuntimeOwnedPayload {
    pointer: VirRuntimePointer,
    permission: VirRuntimePermission,
    loan_authority: Option<RuntimeLoanAuthority>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RuntimeObject {
    offset_bytes: u64,
    access: VirMemoryAccess,
}

#[derive(Clone, Copy, Debug)]
enum RuntimeAllocationKind {
    Heap,
    LocalStorage,
}

struct BlockFrame {
    values: BTreeMap<VirValueId, VirRuntimeValue>,
    consumed_permissions: BTreeSet<VirValueId>,
    loan_authorities: BTreeMap<VirValueId, RuntimeLoanAuthority>,
}

struct RuntimeBlockArgument {
    value: VirRuntimeValue,
    permission_consumed: bool,
    loan_authority: Option<RuntimeLoanAuthority>,
}

struct CallReturn {
    results: Vec<VirValue>,
    loan_authorities: Vec<loan_shadow::RuntimeBorrowReturn>,
    source_span: ByteSpan,
}

struct FunctionFrame {
    function: VirFunctionId,
    block: VirBlockId,
    block_frame: BlockFrame,
    next_instruction: usize,
    call_return: Option<CallReturn>,
    local_allocations: Vec<u64>,
    loan_shadow: RuntimeLoanShadow,
    result_buffers: Vec<RuntimeResultBuffer>,
}

impl BlockFrame {
    fn new(
        block: &VirBasicBlock,
        arguments: Vec<VirRuntimeValue>,
        source_span: ByteSpan,
    ) -> Result<Self, VirExecutionError> {
        Self::from_block_arguments(
            block,
            arguments
                .into_iter()
                .map(|value| RuntimeBlockArgument {
                    value,
                    permission_consumed: false,
                    loan_authority: None,
                })
                .collect(),
            source_span,
        )
    }

    fn from_block_arguments(
        block: &VirBasicBlock,
        arguments: Vec<RuntimeBlockArgument>,
        source_span: ByteSpan,
    ) -> Result<Self, VirExecutionError> {
        if block.parameters.len() != arguments.len() {
            return Err(error(
                VirExecutionErrorKind::InvalidRuntimeState,
                source_span,
            ));
        }
        let mut values = BTreeMap::new();
        let mut consumed_permissions = BTreeSet::new();
        let mut loan_authorities = BTreeMap::new();
        for (parameter, argument) in block.parameters.iter().zip(arguments) {
            let RuntimeBlockArgument {
                value,
                permission_consumed,
                loan_authority,
            } = argument;
            let is_permission = matches!(value, VirRuntimeValue::Permission(_));
            if !runtime_matches_type(&value, parameter.ty)
                || (permission_consumed && !is_permission)
                || values.insert(parameter.id, value).is_some()
            {
                return Err(error(
                    VirExecutionErrorKind::InvalidRuntimeState,
                    source_span,
                ));
            }
            if permission_consumed {
                consumed_permissions.insert(parameter.id);
            }
            if let Some(authority) = loan_authority {
                if !is_permission || permission_consumed {
                    return Err(error(
                        VirExecutionErrorKind::InvalidRuntimeState,
                        source_span,
                    ));
                }
                loan_authorities.insert(parameter.id, authority);
            }
        }
        Ok(Self {
            values,
            consumed_permissions,
            loan_authorities,
        })
    }

    fn value(
        &self,
        id: VirValueId,
        source_span: ByteSpan,
    ) -> Result<&VirRuntimeValue, VirExecutionError> {
        self.values
            .get(&id)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))
    }

    fn insert(
        &mut self,
        declaration: VirValue,
        value: VirRuntimeValue,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        if !runtime_matches_type(&value, declaration.ty)
            || self.values.insert(declaration.id, value).is_some()
        {
            return Err(error(
                VirExecutionErrorKind::InvalidRuntimeState,
                source_span,
            ));
        }
        Ok(())
    }

    fn permission(
        &self,
        id: VirValueId,
        source_span: ByteSpan,
    ) -> Result<VirRuntimePermission, VirExecutionError> {
        if self.consumed_permissions.contains(&id) {
            return Err(error(
                VirExecutionErrorKind::PermissionAlreadyConsumed(id),
                source_span,
            ));
        }
        let VirRuntimeValue::Permission(permission) = self.value(id, source_span)? else {
            return Err(error(
                VirExecutionErrorKind::InvalidRuntimeState,
                source_span,
            ));
        };
        Ok(*permission)
    }

    fn active_values(
        &self,
        ids: &[VirValueId],
        source_span: ByteSpan,
    ) -> Result<Vec<VirRuntimeValue>, VirExecutionError> {
        let mut transferred_permissions = BTreeSet::new();
        ids.iter()
            .map(|id| {
                let value = self.value(*id, source_span)?.clone();
                if matches!(value, VirRuntimeValue::Permission(_)) {
                    self.permission(*id, source_span)?;
                    if !transferred_permissions.insert(*id) {
                        return Err(error(
                            VirExecutionErrorKind::PermissionDuplicated(*id),
                            source_span,
                        ));
                    }
                }
                Ok(value)
            })
            .collect()
    }

    fn move_call_arguments(
        &mut self,
        ids: &[VirValueId],
        source_span: ByteSpan,
    ) -> Result<Vec<VirRuntimeValue>, VirExecutionError> {
        let values = self.active_values(ids, source_span)?;
        for (id, value) in ids.iter().zip(&values) {
            if matches!(value, VirRuntimeValue::Permission(_)) {
                self.consume_permission(*id, source_span)?;
            }
        }
        Ok(values)
    }

    fn consume_permission(
        &mut self,
        id: VirValueId,
        source_span: ByteSpan,
    ) -> Result<VirRuntimePermission, VirExecutionError> {
        let permission = self.permission(id, source_span)?;
        self.consumed_permissions.insert(id);
        Ok(permission)
    }

    fn loan_authority(&self, id: VirValueId) -> Option<RuntimeLoanAuthority> {
        (!self.consumed_permissions.contains(&id))
            .then(|| self.loan_authorities.get(&id).copied())
            .flatten()
    }

    fn set_loan_authority(&mut self, id: VirValueId, authority: RuntimeLoanAuthority) {
        self.loan_authorities.insert(id, authority);
    }
}

struct Interpreter {
    config: VirInterpreterConfig,
    steps: u64,
    allocation_instances: allocation_instance::RuntimeInstanceSequence,
    allocations: BTreeMap<u64, Allocation>,
    trace: Vec<VirTraceEvent>,
}

impl Interpreter {
    fn new(config: VirInterpreterConfig) -> Self {
        Self {
            config,
            steps: 0,
            allocation_instances: allocation_instance::RuntimeInstanceSequence::default(),
            allocations: BTreeMap::new(),
            trace: Vec::new(),
        }
    }

    fn run(
        mut self,
        program: &ResolvedRuntimeVirView<'_>,
    ) -> Result<VirExecution, VirExecutionError> {
        let result = self.run_inner(program);
        match result {
            Ok(execution) => Ok(execution),
            Err(mut error) => {
                error.trace = self.trace;
                Err(error)
            }
        }
    }

    fn run_inner(
        &mut self,
        program: &ResolvedRuntimeVirView<'_>,
    ) -> Result<VirExecution, VirExecutionError> {
        let entry = program.entry;
        let entry_function = program
            .function(entry)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, empty_span()))?;
        if !entry_function.signature.parameters.is_empty() {
            return Err(error(
                VirExecutionErrorKind::EntryPointParametersUnsupported {
                    count: entry_function.signature.parameters.len(),
                },
                entry_function.source_span,
            ));
        }
        let mut stack = vec![new_function_frame(
            program,
            entry,
            Vec::new(),
            None,
            entry_function.source_span,
        )?];
        loop {
            let frame_index = stack
                .len()
                .checked_sub(1)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, empty_span()))?;
            let function_id = stack[frame_index].function;
            let block_id = stack[frame_index].block;
            let function = program
                .function(function_id)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, empty_span()))?;
            let block = program.block(function_id, block_id).ok_or_else(|| {
                error(
                    VirExecutionErrorKind::InvalidRuntimeState,
                    function.source_span,
                )
            })?;

            let instruction_index = stack[frame_index].next_instruction;
            if let Some(spanned) = block.instructions.get(instruction_index) {
                self.charge_step(spanned.source_span)?;
                self.trace.push(VirTraceEvent {
                    function: function_id,
                    block: block_id,
                    point: VirTracePoint::Instruction(instruction_index as u64),
                });
                if let VirInstruction::Call {
                    results,
                    target,
                    arguments,
                } = &spanned.instruction
                {
                    if stack.len() > self.config.max_call_depth as usize {
                        return Err(error(
                            VirExecutionErrorKind::CallDepthExceeded,
                            spanned.source_span,
                        ));
                    }
                    let callee = program.call_function(target).ok_or_else(|| {
                        error(
                            VirExecutionErrorKind::InvalidRuntimeState,
                            spanned.source_span,
                        )
                    })?;
                    let frame = &mut stack[frame_index];
                    if let Some(abi) = &target.abi {
                        self.check_interface_inputs(
                            program.memory,
                            &frame.block_frame,
                            arguments,
                            abi,
                            spanned.source_span,
                        )?;
                        for (index, binding) in abi
                            .parameters()
                            .iter()
                            .enumerate()
                            .filter(|(_, binding)| binding.interface().transfer.is_borrow())
                        {
                            let permission =
                                arguments[*binding.parameter_slots().last().ok_or_else(|| {
                                    error(
                                        VirExecutionErrorKind::InvalidRuntimeState,
                                        spanned.source_span,
                                    )
                                })? as usize];
                            let imported = program.borrows.regions().iter().any(|region| {
                                region.owner == callee.id
                                    && region.origin
                                        == crate::VirBorrowRegionOrigin::Parameter {
                                            index: index as u32,
                                        }
                            });
                            if frame.block_frame.loan_authority(permission).is_some() != imported {
                                return Err(error(
                                    VirExecutionErrorKind::LoanAuthorityAcrossCall { permission },
                                    spanned.source_span,
                                ));
                            }
                        }
                    }
                    let limits = RuntimeLoanLimits {
                        active_loans: self.config.max_active_loans,
                        aliases_per_loan: self.config.max_aliases_per_loan,
                        reborrow_depth: self.config.max_reborrow_depth,
                    };
                    let loan_authorities = frame.loan_shadow.prepare_call(
                        &frame.block_frame,
                        arguments,
                        results,
                        target.abi.as_ref(),
                        limits,
                        spanned.source_span,
                    )?;
                    let arguments = stack[frame_index]
                        .block_frame
                        .move_call_arguments(arguments, spanned.source_span)?;
                    stack[frame_index].next_instruction += 1;
                    let mut callee_frame = new_function_frame(
                        program,
                        callee.id,
                        arguments,
                        Some(CallReturn {
                            results: results.clone(),
                            loan_authorities,
                            source_span: spanned.source_span,
                        }),
                        spanned.source_span,
                    )?;
                    if target.abi.is_some() {
                        callee_frame.loan_shadow.import_parameters(
                            &mut callee_frame.block_frame,
                            callee,
                            program.as_runtime(),
                            limits,
                            spanned.source_span,
                        )?;
                    }
                    stack.push(callee_frame);
                } else {
                    let frame = &mut stack[frame_index];
                    let FunctionFrame {
                        block_frame,
                        local_allocations,
                        loan_shadow,
                        ..
                    } = frame;
                    self.execute_instruction(
                        **program,
                        block_frame,
                        local_allocations,
                        loan_shadow,
                        spanned,
                    )?;
                    stack[frame_index].next_instruction += 1;
                }
                continue;
            }

            self.charge_step(block.terminator.source_span)?;
            self.trace.push(VirTraceEvent {
                function: function_id,
                block: block_id,
                point: VirTracePoint::Terminator,
            });
            match &block.terminator.terminator {
                VirTerminator::Jump { target } => {
                    let (next_block, arguments) = transfer_target(
                        &stack[frame_index].block_frame,
                        target,
                        block.terminator.source_span,
                    )?;
                    enter_block(
                        program,
                        &mut stack[frame_index],
                        next_block,
                        arguments,
                        block.terminator.source_span,
                    )?;
                }
                VirTerminator::Branch {
                    condition,
                    then_target,
                    else_target,
                } => {
                    let condition = bool_value(
                        &stack[frame_index].block_frame,
                        *condition,
                        block.terminator.source_span,
                    )?;
                    let target = if condition { then_target } else { else_target };
                    let (next_block, arguments) = transfer_target(
                        &stack[frame_index].block_frame,
                        target,
                        block.terminator.source_span,
                    )?;
                    enter_block(
                        program,
                        &mut stack[frame_index],
                        next_block,
                        arguments,
                        block.terminator.source_span,
                    )?;
                }
                VirTerminator::Return { values } => {
                    let frame = &mut stack[frame_index];
                    let abi = &program
                        .abis
                        .function(function_id)
                        .ok_or_else(|| {
                            error(
                                VirExecutionErrorKind::InvalidRuntimeState,
                                block.terminator.source_span,
                            )
                        })?
                        .signature;
                    self.check_interface_outputs(
                        program.memory,
                        frame,
                        values,
                        abi,
                        block.terminator.source_span,
                    )?;
                    frame.loan_shadow.export_parameters(
                        &frame.block_frame,
                        values,
                        abi,
                        block.terminator.source_span,
                    )?;
                    stack[frame_index]
                        .loan_shadow
                        .finish(block.terminator.source_span)?;
                    let returned_authorities = values
                        .iter()
                        .map(|value| {
                            stack[frame_index]
                                .block_frame
                                .loan_authority(*value)
                                .map(|authority| {
                                    stack[frame_index]
                                        .loan_shadow
                                        .root_loan(authority.loan, block.terminator.source_span)
                                })
                                .transpose()
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let values = stack[frame_index]
                        .block_frame
                        .active_values(values, block.terminator.source_span)?;
                    if !runtime_values_match(&values, &function.signature.results) {
                        return Err(error(
                            VirExecutionErrorKind::InvalidRuntimeState,
                            block.terminator.source_span,
                        ));
                    }
                    let completed = stack.pop().ok_or_else(|| {
                        error(
                            VirExecutionErrorKind::InvalidRuntimeState,
                            block.terminator.source_span,
                        )
                    })?;
                    for allocation in &completed.local_allocations {
                        if self
                            .allocations
                            .get(allocation)
                            .is_some_and(|storage| !storage.resource_payloads.is_empty())
                        {
                            return Err(error(
                                VirExecutionErrorKind::AllocationContainsResourcePayload {
                                    allocation: *allocation,
                                },
                                block.terminator.source_span,
                            ));
                        }
                        self.allocations
                            .get_mut(allocation)
                            .ok_or_else(|| {
                                error(
                                    VirExecutionErrorKind::InvalidRuntimeState,
                                    block.terminator.source_span,
                                )
                            })?
                            .live = false;
                    }
                    let Some(call_return) = completed.call_return else {
                        if !stack.is_empty() {
                            return Err(error(
                                VirExecutionErrorKind::InvalidRuntimeState,
                                block.terminator.source_span,
                            ));
                        }
                        return Ok(VirExecution {
                            values,
                            steps: self.steps,
                            trace: std::mem::take(&mut self.trace),
                        });
                    };
                    let caller = stack.last_mut().ok_or_else(|| {
                        error(
                            VirExecutionErrorKind::InvalidRuntimeState,
                            call_return.source_span,
                        )
                    })?;
                    if call_return.results.len() != values.len() {
                        return Err(error(
                            VirExecutionErrorKind::InvalidRuntimeState,
                            call_return.source_span,
                        ));
                    }
                    for (result, value) in call_return.results.iter().zip(values) {
                        caller
                            .block_frame
                            .insert(*result, value, call_return.source_span)?;
                    }
                    for restored in call_return.loan_authorities {
                        let returned_permission = restored
                            .callee_loan
                            .and_then(|_| {
                                caller
                                    .block_frame
                                    .permission(restored.value, call_return.source_span)
                                    .ok()
                            })
                            .unwrap_or(restored.permission);
                        let authority = if let Some(expected) = restored.callee_loan {
                            let Some(index) = call_return
                                .results
                                .iter()
                                .position(|result| result.id == restored.value)
                            else {
                                return Err(error(
                                    VirExecutionErrorKind::InvalidRuntimeState,
                                    call_return.source_span,
                                ));
                            };
                            if returned_authorities.get(index).copied().flatten() != Some(expected)
                            {
                                continue;
                            }
                            caller.loan_shadow.activate_conditional_return(
                                restored.authority,
                                restored.projected_pointee,
                                returned_permission,
                                RuntimeLoanLimits {
                                    active_loans: self.config.max_active_loans,
                                    aliases_per_loan: self.config.max_aliases_per_loan,
                                    reborrow_depth: self.config.max_reborrow_depth,
                                },
                                call_return.source_span,
                            )?
                        } else {
                            restored.authority
                        };
                        caller.block_frame.values.insert(
                            restored.value,
                            VirRuntimeValue::Permission(returned_permission),
                        );
                        caller
                            .block_frame
                            .set_loan_authority(restored.value, authority);
                    }
                }
            }
        }
    }

    fn execute_instruction(
        &mut self,
        runtime: super::RuntimeVirView<'_>,
        frame: &mut BlockFrame,
        local_allocations: &mut Vec<u64>,
        loan_shadow: &mut RuntimeLoanShadow,
        spanned: &SpannedVirInstruction,
    ) -> Result<(), VirExecutionError> {
        let semantics = runtime.semantic_profile;
        let memory = runtime.memory;
        let span = spanned.source_span;
        let loan_limits = RuntimeLoanLimits {
            active_loans: self.config.max_active_loans,
            aliases_per_loan: self.config.max_aliases_per_loan,
            reborrow_depth: self.config.max_reborrow_depth,
        };
        check_loan_instruction_access(memory, frame, loan_shadow, &spanned.instruction, span)?;
        match &spanned.instruction {
            VirInstruction::PointerCompare {
                result,
                predicate,
                left,
                right,
            } => {
                let (a, b) = self.pointer_pair(frame, *left, *right, span)?;
                frame.insert(
                    *result,
                    VirRuntimeValue::Bool(semantics.compare(
                        *predicate,
                        a.offset_bytes,
                        b.offset_bytes,
                    )),
                    span,
                )
            }
            VirInstruction::PointerDistance { result, begin, end } => {
                let (a, b) = self.pointer_pair(frame, *begin, *end, span)?;
                let distance = b
                    .offset_bytes
                    .checked_sub(a.offset_bytes)
                    .ok_or_else(|| error(VirExecutionErrorKind::PointerDistanceNegative, span))?;
                frame.insert(*result, VirRuntimeValue::U64(distance), span)
            }
            VirInstruction::Constant { result, value } => {
                let value = match value {
                    VirConstant::U64(value) => VirRuntimeValue::U64(*value),
                    VirConstant::Bool(value) => VirRuntimeValue::Bool(*value),
                };
                frame.insert(*result, value, span)
            }
            VirInstruction::WordAdd {
                result,
                left,
                right,
            } => {
                let left = word_value(frame, *left, span)?;
                let right = word_value(frame, *right, span)?;
                frame.insert(
                    *result,
                    VirRuntimeValue::U64(semantics.word_add(left, right)),
                    span,
                )
            }
            VirInstruction::Compare {
                result,
                predicate,
                left,
                right,
            } => {
                let left = word_value(frame, *left, span)?;
                let right = word_value(frame, *right, span)?;
                let comparison = semantics.compare(*predicate, left, right);
                frame.insert(*result, VirRuntimeValue::Bool(comparison), span)
            }
            VirInstruction::Allocate {
                pointer_result,
                permission_result,
                size_bytes,
                alignment,
                element,
                ..
            } => {
                let size_bytes = word_value(frame, *size_bytes, span)?;
                if size_bytes == 0 || size_bytes > self.config.max_allocation_bytes {
                    return Err(error(
                        VirExecutionErrorKind::AllocationFailure {
                            size_bytes,
                            limit_bytes: self.config.max_allocation_bytes,
                        },
                        span,
                    ));
                }
                let allocation = self.allocation_instances.fresh().ok_or_else(|| {
                    error(VirExecutionErrorKind::AllocationIdentityExhausted, span)
                })?;
                let shape = memory
                    .object_shape(*element)
                    .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                let objects = repeated_runtime_objects(
                    *element,
                    shape.size_bytes(),
                    size_bytes,
                    !shape.variants().is_empty(),
                );
                if objects.len() > VIR_INTERPRETER_MAX_OBJECT_ROOTS {
                    return Err(error(
                        VirExecutionErrorKind::ObjectRootLimitExceeded {
                            allocation,
                            limit: VIR_INTERPRETER_MAX_OBJECT_ROOTS,
                        },
                        span,
                    ));
                }
                if self
                    .allocations
                    .insert(
                        allocation,
                        Allocation {
                            size_bytes,
                            alignment: *alignment,
                            kind: RuntimeAllocationKind::Heap,
                            live: true,
                            bytes: BTreeMap::new(),
                            objects,
                            resource_payloads: BTreeMap::new(),
                        },
                    )
                    .is_some()
                {
                    return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
                }
                frame.insert(
                    *pointer_result,
                    VirRuntimeValue::Pointer(VirRuntimePointer {
                        allocation,
                        offset_bytes: 0,
                        access: *element,
                        paths: crate::VirPointerPaths::root(*element),
                        view_range: None,
                        domain: crate::VirPointerDomain::Allocation,
                    }),
                    span,
                )?;
                frame.insert(
                    *permission_result,
                    VirRuntimeValue::Permission(VirRuntimePermission {
                        allocation,
                        start_bytes: 0,
                        end_bytes: size_bytes,
                        can_free_when_complete: true,
                    }),
                    span,
                )
            }
            VirInstruction::LocalStorage {
                pointer_result,
                permission_result,
                access,
            } => {
                let shape = memory
                    .object_shape(*access)
                    .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                let size_bytes = shape.size_bytes();
                debug_assert_ne!(size_bytes, 0);
                let allocation = self.allocation_instances.fresh().ok_or_else(|| {
                    error(VirExecutionErrorKind::AllocationIdentityExhausted, span)
                })?;
                if self
                    .allocations
                    .insert(
                        allocation,
                        Allocation {
                            size_bytes,
                            alignment: shape.alignment(),
                            kind: RuntimeAllocationKind::LocalStorage,
                            live: true,
                            bytes: BTreeMap::new(),
                            objects: (!shape.variants().is_empty())
                                .then_some(RuntimeObject {
                                    offset_bytes: 0,
                                    access: *access,
                                })
                                .into_iter()
                                .collect(),
                            resource_payloads: BTreeMap::new(),
                        },
                    )
                    .is_some()
                {
                    return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
                }
                local_allocations.push(allocation);
                frame.insert(
                    *pointer_result,
                    VirRuntimeValue::Pointer(VirRuntimePointer {
                        allocation,
                        offset_bytes: 0,
                        access: *access,
                        paths: crate::VirPointerPaths::root(*access),
                        view_range: None,
                        domain: crate::VirPointerDomain::Allocation,
                    }),
                    span,
                )?;
                frame.insert(
                    *permission_result,
                    VirRuntimeValue::Permission(VirRuntimePermission {
                        allocation,
                        start_bytes: 0,
                        end_bytes: size_bytes,
                        can_free_when_complete: false,
                    }),
                    span,
                )
            }
            VirInstruction::Initialize {
                pointer,
                value,
                permission,
                access,
            } => {
                let pointer = pointer_value(frame, *pointer, span)?;
                let value = scalar_value(memory, frame, *value, *access, span)?;
                self.live_allocation(pointer.allocation, span)?;
                let permission = frame.permission(*permission, span)?;
                self.write_memory(
                    pointer,
                    permission,
                    value,
                    WriteKind::Initialize,
                    MemoryAccessContext::new(memory, *access, span),
                )
            }
            VirInstruction::Write {
                pointer,
                value,
                permission,
                access,
            } => {
                let pointer = pointer_value(frame, *pointer, span)?;
                let value = scalar_value(memory, frame, *value, *access, span)?;
                self.live_allocation(pointer.allocation, span)?;
                let permission = frame.permission(*permission, span)?;
                self.write_memory(
                    pointer,
                    permission,
                    value,
                    WriteKind::Write,
                    MemoryAccessContext::new(memory, *access, span),
                )
            }
            VirInstruction::Load {
                result,
                pointer,
                permission,
                access,
            } => {
                let pointer = pointer_value(frame, *pointer, span)?;
                self.live_allocation(pointer.allocation, span)?;
                let permission = frame.permission(*permission, span)?;
                let value = self.load_memory(
                    pointer,
                    permission,
                    MemoryAccessContext::new(memory, *access, span),
                )?;
                let value = match memory.kind(access.ty) {
                    Some(VirMemoryTypeKind::Bool) => VirRuntimeValue::Bool(value != 0),
                    Some(VirMemoryTypeKind::Integer(
                        super::VirIntegerType::U64 | super::VirIntegerType::Usize,
                    )) => VirRuntimeValue::U64(value),
                    _ => return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span)),
                };
                frame.insert(*result, value, span)
            }
            VirInstruction::EnumDiscriminant {
                result,
                pointer,
                permission,
                access,
            } => {
                let pointer = pointer_value(frame, *pointer, span)?;
                let permission = frame.permission(*permission, span)?;
                let discriminant =
                    self.enum_discriminant(memory, pointer, permission, *access, span)?;
                frame.insert(*result, VirRuntimeValue::U64(discriminant), span)
            }
            VirInstruction::Store {
                pointer,
                value,
                permission,
                access,
            } => {
                let pointer = pointer_value(frame, *pointer, span)?;
                let value = scalar_value(memory, frame, *value, *access, span)?;
                self.live_allocation(pointer.allocation, span)?;
                let permission = frame.permission(*permission, span)?;
                self.write_memory(
                    pointer,
                    permission,
                    value,
                    WriteKind::Store,
                    MemoryAccessContext::new(memory, *access, span),
                )
            }
            VirInstruction::ResourceInitialize {
                destination,
                destination_permission,
                value,
                value_permission,
                access,
            } => {
                let loan_authority = frame.loan_authority(*value_permission);
                let destination = pointer_value(frame, *destination, span)?;
                let destination_permission = frame.permission(*destination_permission, span)?;
                let value = pointer_value(frame, *value, span)?;
                let stored_permission = frame.permission(*value_permission, span)?;
                self.resource_initialize(
                    memory,
                    destination,
                    destination_permission,
                    value,
                    stored_permission,
                    loan_authority,
                    *access,
                    span,
                )?;
                frame.consume_permission(*value_permission, span)?;
                Ok(())
            }
            VirInstruction::ResourceTake {
                pointer_result,
                permission_result,
                source,
                source_permission,
                access,
            } => {
                let source = pointer_value(frame, *source, span)?;
                let source_permission = frame.permission(*source_permission, span)?;
                let payload =
                    self.resource_take(memory, source, source_permission, *access, span)?;
                frame.insert(
                    *pointer_result,
                    VirRuntimeValue::Pointer(payload.pointer),
                    span,
                )?;
                frame.insert(
                    *permission_result,
                    VirRuntimeValue::Permission(payload.permission),
                    span,
                )?;
                if let Some(authority) = payload.loan_authority {
                    frame.set_loan_authority(permission_result.id, authority);
                }
                Ok(())
            }
            VirInstruction::DropOwn {
                pointer,
                permission,
                condition,
            } => {
                if !bool_value(frame, *condition, span)? {
                    return Ok(());
                }
                let pointer = pointer_value(frame, *pointer, span)?;
                self.ensure_not_freed(pointer.allocation, span)?;
                let permission = frame.consume_permission(*permission, span)?;
                self.free(pointer, permission, span)
            }
            VirInstruction::ObjectTransfer {
                destination,
                destination_permission,
                source,
                source_permission,
                access,
                destination_mode,
                source_mode,
            } => {
                let destination = pointer_value(frame, *destination, span)?;
                let destination_permission = frame.permission(*destination_permission, span)?;
                let source = pointer_value(frame, *source, span)?;
                let source_permission = frame.permission(*source_permission, span)?;
                self.object_transfer(
                    memory,
                    loan_shadow,
                    loan_limits,
                    destination,
                    destination_permission,
                    source,
                    source_permission,
                    *access,
                    *destination_mode,
                    *source_mode,
                    span,
                )
            }
            VirInstruction::ObjectDeinitialize {
                pointer,
                permission,
                access,
            } => {
                let pointer = pointer_value(frame, *pointer, span)?;
                let permission = frame.permission(*permission, span)?;
                self.object_deinitialize(memory, pointer, permission, *access, true, span)
            }
            VirInstruction::StorageReset {
                pointer,
                permission,
                access,
            } => {
                let pointer = pointer_value(frame, *pointer, span)?;
                let permission = frame.permission(*permission, span)?;
                self.object_deinitialize(memory, pointer, permission, *access, false, span)
            }
            VirInstruction::ResourceStorageReset {
                pointer,
                permission,
                access,
            } => {
                let pointer = pointer_value(frame, *pointer, span)?;
                let permission = frame.permission(*permission, span)?;
                self.resource_storage_reset(memory, pointer, permission, *access, span)
            }
            VirInstruction::ObjectDrop {
                pointer,
                permission,
                access,
                condition,
            } => {
                if !bool_value(frame, *condition, span)? {
                    return Ok(());
                }
                let pointer = pointer_value(frame, *pointer, span)?;
                let permission = frame.permission(*permission, span)?;
                self.object_drop(memory, loan_shadow, pointer, permission, *access, span)
            }
            VirInstruction::EnumSetDiscriminant {
                pointer,
                permission,
                access,
                variant,
                mode,
            } => {
                let pointer = pointer_value(frame, *pointer, span)?;
                let permission = frame.permission(*permission, span)?;
                self.enum_set_discriminant(
                    memory, pointer, permission, *access, *variant, *mode, span,
                )
            }
            VirInstruction::RawAddress {
                result,
                base,
                source_permission,
                raw_type,
            } => {
                let (access, _) = memory
                    .raw_address_pointee(*raw_type)
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                let pointer = pointer_value(frame, *base, span)?;
                let permission = frame.permission(*source_permission, span)?;
                self.check_access(
                    pointer,
                    permission,
                    MemoryAccessContext::new(memory, access, span),
                )?;
                frame.insert(*result, VirRuntimeValue::Pointer(pointer), span)
            }
            VirInstruction::PointerOffset {
                result,
                base,
                delta_bytes,
            } => {
                let base = pointer_value(frame, *base, span)?;
                let delta_bytes = word_value(frame, *delta_bytes, span)?;
                let allocation = self.live_allocation(base.allocation, span)?;
                let offset_bytes = semantics
                    .checked_pointer_offset(base.offset_bytes, delta_bytes, allocation.size_bytes)
                    .ok_or_else(|| {
                        error(
                            VirExecutionErrorKind::PointerOffsetOutOfBounds {
                                allocation: base.allocation,
                                offset_bytes: base.offset_bytes.saturating_add(delta_bytes),
                                size_bytes: allocation.size_bytes,
                            },
                            span,
                        )
                    })?;
                self.check_domain(base, base.offset_bytes, base.offset_bytes, span)?;
                self.check_domain(base, offset_bytes, offset_bytes, span)?;
                frame.insert(
                    *result,
                    VirRuntimeValue::Pointer(VirRuntimePointer {
                        allocation: base.allocation,
                        offset_bytes,
                        access: base.access,
                        paths: base.paths,
                        view_range: base.view_range,
                        domain: base.domain,
                    }),
                    span,
                )
            }
            VirInstruction::FieldAddress {
                result,
                base,
                owner,
                field_access,
                offset_bytes,
                field,
                ..
            } => {
                let base = pointer_value(frame, *base, span)?;
                let mut derived =
                    self.derive_address(memory, base, *owner, *field_access, *offset_bytes, span)?;
                let object = memory
                    .field_subobject(*owner, *field)
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                derived.paths = base.paths.project(&object);
                frame.insert(*result, VirRuntimeValue::Pointer(derived), span)
            }
            VirInstruction::TupleElementAddress {
                result,
                base,
                owner,
                element_access,
                offset_bytes,
                index,
                ..
            } => {
                let base = pointer_value(frame, *base, span)?;
                let mut derived = self.derive_address(
                    memory,
                    base,
                    *owner,
                    *element_access,
                    *offset_bytes,
                    span,
                )?;
                let object = memory
                    .subobject(*owner, &[crate::VirObjectPathSegment::TupleElement(*index)])
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                derived.paths = base.paths.project(&object);
                frame.insert(*result, VirRuntimeValue::Pointer(derived), span)
            }
            VirInstruction::ObjectLeafAddress {
                result,
                base,
                owner,
                leaf,
                offset_bytes,
            } => {
                let base = pointer_value(frame, *base, span)?;
                let mut derived =
                    self.derive_address(memory, base, *owner, *leaf, *offset_bytes, span)?;
                if let Some(object) = memory.leaf_subobject(*owner, *leaf, *offset_bytes) {
                    derived.paths = base.paths.project(&object);
                    derived.domain = self.selected_domain(
                        base,
                        object.domain_offset_bytes(),
                        object.domain_size_bytes(),
                        span,
                    )?;
                }
                frame.insert(*result, VirRuntimeValue::Pointer(derived), span)
            }
            VirInstruction::IndexAddress {
                result,
                base,
                index,
                source,
                element,
                stride_bytes,
                bounds: VirIndexBounds::Array { length },
            } => {
                let base = pointer_value(frame, *base, span)?;
                let index = word_value(frame, *index, span)?;
                if index >= *length {
                    return Err(error(
                        VirExecutionErrorKind::IndexOutOfBounds {
                            index,
                            length: *length,
                        },
                        span,
                    ));
                }
                let delta = index.checked_mul(*stride_bytes).ok_or_else(|| {
                    error(VirExecutionErrorKind::AddressCalculationOverflow, span)
                })?;
                let mut derived =
                    self.derive_address(memory, base, *source, *element, delta, span)?;
                derived.paths = base.paths.element();
                derived.domain = self.selected_domain(
                    base,
                    0,
                    length.checked_mul(*stride_bytes).ok_or_else(|| {
                        error(VirExecutionErrorKind::AddressCalculationOverflow, span)
                    })?,
                    span,
                )?;
                frame.insert(*result, VirRuntimeValue::Pointer(derived), span)
            }
            VirInstruction::IndexAddress {
                result,
                base,
                index,
                element,
                stride_bytes,
                bounds: VirIndexBounds::Slice { length },
                ..
            } => {
                let base = pointer_value(frame, *base, span)?;
                let index = word_value(frame, *index, span)?;
                let length = word_value(frame, *length, span)?;
                if index >= length {
                    return Err(error(
                        VirExecutionErrorKind::IndexOutOfBounds { index, length },
                        span,
                    ));
                }
                let delta = index.checked_mul(*stride_bytes).ok_or_else(|| {
                    error(VirExecutionErrorKind::AddressCalculationOverflow, span)
                })?;
                let mut derived =
                    self.derive_address(memory, base, *element, *element, delta, span)?;
                derived.domain = base.domain;
                derived.paths = base.paths;
                frame.insert(*result, VirRuntimeValue::Pointer(derived), span)
            }
            VirInstruction::SliceRange {
                pointer_result,
                length_result,
                permission_result,
                base,
                permission,
                start,
                end,
                source,
                element,
                stride_bytes,
                bounds,
                ..
            } => {
                let base = pointer_value(frame, *base, span)?;
                let start = word_value(frame, *start, span)?;
                let end = word_value(frame, *end, span)?;
                let length = match bounds {
                    VirIndexBounds::Array { length } => *length,
                    VirIndexBounds::Slice { length } => word_value(frame, *length, span)?,
                };
                if start > end || end > length {
                    return Err(error(
                        VirExecutionErrorKind::InvalidSliceRange { start, end, length },
                        span,
                    ));
                }
                let loan_authority = frame.loan_authority(*permission);
                let permission = frame.consume_permission(*permission, span)?;
                let expected_base = match bounds {
                    VirIndexBounds::Array { .. } => *source,
                    VirIndexBounds::Slice { .. } => *element,
                };
                let (pointer, permission) = self.slice_range(
                    memory,
                    base,
                    permission,
                    expected_base,
                    *element,
                    start,
                    end,
                    length,
                    *stride_bytes,
                    span,
                )?;
                frame.insert(*pointer_result, VirRuntimeValue::Pointer(pointer), span)?;
                frame.insert(*length_result, VirRuntimeValue::U64(end - start), span)?;
                frame.insert(
                    *permission_result,
                    VirRuntimeValue::Permission(permission),
                    span,
                )?;
                if let Some(authority) = loan_authority {
                    frame.set_loan_authority(permission_result.id, authority);
                }
                Ok(())
            }
            VirInstruction::SliceAddress {
                pointer_result,
                length_result,
                base,
                start,
                end,
                source,
                element,
                stride_bytes,
                bounds,
                ..
            } => {
                let base = pointer_value(frame, *base, span)?;
                let start = word_value(frame, *start, span)?;
                let end = word_value(frame, *end, span)?;
                let length = match bounds {
                    VirIndexBounds::Array { length } => *length,
                    VirIndexBounds::Slice { length } => word_value(frame, *length, span)?,
                };
                if start > end || end > length {
                    return Err(error(
                        VirExecutionErrorKind::InvalidSliceRange { start, end, length },
                        span,
                    ));
                }
                let expected_base = match bounds {
                    VirIndexBounds::Array { .. } => *source,
                    VirIndexBounds::Slice { .. } => *element,
                };
                let mut pointer = self.slice_address(
                    memory,
                    base,
                    expected_base,
                    *element,
                    start,
                    length,
                    *stride_bytes,
                    span,
                )?;
                let end_bytes = end
                    .checked_mul(*stride_bytes)
                    .and_then(|delta| base.offset_bytes.checked_add(delta))
                    .ok_or_else(|| {
                        error(VirExecutionErrorKind::AddressCalculationOverflow, span)
                    })?;
                pointer.view_range = Some(super::VirLoanRange {
                    start_bytes: pointer.offset_bytes,
                    end_bytes,
                });
                pointer.domain = crate::VirPointerDomain::Restricted(pointer.view_range.unwrap());
                frame.insert(*pointer_result, VirRuntimeValue::Pointer(pointer), span)?;
                frame.insert(*length_result, VirRuntimeValue::U64(end - start), span)
            }
            VirInstruction::Free {
                pointer,
                permission,
            } => {
                let pointer = pointer_value(frame, *pointer, span)?;
                self.ensure_not_freed(pointer.allocation, span)?;
                let permission = frame.consume_permission(*permission, span)?;
                self.free(pointer, permission, span)
            }
            VirInstruction::PermissionSplit {
                left_result,
                right_result,
                source,
                split_at_bytes,
            } => {
                let permission = frame.consume_permission(*source, span)?;
                let split_at_bytes = word_value(frame, *split_at_bytes, span)?;
                if split_at_bytes < permission.start_bytes || split_at_bytes > permission.end_bytes
                {
                    return Err(error(
                        VirExecutionErrorKind::InvalidPermissionSplit {
                            split_at_bytes,
                            start_bytes: permission.start_bytes,
                            end_bytes: permission.end_bytes,
                        },
                        span,
                    ));
                }
                frame.insert(
                    *left_result,
                    VirRuntimeValue::Permission(VirRuntimePermission {
                        end_bytes: split_at_bytes,
                        ..permission
                    }),
                    span,
                )?;
                frame.insert(
                    *right_result,
                    VirRuntimeValue::Permission(VirRuntimePermission {
                        start_bytes: split_at_bytes,
                        ..permission
                    }),
                    span,
                )
            }
            VirInstruction::PermissionJoin {
                result,
                left,
                right,
            } => {
                let left = frame.consume_permission(*left, span)?;
                let right = frame.consume_permission(*right, span)?;
                let joined = join_permissions(left, right)
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidPermissionJoin, span))?;
                frame.insert(*result, VirRuntimeValue::Permission(joined), span)
            }
            VirInstruction::PermissionMove { result, source } => {
                let loan_authority = frame.loan_authority(*source);
                let permission = frame.consume_permission(*source, span)?;
                frame.insert(*result, VirRuntimeValue::Permission(permission), span)?;
                if let Some(authority) = loan_authority {
                    frame.set_loan_authority(result.id, authority);
                }
                Ok(())
            }
            VirInstruction::LoanBegin {
                effect,
                reference_result,
                permission_result,
            } => {
                let pointer = pointer_value(frame, effect.source_pointer, span)?;
                self.live_allocation(pointer.allocation, span)?;
                let actual = self.borrow_selection(memory, pointer, effect.reference, span)?;
                loan_shadow.begin(
                    frame,
                    *effect,
                    actual,
                    *reference_result,
                    *permission_result,
                    loan_limits,
                    span,
                )?;
                self.check_borrow_value(memory, pointer, effect.reference, actual, span)
            }
            VirInstruction::LoanAliasShared {
                effect,
                reference_result,
                permission_result,
            } => {
                let pointer = pointer_value(frame, effect.source_pointer, span)?;
                self.live_allocation(pointer.allocation, span)?;
                loan_shadow.alias_shared(
                    frame,
                    *effect,
                    *reference_result,
                    *permission_result,
                    loan_limits,
                    span,
                )?;
                let permission = frame.permission(permission_result.id, span)?;
                self.check_borrow_value(
                    memory,
                    pointer,
                    effect.reference,
                    super::VirLoanRange {
                        start_bytes: permission.start_bytes,
                        end_bytes: permission.end_bytes,
                    },
                    span,
                )
            }
            VirInstruction::LoanReborrow {
                effect,
                reference_result,
                permission_result,
            } => {
                let pointer = pointer_value(frame, effect.source_pointer, span)?;
                self.live_allocation(pointer.allocation, span)?;
                let actual = self.borrow_selection(memory, pointer, effect.reference, span)?;
                loan_shadow.reborrow(
                    frame,
                    *effect,
                    actual,
                    *reference_result,
                    *permission_result,
                    loan_limits,
                    span,
                )?;
                self.check_borrow_value(memory, pointer, effect.reference, actual, span)
            }
            VirInstruction::LoanEnd { effect } => {
                let pointer = pointer_value(frame, effect.source_pointer, span)?;
                self.live_allocation(pointer.allocation, span)?;
                loan_shadow.end(frame, *effect, span)
            }
            VirInstruction::LoanAliasAuthority {
                effect,
                reference_result,
                permission_result,
            } => {
                let pointer = pointer_value(frame, effect.source_pointer, span)?;
                let permission = frame.permission(effect.source_permission, span)?;
                self.check_borrow_value(
                    memory,
                    pointer,
                    effect.reference,
                    super::VirLoanRange {
                        start_bytes: permission.start_bytes,
                        end_bytes: permission.end_bytes,
                    },
                    span,
                )?;
                loan_shadow.alias_authority(
                    frame,
                    *effect,
                    *reference_result,
                    *permission_result,
                    loan_limits,
                    span,
                )
            }
            VirInstruction::LoanEndAuthority { effect } => {
                let pointer = pointer_value(frame, effect.source_pointer, span)?;
                self.live_allocation(pointer.allocation, span)?;
                loan_shadow.end_authority(frame, *effect, span)
            }
            VirInstruction::LoanReborrowAuthority {
                loan,
                region,
                effect,
                reference_result,
                permission_result,
            } => {
                let pointer = pointer_value(frame, effect.source_pointer, span)?;
                self.live_allocation(pointer.allocation, span)?;
                let actual = self.borrow_selection(memory, pointer, effect.reference, span)?;
                let resolved = loan_shadow
                    .resolve_reborrow(frame, *loan, *region, *effect, actual, runtime, span)?;
                loan_shadow.reborrow(
                    frame,
                    resolved,
                    actual,
                    *reference_result,
                    *permission_result,
                    loan_limits,
                    span,
                )?;
                self.check_borrow_value(memory, pointer, effect.reference, actual, span)
            }
            VirInstruction::Check { condition } => {
                if bool_value(frame, *condition, span)? {
                    Ok(())
                } else {
                    Err(error(VirExecutionErrorKind::CheckFailed, span))
                }
            }
            VirInstruction::Call { .. } => {
                Err(error(VirExecutionErrorKind::InvalidRuntimeState, span))
            }
        }
    }

    fn live_allocation(
        &self,
        allocation_id: u64,
        source_span: ByteSpan,
    ) -> Result<&Allocation, VirExecutionError> {
        let allocation = self
            .allocations
            .get(&allocation_id)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        if !allocation.live {
            let kind = match allocation.kind {
                RuntimeAllocationKind::Heap => VirExecutionErrorKind::UseAfterFree {
                    allocation: allocation_id,
                },
                RuntimeAllocationKind::LocalStorage => VirExecutionErrorKind::UseAfterLifetimeEnd {
                    allocation: allocation_id,
                },
            };
            return Err(error(kind, source_span));
        }
        Ok(allocation)
    }

    fn ensure_not_freed(
        &self,
        allocation_id: u64,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let allocation = self
            .allocations
            .get(&allocation_id)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        if !allocation.live {
            let kind = match allocation.kind {
                RuntimeAllocationKind::Heap => VirExecutionErrorKind::DoubleFree {
                    allocation: allocation_id,
                },
                RuntimeAllocationKind::LocalStorage => VirExecutionErrorKind::UseAfterLifetimeEnd {
                    allocation: allocation_id,
                },
            };
            return Err(error(kind, source_span));
        }
        Ok(())
    }

    fn check_domain(
        &self,
        pointer: VirRuntimePointer,
        start_bytes: u64,
        end_bytes: u64,
        span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let size = self.live_allocation(pointer.allocation, span)?.size_bytes;
        let range = match pointer.domain {
            crate::VirPointerDomain::Allocation => Some(super::VirLoanRange {
                start_bytes: 0,
                end_bytes: size,
            }),
            crate::VirPointerDomain::Restricted(range) => Some(range),
            crate::VirPointerDomain::Unknown => None,
        };
        if range.is_some_and(|r| {
            // Validate the shadow domain itself, not just this query. A
            // corrupted wider domain must not survive an in-bounds access.
            r.end_bytes <= size
                && r.start_bytes <= start_bytes
                && start_bytes <= end_bytes
                && end_bytes <= r.end_bytes
        }) {
            Ok(())
        } else {
            Err(error(
                VirExecutionErrorKind::PointerDomainViolation {
                    allocation: pointer.allocation,
                    start_bytes,
                    end_bytes,
                },
                span,
            ))
        }
    }

    fn pointer_pair(
        &self,
        frame: &BlockFrame,
        left: VirValueId,
        right: VirValueId,
        span: ByteSpan,
    ) -> Result<(VirRuntimePointer, VirRuntimePointer), VirExecutionError> {
        let a = pointer_value(frame, left, span)?;
        let b = pointer_value(frame, right, span)?;
        self.check_domain(a, a.offset_bytes, a.offset_bytes, span)?;
        self.check_domain(b, b.offset_bytes, b.offset_bytes, span)?;
        let range = |p: VirRuntimePointer| match p.domain {
            crate::VirPointerDomain::Allocation => {
                self.allocations
                    .get(&p.allocation)
                    .map(|a| super::VirLoanRange {
                        start_bytes: 0,
                        end_bytes: a.size_bytes,
                    })
            }
            crate::VirPointerDomain::Restricted(r) => Some(r),
            crate::VirPointerDomain::Unknown => None,
        };
        if a.allocation != b.allocation
            || a.paths.domain.is_none()
            || a.paths.domain != b.paths.domain
            || range(a) != range(b)
        {
            return Err(error(
                VirExecutionErrorKind::PointerRelationIncompatible,
                span,
            ));
        }
        Ok((a, b))
    }

    fn selected_domain(
        &self,
        base: VirRuntimePointer,
        delta: u64,
        size: u64,
        span: ByteSpan,
    ) -> Result<crate::VirPointerDomain<super::VirLoanRange>, VirExecutionError> {
        let start_bytes = base
            .offset_bytes
            .checked_add(delta)
            .ok_or_else(|| error(VirExecutionErrorKind::AddressCalculationOverflow, span))?;
        let end_bytes = start_bytes
            .checked_add(size)
            .ok_or_else(|| error(VirExecutionErrorKind::AddressCalculationOverflow, span))?;
        self.check_domain(base, start_bytes, end_bytes, span)?;
        Ok(crate::VirPointerDomain::Restricted(super::VirLoanRange {
            start_bytes,
            end_bytes,
        }))
    }

    fn derive_address(
        &self,
        memory: &VirMemorySchema,
        base: VirRuntimePointer,
        source: VirMemoryAccess,
        result: VirMemoryAccess,
        delta_bytes: u64,
        source_span: ByteSpan,
    ) -> Result<VirRuntimePointer, VirExecutionError> {
        if base.access != source {
            return Err(error(
                VirExecutionErrorKind::AddressTypeMismatch {
                    found: base.access,
                    expected: source,
                },
                source_span,
            ));
        }
        self.check_object_address(memory, base, source, source_span)?;
        let offset_bytes = base.offset_bytes.checked_add(delta_bytes).ok_or_else(|| {
            error(
                VirExecutionErrorKind::AddressCalculationOverflow,
                source_span,
            )
        })?;
        let derived = VirRuntimePointer {
            allocation: base.allocation,
            offset_bytes,
            access: result,
            paths: crate::VirPointerPaths::default(),
            view_range: None,
            domain: base.domain,
        };
        self.check_object_address(memory, derived, result, source_span)?;
        Ok(VirRuntimePointer {
            domain: self.selected_domain(
                base,
                delta_bytes,
                memory.layout(result.layout).unwrap().size_bytes,
                source_span,
            )?,
            ..derived
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn slice_address(
        &self,
        memory: &VirMemorySchema,
        base: VirRuntimePointer,
        expected_base: VirMemoryAccess,
        element: VirMemoryAccess,
        start: u64,
        length: u64,
        stride_bytes: u64,
        source_span: ByteSpan,
    ) -> Result<VirRuntimePointer, VirExecutionError> {
        if base.access != expected_base {
            return Err(error(
                VirExecutionErrorKind::AddressTypeMismatch {
                    found: base.access,
                    expected: expected_base,
                },
                source_span,
            ));
        }
        let layout = memory
            .layout(element.layout)
            .filter(|layout| layout.ty == element.ty && layout.size_bytes == stride_bytes)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        let source_bytes = length.checked_mul(stride_bytes).ok_or_else(|| {
            error(
                VirExecutionErrorKind::AddressCalculationOverflow,
                source_span,
            )
        })?;
        let start_bytes = start
            .checked_mul(stride_bytes)
            .and_then(|delta| base.offset_bytes.checked_add(delta))
            .ok_or_else(|| {
                error(
                    VirExecutionErrorKind::AddressCalculationOverflow,
                    source_span,
                )
            })?;
        let source_end = base.offset_bytes.checked_add(source_bytes).ok_or_else(|| {
            error(
                VirExecutionErrorKind::AddressCalculationOverflow,
                source_span,
            )
        })?;
        let allocation = self.live_allocation(base.allocation, source_span)?;
        if source_end > allocation.size_bytes {
            return Err(error(
                VirExecutionErrorKind::AddressOutOfBounds {
                    allocation: base.allocation,
                    offset_bytes: base.offset_bytes,
                    object_bytes: source_bytes,
                    size_bytes: allocation.size_bytes,
                },
                source_span,
            ));
        }
        self.check_domain(base, base.offset_bytes, source_end, source_span)?;
        if !base.offset_bytes.is_multiple_of(layout.alignment)
            || start_bytes % layout.alignment != 0
        {
            return Err(error(
                VirExecutionErrorKind::MisalignedAccess {
                    allocation: base.allocation,
                    offset_bytes: start_bytes,
                    required_alignment: layout.alignment,
                },
                source_span,
            ));
        }
        Ok(VirRuntimePointer {
            allocation: base.allocation,
            offset_bytes: start_bytes,
            access: element,
            paths: if expected_base == element {
                base.paths
            } else {
                base.paths.element()
            },
            view_range: None,
            domain: base.domain,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn slice_range(
        &self,
        memory: &VirMemorySchema,
        base: VirRuntimePointer,
        permission: VirRuntimePermission,
        expected_base: VirMemoryAccess,
        element: VirMemoryAccess,
        start: u64,
        end: u64,
        length: u64,
        stride_bytes: u64,
        source_span: ByteSpan,
    ) -> Result<(VirRuntimePointer, VirRuntimePermission), VirExecutionError> {
        let pointer = self.slice_address(
            memory,
            base,
            expected_base,
            element,
            start,
            length,
            stride_bytes,
            source_span,
        )?;
        let source_end = length
            .checked_mul(stride_bytes)
            .and_then(|bytes| base.offset_bytes.checked_add(bytes))
            .ok_or_else(|| {
                error(
                    VirExecutionErrorKind::AddressCalculationOverflow,
                    source_span,
                )
            })?;
        let end_bytes = end
            .checked_mul(stride_bytes)
            .and_then(|delta| base.offset_bytes.checked_add(delta))
            .ok_or_else(|| {
                error(
                    VirExecutionErrorKind::AddressCalculationOverflow,
                    source_span,
                )
            })?;
        if permission.allocation != base.allocation {
            return Err(error(
                VirExecutionErrorKind::PermissionMismatch {
                    allocation: base.allocation,
                    permission_allocation: permission.allocation,
                },
                source_span,
            ));
        }
        if base.offset_bytes < permission.start_bytes || source_end > permission.end_bytes {
            return Err(error(
                VirExecutionErrorKind::PermissionOutOfRange {
                    start_bytes: permission.start_bytes,
                    end_bytes: permission.end_bytes,
                    access_start_bytes: base.offset_bytes,
                    access_end_bytes: source_end,
                },
                source_span,
            ));
        }
        Ok((
            VirRuntimePointer {
                domain: crate::VirPointerDomain::Restricted(super::VirLoanRange {
                    start_bytes: pointer.offset_bytes,
                    end_bytes,
                }),
                view_range: Some(super::VirLoanRange {
                    start_bytes: pointer.offset_bytes,
                    end_bytes,
                }),
                ..pointer
            },
            VirRuntimePermission {
                allocation: base.allocation,
                start_bytes: pointer.offset_bytes,
                end_bytes,
                can_free_when_complete: false,
            },
        ))
    }

    fn check_object_address(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        expected: VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        if pointer.access != expected || !memory.resolves_access(expected) {
            return Err(error(
                VirExecutionErrorKind::AddressTypeMismatch {
                    found: pointer.access,
                    expected,
                },
                source_span,
            ));
        }
        let layout = memory
            .layout(expected.layout)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        let allocation = self.live_allocation(pointer.allocation, source_span)?;
        if allocation.alignment < layout.alignment
            || !pointer.offset_bytes.is_multiple_of(layout.alignment)
        {
            return Err(error(
                VirExecutionErrorKind::MisalignedAccess {
                    allocation: pointer.allocation,
                    offset_bytes: pointer.offset_bytes,
                    required_alignment: layout.alignment,
                },
                source_span,
            ));
        }
        if pointer
            .offset_bytes
            .checked_add(layout.size_bytes)
            .is_none_or(|end| end > allocation.size_bytes)
        {
            return Err(error(
                VirExecutionErrorKind::AddressOutOfBounds {
                    allocation: pointer.allocation,
                    offset_bytes: pointer.offset_bytes,
                    object_bytes: layout.size_bytes,
                    size_bytes: allocation.size_bytes,
                },
                source_span,
            ));
        }
        self.check_domain(
            pointer,
            pointer.offset_bytes,
            pointer.offset_bytes + layout.size_bytes,
            source_span,
        )
    }

    fn check_access(
        &self,
        pointer: VirRuntimePointer,
        permission: VirRuntimePermission,
        context: MemoryAccessContext<'_>,
    ) -> Result<(), VirExecutionError> {
        if pointer.access != context.access {
            return Err(error(
                VirExecutionErrorKind::AddressTypeMismatch {
                    found: pointer.access,
                    expected: context.access,
                },
                context.source_span,
            ));
        }
        let layout = context
            .memory
            .layout(context.access.layout)
            .filter(|layout| layout.ty == context.access.ty)
            .ok_or_else(|| {
                error(
                    VirExecutionErrorKind::InvalidRuntimeState,
                    context.source_span,
                )
            })?;
        let allocation = self.live_allocation(pointer.allocation, context.source_span)?;
        if allocation.alignment < layout.alignment
            || !pointer.offset_bytes.is_multiple_of(layout.alignment)
        {
            return Err(error(
                VirExecutionErrorKind::MisalignedAccess {
                    allocation: pointer.allocation,
                    offset_bytes: pointer.offset_bytes,
                    required_alignment: layout.alignment,
                },
                context.source_span,
            ));
        }
        let access_end = pointer
            .offset_bytes
            .checked_add(layout.size_bytes)
            .filter(|end| *end <= allocation.size_bytes)
            .ok_or_else(|| {
                error(
                    VirExecutionErrorKind::OutOfBoundsAccess {
                        allocation: pointer.allocation,
                        offset_bytes: pointer.offset_bytes,
                        access_bytes: layout.size_bytes,
                        size_bytes: allocation.size_bytes,
                    },
                    context.source_span,
                )
            })?;
        if permission.allocation != pointer.allocation {
            return Err(error(
                VirExecutionErrorKind::PermissionMismatch {
                    allocation: pointer.allocation,
                    permission_allocation: permission.allocation,
                },
                context.source_span,
            ));
        }
        if pointer.offset_bytes < permission.start_bytes || access_end > permission.end_bytes {
            return Err(error(
                VirExecutionErrorKind::PermissionOutOfRange {
                    start_bytes: permission.start_bytes,
                    end_bytes: permission.end_bytes,
                    access_start_bytes: pointer.offset_bytes,
                    access_end_bytes: access_end,
                },
                context.source_span,
            ));
        }
        self.check_domain(
            pointer,
            pointer.offset_bytes,
            access_end,
            context.source_span,
        )
    }

    fn load_memory(
        &self,
        pointer: VirRuntimePointer,
        permission: VirRuntimePermission,
        context: MemoryAccessContext<'_>,
    ) -> Result<u64, VirExecutionError> {
        self.check_access(pointer, permission, context)?;
        self.check_scalar_active_access(context.memory, pointer, context.source_span)?;
        let layout = context
            .memory
            .layout(context.access.layout)
            .expect("validated scalar access");
        let allocation = &self.allocations[&pointer.allocation];
        let bytes = read_initialized_bytes(
            allocation,
            pointer.allocation,
            pointer.offset_bytes,
            layout.size_bytes,
            context.access,
            false,
            context.source_span,
        )?;
        let value = decode_u64(&bytes, context.memory.target.endianness).ok_or_else(|| {
            error(
                VirExecutionErrorKind::InvalidObjectRepresentation {
                    allocation: pointer.allocation,
                    offset_bytes: pointer.offset_bytes,
                    access: context.access,
                },
                context.source_span,
            )
        })?;
        if matches!(
            context.memory.kind(context.access.ty),
            Some(VirMemoryTypeKind::Bool)
        ) && value > 1
        {
            return Err(error(
                VirExecutionErrorKind::InvalidObjectRepresentation {
                    allocation: pointer.allocation,
                    offset_bytes: pointer.offset_bytes,
                    access: context.access,
                },
                context.source_span,
            ));
        }
        Ok(value)
    }

    fn write_memory(
        &mut self,
        pointer: VirRuntimePointer,
        permission: VirRuntimePermission,
        value: u64,
        kind: WriteKind,
        context: MemoryAccessContext<'_>,
    ) -> Result<(), VirExecutionError> {
        self.check_access(pointer, permission, context)?;
        self.check_scalar_active_access(context.memory, pointer, context.source_span)?;
        let layout = context
            .memory
            .layout(context.access.layout)
            .expect("validated scalar access");
        let encoded = encode_u64(value, layout.size_bytes, context.memory.target.endianness)
            .ok_or_else(|| {
                error(
                    VirExecutionErrorKind::InvalidRuntimeState,
                    context.source_span,
                )
            })?;
        let allocation = self
            .allocations
            .get_mut(&pointer.allocation)
            .ok_or_else(|| {
                error(
                    VirExecutionErrorKind::InvalidRuntimeState,
                    context.source_span,
                )
            })?;
        let first_initialized = encoded.iter().enumerate().find_map(|(index, _)| {
            let index = u64::try_from(index).ok()?;
            let offset = pointer.offset_bytes.checked_add(index)?;
            allocation.bytes.contains_key(&offset).then_some(offset)
        });
        let first_uninitialized = encoded.iter().enumerate().find_map(|(index, _)| {
            let index = u64::try_from(index).ok()?;
            let offset = pointer.offset_bytes.checked_add(index)?;
            (!allocation.bytes.contains_key(&offset)).then_some(offset)
        });
        match (kind, first_initialized, first_uninitialized) {
            (WriteKind::Initialize, Some(offset_bytes), _) => {
                return Err(error(
                    VirExecutionErrorKind::InitializeAlreadyInitialized {
                        allocation: pointer.allocation,
                        offset_bytes,
                    },
                    context.source_span,
                ));
            }
            (WriteKind::Store, _, Some(offset_bytes)) => {
                return Err(error(
                    VirExecutionErrorKind::StoreToUninitialized {
                        allocation: pointer.allocation,
                        offset_bytes,
                    },
                    context.source_span,
                ));
            }
            (WriteKind::Initialize, None, _)
            | (WriteKind::Write, _, _)
            | (WriteKind::Store, _, None) => {}
        }
        for (index, byte) in encoded.into_iter().enumerate() {
            let offset = pointer.offset_bytes + u64::try_from(index).expect("small scalar layout");
            allocation.bytes.insert(offset, byte);
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn resource_initialize(
        &mut self,
        memory: &VirMemorySchema,
        destination: VirRuntimePointer,
        destination_permission: VirRuntimePermission,
        value: VirRuntimePointer,
        value_permission: VirRuntimePermission,
        loan_authority: Option<RuntimeLoanAuthority>,
        access: VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let (pointee, kind) = runtime_storable_resource(memory, access, source_span)?;
        if value.access != pointee {
            return Err(error(
                VirExecutionErrorKind::AddressTypeMismatch {
                    found: value.access,
                    expected: pointee,
                },
                source_span,
            ));
        }
        match kind {
            super::VirPointerKind::Own => {
                let owned = self.live_allocation(value.allocation, source_span)?;
                if loan_authority.is_some()
                    || value.offset_bytes != 0
                    || value_permission.allocation != value.allocation
                    || value_permission.start_bytes != 0
                    || value_permission.end_bytes != owned.size_bytes
                    || !value_permission.can_free_when_complete
                {
                    return Err(error(
                        VirExecutionErrorKind::InvalidFree {
                            allocation: value.allocation,
                            offset_bytes: value.offset_bytes,
                        },
                        source_span,
                    ));
                }
            }
            super::VirPointerKind::Reference => {
                if loan_authority.is_none()
                    || value_permission.can_free_when_complete
                    || value_permission.allocation != value.allocation
                    || value.offset_bytes < value_permission.start_bytes
                    || value.offset_bytes >= value_permission.end_bytes
                {
                    return Err(error(
                        VirExecutionErrorKind::InvalidRuntimeState,
                        source_span,
                    ));
                }
            }
            super::VirPointerKind::Raw => {
                return Err(error(
                    VirExecutionErrorKind::UnsupportedObjectEffectType { access },
                    source_span,
                ));
            }
        }
        self.check_access(
            destination,
            destination_permission,
            MemoryAccessContext::new(memory, access, source_span),
        )?;
        let key = RuntimeResourcePayloadKey {
            offset_bytes: destination.offset_bytes,
            access,
        };
        let destination_allocation = &self.allocations[&destination.allocation];
        if !destination_allocation.resource_payloads.contains_key(&key)
            && destination_allocation.resource_payloads.len()
                >= VIR_INTERPRETER_MAX_RESOURCE_PAYLOADS
        {
            return Err(error(
                VirExecutionErrorKind::ResourcePayloadLimitExceeded {
                    allocation: destination.allocation,
                    limit: VIR_INTERPRETER_MAX_RESOURCE_PAYLOADS,
                },
                source_span,
            ));
        }
        self.write_memory(
            destination,
            destination_permission,
            opaque_runtime_pointer_bits(value),
            WriteKind::Initialize,
            MemoryAccessContext::new(memory, access, source_span),
        )?;
        self.allocations
            .get_mut(&destination.allocation)
            .expect("checked live resource destination")
            .resource_payloads
            .insert(
                key,
                RuntimeOwnedPayload {
                    pointer: value,
                    permission: value_permission,
                    loan_authority,
                },
            );
        Ok(())
    }

    fn resource_take(
        &mut self,
        memory: &VirMemorySchema,
        source: VirRuntimePointer,
        source_permission: VirRuntimePermission,
        access: VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Result<RuntimeOwnedPayload, VirExecutionError> {
        runtime_storable_resource(memory, access, source_span)?;
        let context = MemoryAccessContext::new(memory, access, source_span);
        let _physical_bits = self.load_memory(source, source_permission, context)?;
        let key = RuntimeResourcePayloadKey {
            offset_bytes: source.offset_bytes,
            access,
        };
        let payload = self.allocations[&source.allocation]
            .resource_payloads
            .get(&key)
            .copied()
            .ok_or_else(|| {
                error(
                    VirExecutionErrorKind::MissingResourcePayload {
                        allocation: source.allocation,
                        offset_bytes: source.offset_bytes,
                        access,
                    },
                    source_span,
                )
            })?;
        let width = memory
            .layout(access.layout)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?
            .size_bytes;
        let allocation = self
            .allocations
            .get_mut(&source.allocation)
            .expect("checked live resource source");
        allocation.resource_payloads.remove(&key);
        for offset in source.offset_bytes..source.offset_bytes + width {
            allocation.bytes.remove(&offset);
        }
        Ok(payload)
    }

    #[allow(clippy::too_many_arguments)]
    fn object_transfer(
        &mut self,
        memory: &VirMemorySchema,
        loan_shadow: &mut RuntimeLoanShadow,
        loan_limits: RuntimeLoanLimits,
        destination: VirRuntimePointer,
        destination_permission: VirRuntimePermission,
        source: VirRuntimePointer,
        source_permission: VirRuntimePermission,
        access: VirMemoryAccess,
        destination_mode: VirObjectDestinationMode,
        source_mode: VirObjectSourceMode,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let context = MemoryAccessContext::new(memory, access, source_span);
        self.check_access(destination, destination_permission, context)?;
        self.check_access(source, source_permission, context)?;
        let shape = memory
            .object_shape(access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        self.check_object_effect_size(shape.size_bytes(), source_span)?;
        ensure_runtime_object_transfer_type(
            memory,
            &shape,
            destination_mode,
            source_mode,
            source_span,
        )?;

        if destination.allocation == source.allocation
            && half_open_ranges_overlap(
                destination.offset_bytes,
                source.offset_bytes,
                shape.size_bytes(),
            )
        {
            return Err(error(
                VirExecutionErrorKind::OverlappingObjectTransfer {
                    allocation: source.allocation,
                    destination_offset_bytes: destination.offset_bytes,
                    source_offset_bytes: source.offset_bytes,
                    size_bytes: shape.size_bytes(),
                },
                source_span,
            ));
        }

        let source_offsets = self.active_object_offsets(memory, source, &shape, source_span)?;
        self.require_object_value(memory, source, &shape, &source_offsets, source_span)?;
        let mut source_payloads =
            self.active_resource_payloads(memory, source, &shape, source_span)?;
        if matches!(source_mode, VirObjectSourceMode::Copy) {
            for (_, leaf_access, payload) in &mut source_payloads {
                let Some(VirMemoryTypeKind::Pointer { kind, .. }) = memory.kind(leaf_access.ty)
                else {
                    return Err(error(
                        VirExecutionErrorKind::InvalidRuntimeState,
                        source_span,
                    ));
                };
                match kind {
                    super::VirPointerKind::Reference => {
                        let authority = payload.loan_authority.ok_or_else(|| {
                            error(VirExecutionErrorKind::InvalidRuntimeState, source_span)
                        })?;
                        payload.loan_authority = Some(loan_shadow.alias_stored(
                            authority,
                            payload.pointer,
                            *leaf_access,
                            loan_limits,
                            source_span,
                        )?);
                    }
                    super::VirPointerKind::Own | super::VirPointerKind::Raw => {
                        return Err(error(
                            VirExecutionErrorKind::UnsupportedObjectEffectType { access },
                            source_span,
                        ));
                    }
                }
            }
        }
        let destination_offsets = match destination_mode {
            VirObjectDestinationMode::Initialize => {
                let allocation = &self.allocations[&destination.allocation];
                if let Some(relative) = source_offsets.iter().copied().find(|relative| {
                    allocation
                        .bytes
                        .contains_key(&(destination.offset_bytes + relative))
                }) {
                    return Err(error(
                        VirExecutionErrorKind::InitializeAlreadyInitialized {
                            allocation: destination.allocation,
                            offset_bytes: destination.offset_bytes + relative,
                        },
                        source_span,
                    ));
                }
                BTreeSet::new()
            }
            VirObjectDestinationMode::Replace => {
                let offsets =
                    self.active_object_offsets(memory, destination, &shape, source_span)?;
                self.require_object_value(memory, destination, &shape, &offsets, source_span)?;
                offsets
            }
        };
        let destination_allocation = &self.allocations[&destination.allocation];
        let additional_payloads = source_payloads
            .iter()
            .filter(|(relative, access, _)| {
                !destination_allocation
                    .resource_payloads
                    .contains_key(&RuntimeResourcePayloadKey {
                        offset_bytes: destination.offset_bytes + relative,
                        access: *access,
                    })
            })
            .count();
        if destination_allocation.resource_payloads.len() + additional_payloads
            > VIR_INTERPRETER_MAX_RESOURCE_PAYLOADS
        {
            return Err(error(
                VirExecutionErrorKind::ResourcePayloadLimitExceeded {
                    allocation: destination.allocation,
                    limit: VIR_INTERPRETER_MAX_RESOURCE_PAYLOADS,
                },
                source_span,
            ));
        }

        let source_bytes = {
            let allocation = &self.allocations[&source.allocation];
            source_offsets
                .iter()
                .map(|relative| {
                    let absolute = source.offset_bytes + relative;
                    (*relative, allocation.bytes[&absolute])
                })
                .collect::<Vec<_>>()
        };
        {
            let allocation = self
                .allocations
                .get_mut(&destination.allocation)
                .expect("checked live destination");
            for relative in destination_offsets.union(&source_offsets) {
                allocation
                    .bytes
                    .remove(&(destination.offset_bytes + relative));
            }
            for (relative, byte) in &source_bytes {
                allocation
                    .bytes
                    .insert(destination.offset_bytes + relative, *byte);
            }
            for (relative, access, payload) in &source_payloads {
                allocation.resource_payloads.insert(
                    RuntimeResourcePayloadKey {
                        offset_bytes: destination.offset_bytes + relative,
                        access: *access,
                    },
                    *payload,
                );
            }
        }
        if matches!(source_mode, VirObjectSourceMode::Move) {
            let allocation = self
                .allocations
                .get_mut(&source.allocation)
                .expect("checked live source");
            for relative in source_offsets {
                allocation.bytes.remove(&(source.offset_bytes + relative));
            }
            for (relative, access, _) in source_payloads {
                allocation
                    .resource_payloads
                    .remove(&RuntimeResourcePayloadKey {
                        offset_bytes: source.offset_bytes + relative,
                        access,
                    });
            }
        }
        self.register_runtime_object(destination, &shape, source_span)?;
        self.register_runtime_object(source, &shape, source_span)?;
        Ok(())
    }

    fn active_resource_payloads(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        shape: &VirObjectShape,
        source_span: ByteSpan,
    ) -> Result<Vec<(u64, VirMemoryAccess, RuntimeOwnedPayload)>, VirExecutionError> {
        let mut payloads = Vec::new();
        for leaf in shape.resource_leaves() {
            if self
                .path_inactive_variant(memory, pointer, shape, leaf.path(), source_span)?
                .is_some()
            {
                continue;
            }
            let key = RuntimeResourcePayloadKey {
                offset_bytes: pointer.offset_bytes + leaf.bytes().start_bytes(),
                access: leaf.access(),
            };
            let payload = self.allocations[&pointer.allocation]
                .resource_payloads
                .get(&key)
                .copied()
                .ok_or_else(|| {
                    error(
                        VirExecutionErrorKind::MissingResourcePayload {
                            allocation: pointer.allocation,
                            offset_bytes: key.offset_bytes,
                            access: key.access,
                        },
                        source_span,
                    )
                })?;
            payloads.push((leaf.bytes().start_bytes(), leaf.access(), payload));
        }
        Ok(payloads)
    }

    fn resource_storage_reset(
        &mut self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        permission: VirRuntimePermission,
        access: VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        self.check_access(
            pointer,
            permission,
            MemoryAccessContext::new(memory, access, source_span),
        )?;
        let shape = memory
            .object_shape(access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        self.check_object_effect_size(shape.size_bytes(), source_span)?;
        if !shape.supports_resource_storage_reset() {
            return Err(error(
                VirExecutionErrorKind::UnsupportedObjectEffectType { access },
                source_span,
            ));
        }
        let allocation = &self.allocations[&pointer.allocation];
        if !allocation.resource_payloads.is_empty() {
            return Err(error(
                VirExecutionErrorKind::AllocationContainsResourcePayload {
                    allocation: pointer.allocation,
                },
                source_span,
            ));
        }
        if shape.resource_leaves().iter().any(|leaf| {
            (leaf.bytes().start_bytes()..leaf.bytes().end_bytes()).any(|offset| {
                allocation
                    .bytes
                    .contains_key(&(pointer.offset_bytes + offset))
            })
        }) {
            return Err(error(
                VirExecutionErrorKind::InvalidRuntimeState,
                source_span,
            ));
        }
        let offsets = self.active_object_offsets(memory, pointer, &shape, source_span)?;
        let allocation = self
            .allocations
            .get_mut(&pointer.allocation)
            .expect("checked storage reset");
        for offset in offsets {
            allocation.bytes.remove(&(pointer.offset_bytes + offset));
        }
        self.register_runtime_object(pointer, &shape, source_span)
    }

    fn object_deinitialize(
        &mut self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        permission: VirRuntimePermission,
        access: VirMemoryAccess,
        require_complete: bool,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        self.check_access(
            pointer,
            permission,
            MemoryAccessContext::new(memory, access, source_span),
        )?;
        let shape = memory
            .object_shape(access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        self.check_object_effect_size(shape.size_bytes(), source_span)?;
        ensure_runtime_object_type(memory, &shape, source_span)?;
        let offsets = self.active_object_offsets(memory, pointer, &shape, source_span)?;
        if require_complete {
            self.require_object_value(memory, pointer, &shape, &offsets, source_span)?;
        } else if !shape.supports_storage_reset() {
            return Err(error(
                VirExecutionErrorKind::InvalidRuntimeState,
                source_span,
            ));
        }
        let allocation = self
            .allocations
            .get_mut(&pointer.allocation)
            .expect("checked live object");
        for relative in offsets {
            allocation.bytes.remove(&(pointer.offset_bytes + relative));
        }
        self.register_runtime_object(pointer, &shape, source_span)?;
        Ok(())
    }

    fn object_drop(
        &mut self,
        memory: &VirMemorySchema,
        loan_shadow: &mut RuntimeLoanShadow,
        pointer: VirRuntimePointer,
        permission: VirRuntimePermission,
        access: VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        self.check_access(
            pointer,
            permission,
            MemoryAccessContext::new(memory, access, source_span),
        )?;
        let shape = memory
            .object_shape(access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        self.check_object_effect_size(shape.size_bytes(), source_span)?;
        ensure_runtime_object_drop_type(memory, &shape, source_span)?;

        // No tag may be decoded in empty, never-constructed (or wholly moved)
        // storage. Check byte absence and authority absence independently.
        let allocation = &self.allocations[&pointer.allocation];
        if matches!(allocation.kind, RuntimeAllocationKind::Heap)
            && !shape.variants().is_empty()
            && shape.value_bytes().iter().all(|range| {
                (range.start_bytes()..range.end_bytes()).all(|offset| {
                    !allocation
                        .bytes
                        .contains_key(&(pointer.offset_bytes + offset))
                })
            })
            && allocation.resource_payloads.keys().all(|key| {
                memory.layout(key.access.layout).is_some_and(|layout| {
                    key.offset_bytes >= pointer.offset_bytes + shape.size_bytes()
                        || key.offset_bytes.saturating_add(layout.size_bytes)
                            <= pointer.offset_bytes
                })
            })
        {
            return Ok(());
        }
        let all_offsets = self.active_object_offsets(memory, pointer, &shape, source_span)?;
        let mut owned = Vec::new();
        for leaf in shape.resource_leaves() {
            if self
                .path_inactive_variant(memory, pointer, &shape, leaf.path(), source_span)?
                .is_some()
            {
                continue;
            }
            let start = pointer
                .offset_bytes
                .checked_add(leaf.bytes().start_bytes())
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
            let end = pointer
                .offset_bytes
                .checked_add(leaf.bytes().end_bytes())
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
            let key = RuntimeResourcePayloadKey {
                offset_bytes: start,
                access: leaf.access(),
            };
            let payload = self.allocations[&pointer.allocation]
                .resource_payloads
                .get(&key)
                .copied();
            let bytes_present = (start..end).all(|offset| {
                self.allocations[&pointer.allocation]
                    .bytes
                    .contains_key(&offset)
            });
            match (payload, bytes_present) {
                (Some(payload), true) => owned.push((key, payload)),
                (None, false) => {}
                (None, true) => {
                    return Err(error(
                        VirExecutionErrorKind::MissingResourcePayload {
                            allocation: pointer.allocation,
                            offset_bytes: start,
                            access: leaf.access(),
                        },
                        source_span,
                    ));
                }
                (Some(_), false) => {
                    return Err(error(
                        VirExecutionErrorKind::InvalidRuntimeState,
                        source_span,
                    ));
                }
            }
        }
        // active_object_offsets decoded every active tag above. Cleanup never
        // observes trivial payload bytes, which may be absent after a move or
        // during construction.

        for (key, payload) in &owned {
            let kind = memory.kind(key.access.ty).and_then(|kind| match kind {
                VirMemoryTypeKind::Pointer { kind, .. } => Some(*kind),
                _ => None,
            });
            match kind {
                Some(super::VirPointerKind::Own) => {
                    if payload.loan_authority.is_some() {
                        return Err(error(
                            VirExecutionErrorKind::InvalidRuntimeState,
                            source_span,
                        ));
                    }
                    self.free(payload.pointer, payload.permission, source_span)?;
                }
                Some(super::VirPointerKind::Reference) => {
                    let authority = payload.loan_authority.ok_or_else(|| {
                        error(VirExecutionErrorKind::InvalidRuntimeState, source_span)
                    })?;
                    loan_shadow.end_stored(authority, payload.pointer, key.access, source_span)?;
                }
                Some(super::VirPointerKind::Raw) | None => {
                    return Err(error(
                        VirExecutionErrorKind::UnsupportedObjectEffectType { access },
                        source_span,
                    ));
                }
            }
        }
        let allocation = self
            .allocations
            .get_mut(&pointer.allocation)
            .expect("checked live object drop");
        for (key, _) in owned {
            allocation.resource_payloads.remove(&key);
        }
        for relative in all_offsets {
            allocation.bytes.remove(&(pointer.offset_bytes + relative));
        }
        self.register_runtime_object(pointer, &shape, source_span)?;
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn enum_set_discriminant(
        &mut self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        permission: VirRuntimePermission,
        access: VirMemoryAccess,
        variant: VirVariantId,
        mode: VirObjectDestinationMode,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        self.check_access(
            pointer,
            permission,
            MemoryAccessContext::new(memory, access, source_span),
        )?;
        let shape = memory
            .object_shape(access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        self.check_object_effect_size(shape.size_bytes(), source_span)?;
        match mode {
            VirObjectDestinationMode::Initialize => {
                ensure_runtime_object_observation_type(memory, &shape, source_span)?;
            }
            VirObjectDestinationMode::Replace => {
                ensure_runtime_object_type(memory, &shape, source_span)?;
            }
        }
        let case = shape
            .variants()
            .iter()
            .find(|case| case.path().segments().is_empty() && case.variant() == variant)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        let tag = case.tag();
        // A new tag cannot hide live authority from another variant. This is
        // checked independently of initialized bytes and the new active mask.
        let end = pointer.offset_bytes + shape.size_bytes();
        for key in self.allocations[&pointer.allocation]
            .resource_payloads
            .keys()
        {
            let layout = memory
                .layout(key.access.layout)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
            if key.offset_bytes < end
                && key.offset_bytes.saturating_add(layout.size_bytes) > pointer.offset_bytes
            {
                return Err(error(
                    VirExecutionErrorKind::AllocationContainsResourcePayload {
                        allocation: pointer.allocation,
                    },
                    source_span,
                ));
            }
        }
        let tag_start = pointer
            .offset_bytes
            .checked_add(tag.start_bytes())
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        let previous_offsets = if matches!(mode, VirObjectDestinationMode::Replace) {
            Some(self.active_object_offsets(memory, pointer, &shape, source_span)?)
        } else {
            None
        };
        match mode {
            VirObjectDestinationMode::Initialize => {
                let allocation = &self.allocations[&pointer.allocation];
                for offset in tag_start..tag_start + tag.len_bytes() {
                    if allocation.bytes.contains_key(&offset) {
                        return Err(error(
                            VirExecutionErrorKind::InitializeAlreadyInitialized {
                                allocation: pointer.allocation,
                                offset_bytes: offset,
                            },
                            source_span,
                        ));
                    }
                }
            }
            VirObjectDestinationMode::Replace => {
                // `active_object_offsets` above decodes every active enum site,
                // including the root discriminant, without requiring payload
                // bytes to be initialized.
            }
        }
        let discriminant = encode_u64(
            case.discriminant(),
            tag.len_bytes(),
            memory.target.endianness,
        )
        .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        let allocation = self
            .allocations
            .get_mut(&pointer.allocation)
            .expect("checked live enum");
        let mut retired = previous_offsets.unwrap_or_default();
        for range in case.value_bytes() {
            retired.extend(range.start_bytes()..range.end_bytes());
        }
        for relative in tag.start_bytes()..tag.end_bytes() {
            retired.remove(&relative);
        }
        for relative in retired {
            allocation.bytes.remove(&(pointer.offset_bytes + relative));
        }
        for (index, byte) in discriminant.into_iter().enumerate() {
            allocation.bytes.insert(
                tag_start + u64::try_from(index).expect("tag index fits u64"),
                byte,
            );
        }
        self.register_runtime_object(pointer, &shape, source_span)?;
        Ok(())
    }

    fn enum_discriminant(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        permission: VirRuntimePermission,
        access: VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Result<u64, VirExecutionError> {
        self.check_access(
            pointer,
            permission,
            MemoryAccessContext::new(memory, access, source_span),
        )?;
        let shape = memory
            .object_shape(access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        self.check_object_effect_size(shape.size_bytes(), source_span)?;
        ensure_runtime_object_observation_type(memory, &shape, source_span)?;
        let path = VirObjectPath::default();
        let active =
            self.read_active_variant(memory, pointer, &shape, &path, access, source_span)?;
        shape
            .variants()
            .iter()
            .find(|case| {
                case.path().segments().is_empty()
                    && case.enum_access() == access
                    && case.variant() == active
            })
            .map(|case| case.discriminant())
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))
    }

    fn active_object_offsets(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        shape: &VirObjectShape,
        source_span: ByteSpan,
    ) -> Result<BTreeSet<u64>, VirExecutionError> {
        let mut offsets = BTreeSet::new();
        let mut sites = BTreeSet::new();
        for case in shape.variants() {
            sites.insert((case.path().clone(), case.enum_access()));
        }
        for (path, enum_access) in sites {
            if self
                .path_inactive_variant(memory, pointer, shape, &path, source_span)?
                .is_some()
            {
                continue;
            }
            let active =
                self.read_active_variant(memory, pointer, shape, &path, enum_access, source_span)?;
            let case = shape
                .variants()
                .iter()
                .find(|case| {
                    case.path() == &path
                        && case.enum_access() == enum_access
                        && case.variant() == active
                })
                .expect("decoded variant belongs to canonical shape");
            offsets.extend(case.tag().start_bytes()..case.tag().end_bytes());
        }
        for leaf in shape.leaves() {
            if self
                .path_inactive_variant(memory, pointer, shape, leaf.path(), source_span)?
                .is_none()
            {
                offsets.extend(leaf.bytes().start_bytes()..leaf.bytes().end_bytes());
            }
        }
        Ok(offsets)
    }

    /// Check reference formation, not a read of the object's padding. The
    /// static slice range is a conservative envelope, as in the verifier.
    fn check_borrow_value(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        reference: VirMemoryAccess,
        range: super::VirLoanRange,
        span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let (pointee, slice) = match memory.kind(reference.ty) {
            Some(VirMemoryTypeKind::Pointer {
                pointee,
                kind: super::VirPointerKind::Reference,
                ..
            }) => (*pointee, false),
            Some(VirMemoryTypeKind::Slice { element, .. }) => (*element, true),
            _ => return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span)),
        };
        let access = memory
            .access(pointee)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
        let shape = memory
            .object_shape(access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
        ensure_runtime_object_observation_type(memory, &shape, span)?;
        self.check_domain(pointer, range.start_bytes, range.end_bytes, span)?;
        let allocation = self.live_allocation(pointer.allocation, span)?;
        if range.start_bytes > range.end_bytes || range.end_bytes > allocation.size_bytes {
            return Err(error(
                VirExecutionErrorKind::AddressOutOfBounds {
                    allocation: pointer.allocation,
                    offset_bytes: range.start_bytes,
                    object_bytes: range.end_bytes.saturating_sub(range.start_bytes),
                    size_bytes: allocation.size_bytes,
                },
                span,
            ));
        }
        if pointer.access != access {
            return Err(error(
                VirExecutionErrorKind::AddressTypeMismatch {
                    found: pointer.access,
                    expected: access,
                },
                span,
            ));
        }
        let extent = range.end_bytes - range.start_bytes;
        self.check_object_effect_size(if slice { extent } else { shape.size_bytes() }, span)?;
        let stride = shape.size_bytes();
        if slice && (stride == 0 || !extent.is_multiple_of(stride)) {
            return Err(error(
                VirExecutionErrorKind::UnsupportedObjectEffectType { access },
                span,
            ));
        }
        if allocation.alignment < shape.alignment()
            || !pointer.offset_bytes.is_multiple_of(shape.alignment())
        {
            return Err(error(
                VirExecutionErrorKind::MisalignedAccess {
                    allocation: pointer.allocation,
                    offset_bytes: pointer.offset_bytes,
                    required_alignment: shape.alignment(),
                },
                span,
            ));
        }
        let count = if slice { extent / stride } else { 1 };
        for index in 0..count {
            let selected = if slice {
                VirRuntimePointer {
                    offset_bytes: range.start_bytes + index * stride,
                    ..pointer
                }
            } else {
                pointer
            };
            self.check_object_address(memory, selected, access, span)?;
            self.check_scalar_active_access(memory, selected, span)?;
            let offsets = self.active_object_offsets(memory, selected, &shape, span)?;
            self.require_object_value(memory, selected, &shape, &offsets, span)?;
            self.active_resource_payloads(memory, selected, &shape, span)?;
        }
        Ok(())
    }

    fn borrow_selection(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        reference: VirMemoryAccess,
        span: ByteSpan,
    ) -> Result<super::VirLoanRange, VirExecutionError> {
        let (pointee, slice) = match memory.kind(reference.ty) {
            Some(VirMemoryTypeKind::Pointer {
                pointee,
                kind: super::VirPointerKind::Reference,
                ..
            }) => (*pointee, false),
            Some(VirMemoryTypeKind::Slice { element, .. }) => (*element, true),
            _ => return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span)),
        };
        let access = memory
            .access(pointee)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
        let stride = memory
            .object_shape(access)
            .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
            .size_bytes();
        let range = if slice {
            pointer
                .view_range
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
        } else {
            super::VirLoanRange {
                start_bytes: pointer.offset_bytes,
                end_bytes: pointer.offset_bytes.checked_add(stride).ok_or_else(|| {
                    error(VirExecutionErrorKind::AddressCalculationOverflow, span)
                })?,
            }
        };
        if pointer.access != access
            || range.start_bytes != pointer.offset_bytes
            || range.end_bytes < range.start_bytes
            || (slice && (stride == 0 || (range.end_bytes - range.start_bytes) % stride != 0))
        {
            return Err(error(VirExecutionErrorKind::InvalidRuntimeState, span));
        }
        Ok(range)
    }

    fn require_object_value(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        shape: &VirObjectShape,
        offsets: &BTreeSet<u64>,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let allocation = &self.allocations[&pointer.allocation];
        for relative in offsets {
            let absolute = pointer.offset_bytes + relative;
            if !allocation.bytes.contains_key(&absolute) {
                return Err(error(
                    VirExecutionErrorKind::UninitializedObjectLeaf {
                        allocation: pointer.allocation,
                        offset_bytes: absolute,
                        access: shape.access(),
                    },
                    source_span,
                ));
            }
        }
        for leaf in shape.leaves() {
            if !matches!(memory.kind(leaf.access().ty), Some(VirMemoryTypeKind::Bool))
                || self
                    .path_inactive_variant(memory, pointer, shape, leaf.path(), source_span)?
                    .is_some()
            {
                continue;
            }
            let absolute = pointer.offset_bytes + leaf.bytes().start_bytes();
            if allocation.bytes.get(&absolute).copied() != Some(0)
                && allocation.bytes.get(&absolute).copied() != Some(1)
            {
                return Err(error(
                    VirExecutionErrorKind::InvalidObjectRepresentation {
                        allocation: pointer.allocation,
                        offset_bytes: absolute,
                        access: leaf.access(),
                    },
                    source_span,
                ));
            }
        }
        Ok(())
    }

    fn check_scalar_active_access(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let allocation = self.live_allocation(pointer.allocation, source_span)?;
        let access_size = memory
            .layout(pointer.access.layout)
            .map(|layout| layout.size_bytes)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        let mut found_candidate = false;
        let mut inactive = None;
        for object in &allocation.objects {
            let shape = memory
                .object_shape(object.access)
                .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
            for leaf in shape.leaves() {
                let start = object.offset_bytes + leaf.bytes().start_bytes();
                let end = object.offset_bytes + leaf.bytes().end_bytes();
                if leaf.access() != pointer.access
                    || start != pointer.offset_bytes
                    || end != pointer.offset_bytes + access_size
                {
                    continue;
                }
                found_candidate = true;
                let root = VirRuntimePointer {
                    allocation: pointer.allocation,
                    offset_bytes: object.offset_bytes,
                    access: object.access,
                    paths: crate::VirPointerPaths::default(),
                    view_range: None,
                    domain: crate::VirPointerDomain::Allocation,
                };
                match self.path_inactive_variant(memory, root, &shape, leaf.path(), source_span)? {
                    None => return Ok(()),
                    Some(candidate) => inactive.get_or_insert(candidate),
                };
            }
        }
        if found_candidate && let Some(inactive) = inactive {
            return Err(error(
                VirExecutionErrorKind::InactiveVariantAccess {
                    allocation: pointer.allocation,
                    offset_bytes: pointer.offset_bytes,
                    enum_access: inactive.enum_access,
                    active: inactive.active,
                    required: inactive.required,
                },
                source_span,
            ));
        }
        Ok(())
    }

    fn path_inactive_variant(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        shape: &VirObjectShape,
        path: &VirObjectPath,
        source_span: ByteSpan,
    ) -> Result<Option<RuntimeInactiveVariant>, VirExecutionError> {
        let mut prefix = Vec::new();
        for segment in path.segments() {
            if let VirObjectPathSegment::Variant(required) = segment {
                let case = shape
                    .variants()
                    .iter()
                    .find(|case| {
                        case.path().segments() == prefix.as_slice() && case.variant() == *required
                    })
                    .ok_or_else(|| {
                        error(VirExecutionErrorKind::InvalidRuntimeState, source_span)
                    })?;
                let active = self.read_active_variant(
                    memory,
                    pointer,
                    shape,
                    case.path(),
                    case.enum_access(),
                    source_span,
                )?;
                if active != *required {
                    return Ok(Some(RuntimeInactiveVariant {
                        enum_access: case.enum_access(),
                        active,
                        required: *required,
                    }));
                }
            }
            prefix.push(*segment);
        }
        Ok(None)
    }

    fn read_active_variant(
        &self,
        memory: &VirMemorySchema,
        pointer: VirRuntimePointer,
        shape: &VirObjectShape,
        path: &VirObjectPath,
        enum_access: VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Result<VirVariantId, VirExecutionError> {
        let case = shape
            .variants()
            .iter()
            .find(|case| case.path() == path && case.enum_access() == enum_access)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        let tag_start = pointer.offset_bytes + case.tag().start_bytes();
        let allocation = &self.allocations[&pointer.allocation];
        let bytes = read_initialized_bytes(
            allocation,
            pointer.allocation,
            tag_start,
            case.tag().len_bytes(),
            enum_access,
            true,
            source_span,
        )?;
        let discriminant = decode_u64(&bytes, memory.target.endianness).ok_or_else(|| {
            error(
                VirExecutionErrorKind::InvalidObjectRepresentation {
                    allocation: pointer.allocation,
                    offset_bytes: tag_start,
                    access: enum_access,
                },
                source_span,
            )
        })?;
        shape
            .variants()
            .iter()
            .find(|candidate| {
                candidate.path() == path
                    && candidate.enum_access() == enum_access
                    && candidate.discriminant() == discriminant
            })
            .map(|candidate| candidate.variant())
            .ok_or_else(|| {
                error(
                    VirExecutionErrorKind::InvalidObjectRepresentation {
                        allocation: pointer.allocation,
                        offset_bytes: tag_start,
                        access: enum_access,
                    },
                    source_span,
                )
            })
    }

    fn check_object_effect_size(
        &self,
        size_bytes: u64,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        if size_bytes > self.config.max_object_effect_bytes {
            return Err(error(
                VirExecutionErrorKind::ObjectEffectSizeLimitExceeded {
                    requested: size_bytes,
                    limit: self.config.max_object_effect_bytes,
                },
                source_span,
            ));
        }
        Ok(())
    }

    fn register_runtime_object(
        &mut self,
        pointer: VirRuntimePointer,
        shape: &VirObjectShape,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        if shape.variants().is_empty() {
            return Ok(());
        }
        let allocation = self
            .allocations
            .get_mut(&pointer.allocation)
            .expect("object access checked its allocation");
        let object = RuntimeObject {
            offset_bytes: pointer.offset_bytes,
            access: pointer.access,
        };
        if !allocation.objects.contains(&object) {
            if allocation.objects.len() >= VIR_INTERPRETER_MAX_OBJECT_ROOTS {
                return Err(error(
                    VirExecutionErrorKind::ObjectRootLimitExceeded {
                        allocation: pointer.allocation,
                        limit: VIR_INTERPRETER_MAX_OBJECT_ROOTS,
                    },
                    source_span,
                ));
            }
            allocation.objects.push(object);
            allocation
                .objects
                .sort_unstable_by_key(|object| (object.offset_bytes, object.access));
        }
        Ok(())
    }

    fn free(
        &mut self,
        pointer: VirRuntimePointer,
        permission: VirRuntimePermission,
        source_span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let allocation = self.live_allocation(pointer.allocation, source_span)?;
        if permission.allocation != pointer.allocation {
            return Err(error(
                VirExecutionErrorKind::PermissionMismatch {
                    allocation: pointer.allocation,
                    permission_allocation: permission.allocation,
                },
                source_span,
            ));
        }
        if pointer.offset_bytes != 0
            || permission.start_bytes != 0
            || permission.end_bytes != allocation.size_bytes
            || !permission.can_free_when_complete
        {
            return Err(error(
                VirExecutionErrorKind::InvalidFree {
                    allocation: pointer.allocation,
                    offset_bytes: pointer.offset_bytes,
                },
                source_span,
            ));
        }
        if !allocation.resource_payloads.is_empty() {
            return Err(error(
                VirExecutionErrorKind::AllocationContainsResourcePayload {
                    allocation: pointer.allocation,
                },
                source_span,
            ));
        }
        self.allocations
            .get_mut(&pointer.allocation)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?
            .live = false;
        Ok(())
    }

    fn charge_step(&mut self, source_span: ByteSpan) -> Result<(), VirExecutionError> {
        if self.steps >= self.config.max_steps {
            return Err(error(VirExecutionErrorKind::StepLimitExceeded, source_span));
        }
        self.steps += 1;
        Ok(())
    }
}

fn new_function_frame(
    program: &ResolvedRuntimeVirView<'_>,
    function_id: VirFunctionId,
    arguments: Vec<VirRuntimeValue>,
    call_return: Option<CallReturn>,
    source_span: ByteSpan,
) -> Result<FunctionFrame, VirExecutionError> {
    let function = program
        .function(function_id)
        .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
    if !runtime_values_match(&arguments, &function.signature.parameters) {
        return Err(error(
            VirExecutionErrorKind::InvalidRuntimeState,
            source_span,
        ));
    }
    let block = program
        .block(function_id, function.entry)
        .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
    let result_buffers =
        interface::capture_result_buffers(program, function_id, &arguments, source_span)?;
    Ok(FunctionFrame {
        function: function_id,
        block: function.entry,
        block_frame: BlockFrame::new(block, arguments, source_span)?,
        next_instruction: 0,
        call_return,
        local_allocations: Vec::new(),
        loan_shadow: RuntimeLoanShadow::default(),
        result_buffers,
    })
}

fn enter_block(
    program: &ResolvedRuntimeVirView<'_>,
    frame: &mut FunctionFrame,
    block_id: VirBlockId,
    arguments: Vec<RuntimeBlockArgument>,
    source_span: ByteSpan,
) -> Result<(), VirExecutionError> {
    let block = program
        .block(frame.function, block_id)
        .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
    frame.block = block_id;
    frame.block_frame = BlockFrame::from_block_arguments(block, arguments, source_span)?;
    frame.next_instruction = 0;
    Ok(())
}

fn check_loan_instruction_access(
    memory: &VirMemorySchema,
    frame: &BlockFrame,
    shadow: &RuntimeLoanShadow,
    instruction: &VirInstruction,
    source_span: ByteSpan,
) -> Result<(), VirExecutionError> {
    if !shadow.has_live_loans() {
        return Ok(());
    }
    match instruction {
        VirInstruction::Initialize {
            pointer,
            permission,
            access,
            ..
        }
        | VirInstruction::Write {
            pointer,
            permission,
            access,
            ..
        }
        | VirInstruction::Store {
            pointer,
            permission,
            access,
            ..
        }
        | VirInstruction::ObjectDeinitialize {
            pointer,
            permission,
            access,
        }
        | VirInstruction::StorageReset {
            pointer,
            permission,
            access,
        }
        | VirInstruction::ResourceStorageReset {
            pointer,
            permission,
            access,
        }
        | VirInstruction::EnumSetDiscriminant {
            pointer,
            permission,
            access,
            ..
        } => check_typed_loan_access(
            memory,
            frame,
            shadow,
            TypedLoanAccess {
                pointer: *pointer,
                permission: *permission,
                access: *access,
                kind: RuntimeLoanAccess::Write,
            },
            source_span,
        ),
        VirInstruction::Load {
            pointer,
            permission,
            access,
            ..
        }
        | VirInstruction::EnumDiscriminant {
            pointer,
            permission,
            access,
            ..
        } => check_typed_loan_access(
            memory,
            frame,
            shadow,
            TypedLoanAccess {
                pointer: *pointer,
                permission: *permission,
                access: *access,
                kind: RuntimeLoanAccess::Read,
            },
            source_span,
        ),
        VirInstruction::ResourceInitialize {
            destination,
            destination_permission,
            value,
            value_permission,
            access,
        } => {
            check_typed_loan_access(
                memory,
                frame,
                shadow,
                TypedLoanAccess {
                    pointer: *destination,
                    permission: *destination_permission,
                    access: *access,
                    kind: RuntimeLoanAccess::Write,
                },
                source_span,
            )?;
            let value_access = memory.kind(access.ty).map(|kind| match kind {
                VirMemoryTypeKind::Pointer {
                    kind: super::VirPointerKind::Reference,
                    mutability,
                    ..
                } => {
                    if *mutability == super::VirMutability::Mutable {
                        RuntimeLoanAccess::Move
                    } else {
                        RuntimeLoanAccess::Read
                    }
                }
                _ => RuntimeLoanAccess::Move,
            });
            check_permission_range_loan_access(
                frame,
                shadow,
                *value,
                *value_permission,
                value_access.ok_or_else(|| {
                    error(VirExecutionErrorKind::InvalidRuntimeState, source_span)
                })?,
                source_span,
            )
        }
        VirInstruction::ResourceTake {
            source,
            source_permission,
            access,
            ..
        } => check_typed_loan_access(
            memory,
            frame,
            shadow,
            TypedLoanAccess {
                pointer: *source,
                permission: *source_permission,
                access: *access,
                kind: RuntimeLoanAccess::Move,
            },
            source_span,
        ),
        VirInstruction::ObjectTransfer {
            destination,
            destination_permission,
            source,
            source_permission,
            access,
            source_mode,
            ..
        } => {
            check_typed_loan_access(
                memory,
                frame,
                shadow,
                TypedLoanAccess {
                    pointer: *destination,
                    permission: *destination_permission,
                    access: *access,
                    kind: RuntimeLoanAccess::Write,
                },
                source_span,
            )?;
            check_typed_loan_access(
                memory,
                frame,
                shadow,
                TypedLoanAccess {
                    pointer: *source,
                    permission: *source_permission,
                    access: *access,
                    kind: match source_mode {
                        VirObjectSourceMode::Copy => RuntimeLoanAccess::Read,
                        VirObjectSourceMode::Move => RuntimeLoanAccess::Move,
                    },
                },
                source_span,
            )
        }
        VirInstruction::ObjectDrop {
            pointer,
            permission,
            access,
            condition,
        } => {
            if bool_value(frame, *condition, source_span)? {
                check_typed_loan_access(
                    memory,
                    frame,
                    shadow,
                    TypedLoanAccess {
                        pointer: *pointer,
                        permission: *permission,
                        access: *access,
                        kind: RuntimeLoanAccess::Write,
                    },
                    source_span,
                )?;
            }
            Ok(())
        }
        VirInstruction::Free {
            pointer,
            permission,
        } => check_permission_range_loan_access(
            frame,
            shadow,
            *pointer,
            *permission,
            RuntimeLoanAccess::Free,
            source_span,
        ),
        VirInstruction::DropOwn {
            pointer,
            permission,
            condition,
        } => {
            if bool_value(frame, *condition, source_span)? {
                check_permission_range_loan_access(
                    frame,
                    shadow,
                    *pointer,
                    *permission,
                    RuntimeLoanAccess::Free,
                    source_span,
                )?;
            }
            Ok(())
        }
        VirInstruction::RawAddress {
            base,
            source_permission,
            raw_type,
            ..
        } => {
            let (access, mutability) = memory
                .raw_address_pointee(*raw_type)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
            check_typed_loan_access(
                memory,
                frame,
                shadow,
                TypedLoanAccess {
                    pointer: *base,
                    permission: *source_permission,
                    access,
                    kind: if mutability == super::VirMutability::Mutable {
                        RuntimeLoanAccess::Write
                    } else {
                        RuntimeLoanAccess::Read
                    },
                },
                source_span,
            )
        }
        VirInstruction::PermissionSplit { source, .. } => {
            shadow.reject_permission_transform(frame, *source, source_span)
        }
        VirInstruction::PermissionJoin { left, right, .. } => {
            shadow.reject_permission_transform(frame, *left, source_span)?;
            shadow.reject_permission_transform(frame, *right, source_span)
        }
        VirInstruction::Constant { .. }
        | VirInstruction::WordAdd { .. }
        | VirInstruction::Compare { .. }
        | VirInstruction::PointerCompare { .. }
        | VirInstruction::PointerDistance { .. }
        | VirInstruction::Allocate { .. }
        | VirInstruction::LocalStorage { .. }
        | VirInstruction::FieldAddress { .. }
        | VirInstruction::TupleElementAddress { .. }
        | VirInstruction::ObjectLeafAddress { .. }
        | VirInstruction::IndexAddress { .. }
        | VirInstruction::SliceRange { .. }
        | VirInstruction::SliceAddress { .. }
        | VirInstruction::PointerOffset { .. }
        | VirInstruction::PermissionMove { .. }
        | VirInstruction::LoanBegin { .. }
        | VirInstruction::LoanAliasShared { .. }
        | VirInstruction::LoanReborrow { .. }
        | VirInstruction::LoanEnd { .. }
        | VirInstruction::LoanAliasAuthority { .. }
        | VirInstruction::LoanReborrowAuthority { .. }
        | VirInstruction::LoanEndAuthority { .. }
        | VirInstruction::Check { .. }
        | VirInstruction::Call { .. } => Ok(()),
    }
}

#[derive(Clone, Copy)]
struct TypedLoanAccess {
    pointer: VirValueId,
    permission: VirValueId,
    access: VirMemoryAccess,
    kind: RuntimeLoanAccess,
}

fn check_typed_loan_access(
    memory: &VirMemorySchema,
    frame: &BlockFrame,
    shadow: &RuntimeLoanShadow,
    request: TypedLoanAccess,
    source_span: ByteSpan,
) -> Result<(), VirExecutionError> {
    let pointer = pointer_value(frame, request.pointer, source_span)?;
    let width = memory
        .layout(request.access.layout)
        .filter(|layout| layout.ty == request.access.ty)
        .map(|layout| layout.size_bytes)
        .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
    let end_bytes = pointer
        .offset_bytes
        .checked_add(width)
        .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
    shadow.check_access(
        frame,
        RuntimeLoanAccessRequest {
            permission: request.permission,
            pointer,
            start_bytes: pointer.offset_bytes,
            end_bytes,
            kind: request.kind,
        },
        source_span,
    )
}

fn check_permission_range_loan_access(
    frame: &BlockFrame,
    shadow: &RuntimeLoanShadow,
    pointer_id: VirValueId,
    permission_id: VirValueId,
    kind: RuntimeLoanAccess,
    source_span: ByteSpan,
) -> Result<(), VirExecutionError> {
    let pointer = pointer_value(frame, pointer_id, source_span)?;
    let permission = frame.permission(permission_id, source_span)?;
    shadow.check_access(
        frame,
        RuntimeLoanAccessRequest {
            permission: permission_id,
            pointer,
            start_bytes: permission.start_bytes,
            end_bytes: permission.end_bytes,
            kind,
        },
        source_span,
    )
}

#[derive(Clone, Copy)]
enum WriteKind {
    Initialize,
    Write,
    Store,
}

#[derive(Clone, Copy)]
struct MemoryAccessContext<'memory> {
    memory: &'memory VirMemorySchema,
    access: VirMemoryAccess,
    source_span: ByteSpan,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RuntimeInactiveVariant {
    enum_access: VirMemoryAccess,
    active: VirVariantId,
    required: VirVariantId,
}

impl<'memory> MemoryAccessContext<'memory> {
    const fn new(
        memory: &'memory VirMemorySchema,
        access: VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Self {
        Self {
            memory,
            access,
            source_span,
        }
    }
}

fn repeated_runtime_objects(
    access: VirMemoryAccess,
    object_size_bytes: u64,
    allocation_size_bytes: u64,
    tracks_variants: bool,
) -> Vec<RuntimeObject> {
    if object_size_bytes == 0 || !tracks_variants {
        return Vec::new();
    }
    let count = allocation_size_bytes / object_size_bytes;
    (0..count)
        .map(|index| RuntimeObject {
            offset_bytes: index * object_size_bytes,
            access,
        })
        .collect()
}

fn ensure_runtime_object_type(
    memory: &VirMemorySchema,
    shape: &VirObjectShape,
    source_span: ByteSpan,
) -> Result<(), VirExecutionError> {
    if !memory
        .type_capabilities(shape.access().ty)
        .is_some_and(crate::TypeCapabilities::pointer_free_trivial)
    {
        return Err(error(
            VirExecutionErrorKind::UnsupportedObjectEffectType {
                access: shape.access(),
            },
            source_span,
        ));
    }
    Ok(())
}

fn ensure_runtime_object_observation_type(
    memory: &VirMemorySchema,
    shape: &VirObjectShape,
    source_span: ByteSpan,
) -> Result<(), VirExecutionError> {
    let supported = memory
        .type_capabilities(shape.access().ty)
        .is_some_and(|capability| capability.size == crate::SizeCapability::Sized)
        && shape
            .resource_leaves()
            .iter()
            .all(|leaf| leaf.kind() != super::VirPointerKind::Raw);
    if !supported {
        return Err(error(
            VirExecutionErrorKind::UnsupportedObjectEffectType {
                access: shape.access(),
            },
            source_span,
        ));
    }
    Ok(())
}

fn ensure_runtime_object_drop_type(
    memory: &VirMemorySchema,
    shape: &VirObjectShape,
    source_span: ByteSpan,
) -> Result<(), VirExecutionError> {
    let supported = memory
        .type_capabilities(shape.access().ty)
        .is_some_and(|capability| {
            capability.size == crate::SizeCapability::Sized
                && matches!(
                    capability.drop,
                    crate::DropCapability::TrivialDrop | crate::DropCapability::BuiltinDrop
                )
        })
        && !shape.resource_leaves().is_empty()
        && shape
            .resource_leaves()
            .iter()
            .all(|leaf| leaf.kind() != super::VirPointerKind::Raw);
    if !supported {
        return Err(error(
            VirExecutionErrorKind::UnsupportedObjectEffectType {
                access: shape.access(),
            },
            source_span,
        ));
    }
    Ok(())
}

fn ensure_runtime_object_transfer_type(
    memory: &VirMemorySchema,
    shape: &VirObjectShape,
    destination_mode: VirObjectDestinationMode,
    source_mode: VirObjectSourceMode,
    source_span: ByteSpan,
) -> Result<(), VirExecutionError> {
    let capability = memory.type_capabilities(shape.access().ty);
    let supported = match source_mode {
        VirObjectSourceMode::Copy => {
            capability.is_some_and(|capability| {
                capability.value == crate::ValueCapability::Copy
                    && capability.size == crate::SizeCapability::Sized
            }) && shape.resource_leaves().iter().all(|leaf| {
                leaf.kind() == super::VirPointerKind::Reference
                    && leaf.mutability() == super::VirMutability::Const
            })
        }
        VirObjectSourceMode::Move => {
            capability.is_some_and(|capability| capability.size == crate::SizeCapability::Sized)
                && shape
                    .resource_leaves()
                    .iter()
                    .all(|leaf| leaf.kind() != super::VirPointerKind::Raw)
                && (matches!(destination_mode, VirObjectDestinationMode::Initialize)
                    || capability.is_some_and(crate::TypeCapabilities::pointer_free_trivial))
        }
    };
    if supported {
        Ok(())
    } else {
        Err(error(
            VirExecutionErrorKind::UnsupportedObjectEffectType {
                access: shape.access(),
            },
            source_span,
        ))
    }
}

fn runtime_storable_resource(
    memory: &VirMemorySchema,
    access: VirMemoryAccess,
    source_span: ByteSpan,
) -> Result<(VirMemoryAccess, super::VirPointerKind), VirExecutionError> {
    let Some(VirMemoryTypeKind::Pointer { pointee, kind, .. }) = memory.kind(access.ty) else {
        return Err(error(
            VirExecutionErrorKind::UnsupportedObjectEffectType { access },
            source_span,
        ));
    };
    if *kind == super::VirPointerKind::Raw {
        return Err(error(
            VirExecutionErrorKind::UnsupportedObjectEffectType { access },
            source_span,
        ));
    }
    let pointee = memory.access(*pointee).ok_or_else(|| {
        error(
            VirExecutionErrorKind::UnsupportedObjectEffectType { access },
            source_span,
        )
    })?;
    Ok((pointee, *kind))
}

/// Deterministic physical bits for tests and byte-wise native differential.
/// No execution path decodes these bits back into provenance or authority.
const fn opaque_runtime_pointer_bits(pointer: VirRuntimePointer) -> u64 {
    pointer
        .allocation
        .wrapping_add(1)
        .rotate_left(17)
        .wrapping_add(pointer.offset_bytes)
}

fn half_open_ranges_overlap(left: u64, right: u64, size_bytes: u64) -> bool {
    let Some(left_end) = left.checked_add(size_bytes) else {
        return true;
    };
    let Some(right_end) = right.checked_add(size_bytes) else {
        return true;
    };
    left < right_end && right < left_end
}

fn encode_u64(value: u64, size_bytes: u64, endianness: VirEndianness) -> Option<Vec<u8>> {
    let size = usize::try_from(size_bytes).ok()?;
    let mut encoded = vec![0; size];
    let value_bytes = value.to_le_bytes();
    let copied = size.min(value_bytes.len());
    match endianness {
        VirEndianness::Little => encoded[..copied].copy_from_slice(&value_bytes[..copied]),
        VirEndianness::Big => {
            for (destination, source) in encoded[size - copied..]
                .iter_mut()
                .rev()
                .zip(value_bytes[..copied].iter())
            {
                *destination = *source;
            }
        }
    }
    Some(encoded)
}

fn decode_u64(bytes: &[u8], endianness: VirEndianness) -> Option<u64> {
    let mut decoded = [0_u8; 8];
    match endianness {
        VirEndianness::Little => {
            if bytes
                .get(8..)
                .is_some_and(|bytes| bytes.iter().any(|byte| *byte != 0))
            {
                return None;
            }
            let copied = bytes.len().min(decoded.len());
            decoded[..copied].copy_from_slice(&bytes[..copied]);
        }
        VirEndianness::Big => {
            let significant_start = bytes.len().saturating_sub(decoded.len());
            if bytes[..significant_start].iter().any(|byte| *byte != 0) {
                return None;
            }
            let significant = &bytes[significant_start..];
            for (destination, source) in decoded[..significant.len()]
                .iter_mut()
                .zip(significant.iter().rev())
            {
                *destination = *source;
            }
        }
    }
    Some(u64::from_le_bytes(decoded))
}

#[allow(clippy::too_many_arguments)]
fn read_initialized_bytes(
    allocation: &Allocation,
    allocation_id: u64,
    start_bytes: u64,
    size_bytes: u64,
    access: VirMemoryAccess,
    object_leaf: bool,
    source_span: ByteSpan,
) -> Result<Vec<u8>, VirExecutionError> {
    let capacity = usize::try_from(size_bytes)
        .map_err(|_| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
    let mut bytes = Vec::with_capacity(capacity);
    for relative in 0..size_bytes {
        let offset_bytes = start_bytes
            .checked_add(relative)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, source_span))?;
        let Some(byte) = allocation.bytes.get(&offset_bytes).copied() else {
            let kind = if object_leaf {
                VirExecutionErrorKind::UninitializedObjectLeaf {
                    allocation: allocation_id,
                    offset_bytes,
                    access,
                }
            } else {
                VirExecutionErrorKind::UninitializedRead {
                    allocation: allocation_id,
                    offset_bytes,
                }
            };
            return Err(error(kind, source_span));
        };
        bytes.push(byte);
    }
    Ok(bytes)
}

fn transfer_target(
    frame: &BlockFrame,
    target: &VirBlockTarget,
    source_span: ByteSpan,
) -> Result<(VirBlockId, Vec<RuntimeBlockArgument>), VirExecutionError> {
    let mut transferred_permissions = BTreeSet::new();
    let arguments = target
        .arguments
        .iter()
        .map(|id| {
            let value = frame.value(*id, source_span)?.clone();
            let permission_consumed = if matches!(value, VirRuntimeValue::Permission(_)) {
                if !transferred_permissions.insert(*id) {
                    return Err(error(
                        VirExecutionErrorKind::PermissionDuplicated(*id),
                        source_span,
                    ));
                }
                frame.consumed_permissions.contains(id)
            } else {
                false
            };
            Ok(RuntimeBlockArgument {
                value,
                permission_consumed,
                loan_authority: frame.loan_authority(*id),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((target.block, arguments))
}

fn word_value(
    frame: &BlockFrame,
    id: VirValueId,
    source_span: ByteSpan,
) -> Result<u64, VirExecutionError> {
    let VirRuntimeValue::U64(value) = frame.value(id, source_span)? else {
        return Err(error(
            VirExecutionErrorKind::InvalidRuntimeState,
            source_span,
        ));
    };
    Ok(*value)
}

fn scalar_value(
    memory: &VirMemorySchema,
    frame: &BlockFrame,
    id: VirValueId,
    access: VirMemoryAccess,
    source_span: ByteSpan,
) -> Result<u64, VirExecutionError> {
    match memory.kind(access.ty) {
        Some(VirMemoryTypeKind::Bool) => bool_value(frame, id, source_span).map(u64::from),
        Some(VirMemoryTypeKind::Integer(
            super::VirIntegerType::U64 | super::VirIntegerType::Usize,
        )) => word_value(frame, id, source_span),
        _ => Err(error(
            VirExecutionErrorKind::InvalidRuntimeState,
            source_span,
        )),
    }
}

fn bool_value(
    frame: &BlockFrame,
    id: VirValueId,
    source_span: ByteSpan,
) -> Result<bool, VirExecutionError> {
    let VirRuntimeValue::Bool(value) = frame.value(id, source_span)? else {
        return Err(error(
            VirExecutionErrorKind::InvalidRuntimeState,
            source_span,
        ));
    };
    Ok(*value)
}

fn pointer_value(
    frame: &BlockFrame,
    id: VirValueId,
    source_span: ByteSpan,
) -> Result<VirRuntimePointer, VirExecutionError> {
    let VirRuntimeValue::Pointer(value) = frame.value(id, source_span)? else {
        return Err(error(
            VirExecutionErrorKind::InvalidRuntimeState,
            source_span,
        ));
    };
    Ok(*value)
}

fn join_permissions(
    left: VirRuntimePermission,
    right: VirRuntimePermission,
) -> Option<VirRuntimePermission> {
    if left.allocation != right.allocation
        || left.can_free_when_complete != right.can_free_when_complete
    {
        return None;
    }
    let (start_bytes, end_bytes) = if left.end_bytes == right.start_bytes {
        (left.start_bytes, right.end_bytes)
    } else if right.end_bytes == left.start_bytes {
        (right.start_bytes, left.end_bytes)
    } else {
        return None;
    };
    Some(VirRuntimePermission {
        allocation: left.allocation,
        start_bytes,
        end_bytes,
        can_free_when_complete: left.can_free_when_complete,
    })
}

fn runtime_values_match(values: &[VirRuntimeValue], types: &[VirType]) -> bool {
    values.len() == types.len()
        && values
            .iter()
            .zip(types)
            .all(|(value, ty)| runtime_matches_type(value, *ty))
}

const fn runtime_matches_type(value: &VirRuntimeValue, ty: VirType) -> bool {
    match (value, ty) {
        (VirRuntimeValue::U64(_), VirType::U64)
        | (VirRuntimeValue::Bool(_), VirType::Bool)
        | (VirRuntimeValue::Permission(_), VirType::Permission) => true,
        (VirRuntimeValue::Pointer(pointer), VirType::Pointer { access }) => {
            pointer.access.ty.get() == access.ty.get()
                && pointer.access.layout.get() == access.layout.get()
        }
        _ => false,
    }
}

fn error(kind: VirExecutionErrorKind, source_span: ByteSpan) -> VirExecutionError {
    VirExecutionError {
        kind,
        source_span,
        trace: Vec::new(),
    }
}

fn empty_span() -> ByteSpan {
    ByteSpan::new(0, 0).expect("empty span is valid")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_numeric_domains_do_not_replace_nominal_path_identity() {
        let interpreter = interpreter_with_enum_tag(None);
        let root = crate::VirPointerPaths::root(WORD);
        let base = VirRuntimePointer {
            allocation: 0,
            offset_bytes: 8,
            access: WORD,
            view_range: None,
            domain: crate::VirPointerDomain::Restricted(super::super::VirLoanRange {
                start_bytes: 8,
                end_bytes: 16,
            }),
            paths: root,
        };
        let left = VirValueId::new(0);
        let right = VirValueId::new(1);
        for domain in [
            root.domain,
            None,
            root.domain
                .unwrap()
                .extend(&[crate::VirObjectPathSegment::TupleElement(0)]),
        ] {
            let other = VirRuntimePointer {
                paths: crate::VirPointerPaths {
                    object: domain,
                    domain,
                },
                ..base
            };
            let frame = BlockFrame {
                values: BTreeMap::from([
                    (left, VirRuntimeValue::Pointer(base)),
                    (right, VirRuntimeValue::Pointer(other)),
                ]),
                consumed_permissions: BTreeSet::new(),
                loan_authorities: BTreeMap::new(),
            };
            let result = interpreter.pointer_pair(&frame, left, right, empty_span());
            if domain == root.domain {
                assert!(result.is_ok());
            } else {
                assert!(matches!(
                    result.unwrap_err().kind(),
                    VirExecutionErrorKind::PointerRelationIncompatible
                ));
            }
        }
    }

    #[test]
    fn partial_construction_clears_payloads_on_every_scope_exit() {
        for (source, count) in [
            (
                include_str!("../../spec/cases/verify/partial-construction.nera"),
                1,
            ),
            (
                include_str!("../../spec/cases/verify/partial-construction-loop.nera"),
                2,
            ),
        ] {
            for condition in ["true", "false"] {
                let source = source.replace("return true;", &format!("return {condition};"));
                let output = crate::analyze(&crate::SourceFile::from_text(
                    "partial-construction.nera",
                    &source,
                ));
                let resolved = output.vir().unwrap().resolve().unwrap();
                let mut interpreter = Interpreter::new(VirInterpreterConfig::default());
                interpreter.run_inner(resolved.runtime()).unwrap();
                let heaps: Vec<_> = interpreter
                    .allocations
                    .values()
                    .filter(|allocation| matches!(allocation.kind, RuntimeAllocationKind::Heap))
                    .collect();
                assert_eq!(heaps.len(), count);
                assert!(heaps.iter().all(|allocation| !allocation.live));
                assert!(
                    interpreter
                        .allocations
                        .values()
                        .all(|allocation| allocation.resource_payloads.is_empty())
                );
            }
        }
    }

    #[test]
    fn partial_refill_retires_every_heap_allocation_and_payload() {
        for condition in ["true", "false"] {
            let source = include_str!("../../spec/cases/verify/partial-refill.nera")
                .replace("return true;", &format!("return {condition};"));
            let output = crate::analyze(&crate::SourceFile::from_text(
                "partial-refill.nera",
                &source,
            ));
            let resolved = output.vir().unwrap().resolve().unwrap();
            let mut interpreter = Interpreter::new(VirInterpreterConfig::default());
            assert_eq!(
                interpreter.run_inner(resolved.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(42)]
            );
            let heaps: Vec<_> = interpreter
                .allocations
                .values()
                .filter(|allocation| matches!(allocation.kind, RuntimeAllocationKind::Heap))
                .collect();
            assert_eq!(heaps.len(), 3);
            assert!(heaps.iter().all(|allocation| !allocation.live));
            assert!(
                interpreter
                    .allocations
                    .values()
                    .all(|allocation| allocation.resource_payloads.is_empty())
            );
        }
    }
    use crate::{
        VirAbiClass, VirField, VirFieldId, VirFieldLayout, VirIntegerType, VirLayout, VirLayoutId,
        VirMemoryType, VirTargetDataLayout, VirTypeId, VirVariant, VirVariantCaseLayout,
        VirVariantLayout,
    };

    const WORD: VirMemoryAccess = VirMemoryAccess::new(VirTypeId::new(0), VirLayoutId::new(0));
    const ENUM: VirMemoryAccess = VirMemoryAccess::new(VirTypeId::new(1), VirLayoutId::new(1));

    #[test]
    fn borrow_formation_checks_concrete_bool_and_resource_payloads() {
        for (source, invalid_bool) in [
            (
                "fn main() -> u64 { let value = true; let reference = &value; return 0; }",
                true,
            ),
            (
                "struct Holder { owner: Own<u64>, } fn main() -> u64 {
             let owner = alloc<u64>(1); *owner = 1; let value = Holder { owner: owner };
             let reference = &value; return 0; }",
                false,
            ),
        ] {
            let output = crate::analyze(&crate::SourceFile::from_text("borrow-bytes.nera", source));
            let unit = output.vir().unwrap().as_unit();
            let (effect, access) = unit.runtime.functions[0]
                .blocks
                .iter()
                .flat_map(|block| &block.instructions)
                .find_map(|instruction| match instruction.instruction {
                    VirInstruction::LoanBegin {
                        effect,
                        reference_result:
                            VirValue {
                                ty: VirType::Pointer { access },
                                ..
                            },
                        ..
                    } => Some((effect, access)),
                    _ => None,
                })
                .unwrap();
            let layout = unit.memory.layout(access.layout).unwrap();
            let mut interpreter = Interpreter::new(VirInterpreterConfig::default());
            interpreter.allocations.insert(
                0,
                Allocation {
                    size_bytes: layout.size_bytes,
                    alignment: layout.alignment,
                    live: true,
                    kind: RuntimeAllocationKind::LocalStorage,
                    bytes: (0..layout.size_bytes)
                        .map(|offset| (offset, if invalid_bool { 2 } else { 0 }))
                        .collect(),
                    objects: Vec::new(),
                    resource_payloads: BTreeMap::new(),
                },
            );
            let failure = interpreter
                .check_borrow_value(
                    &unit.memory,
                    VirRuntimePointer {
                        allocation: 0,
                        offset_bytes: 0,
                        access,
                        paths: crate::VirPointerPaths::root(access),
                        view_range: None,
                        domain: crate::VirPointerDomain::Allocation,
                    },
                    effect.reference,
                    crate::VirLoanRange {
                        start_bytes: 0,
                        end_bytes: layout.size_bytes,
                    },
                    empty_span(),
                )
                .unwrap_err();
            assert!(
                if invalid_bool {
                    matches!(
                        failure.kind(),
                        VirExecutionErrorKind::InvalidObjectRepresentation { .. }
                    )
                } else {
                    matches!(
                        failure.kind(),
                        VirExecutionErrorKind::MissingResourcePayload { .. }
                    )
                },
                "{failure:?}"
            );
        }
    }

    #[test]
    fn enum_payload_faults_distinguish_inactive_invalid_and_uninitialized_tags() {
        let memory = enum_schema();
        let payload = VirRuntimePointer {
            allocation: 0,
            offset_bytes: 8,
            access: WORD,
            paths: crate::VirPointerPaths::root(WORD),
            view_range: None,
            domain: crate::VirPointerDomain::Allocation,
        };

        let inactive = interpreter_with_enum_tag(Some(1));
        assert_eq!(
            inactive
                .check_scalar_active_access(&memory, payload, empty_span())
                .expect_err("variant 0 payload is inactive under variant 1")
                .kind(),
            &VirExecutionErrorKind::InactiveVariantAccess {
                allocation: 0,
                offset_bytes: 8,
                enum_access: ENUM,
                active: VirVariantId::new(1),
                required: VirVariantId::new(0),
            }
        );

        let invalid = interpreter_with_enum_tag(Some(9));
        assert!(matches!(
            invalid
                .check_scalar_active_access(&memory, payload, empty_span())
                .expect_err("unknown discriminant is invalid")
                .kind(),
            VirExecutionErrorKind::InvalidObjectRepresentation {
                allocation: 0,
                offset_bytes: 0,
                access: ENUM,
            }
        ));

        let root = VirRuntimePointer {
            allocation: 0,
            offset_bytes: 0,
            access: ENUM,
            paths: crate::VirPointerPaths::root(ENUM),
            view_range: None,
            domain: crate::VirPointerDomain::Allocation,
        };
        let permission = VirRuntimePermission {
            allocation: 0,
            start_bytes: 0,
            end_bytes: 16,
            can_free_when_complete: false,
        };
        assert_eq!(
            interpreter_with_enum_tag(Some(1))
                .enum_discriminant(&memory, root, permission, ENUM, empty_span())
                .expect("declared tag reads as its discriminant"),
            1
        );
        assert!(matches!(
            interpreter_with_enum_tag(Some(9))
                .enum_discriminant(&memory, root, permission, ENUM, empty_span())
                .expect_err("invalid tag must not become a runtime integer")
                .kind(),
            VirExecutionErrorKind::InvalidObjectRepresentation { access: ENUM, .. }
        ));

        let uninitialized = interpreter_with_enum_tag(None);
        assert!(matches!(
            uninitialized
                .check_scalar_active_access(&memory, payload, empty_span())
                .expect_err("missing discriminant bytes are uninitialized")
                .kind(),
            VirExecutionErrorKind::UninitializedObjectLeaf {
                allocation: 0,
                offset_bytes: 0,
                access: ENUM,
            }
        ));
    }

    #[test]
    fn runtime_object_registry_budget_fails_closed() {
        let memory = enum_schema();
        let shape = memory.object_shape(ENUM).expect("enum shape");
        let mut interpreter = interpreter_with_enum_tag(Some(0));
        interpreter.allocations.get_mut(&0).unwrap().objects = (0
            ..VIR_INTERPRETER_MAX_OBJECT_ROOTS)
            .map(|offset| RuntimeObject {
                offset_bytes: u64::try_from(offset).unwrap(),
                access: ENUM,
            })
            .collect();
        let pointer = VirRuntimePointer {
            allocation: 0,
            offset_bytes: u64::try_from(VIR_INTERPRETER_MAX_OBJECT_ROOTS).unwrap(),
            access: ENUM,
            paths: crate::VirPointerPaths::root(ENUM),
            view_range: None,
            domain: crate::VirPointerDomain::Allocation,
        };
        assert_eq!(
            interpreter
                .register_runtime_object(pointer, &shape, empty_span())
                .expect_err("registry must not truncate and continue")
                .kind(),
            &VirExecutionErrorKind::ObjectRootLimitExceeded {
                allocation: 0,
                limit: VIR_INTERPRETER_MAX_OBJECT_ROOTS,
            }
        );
    }

    fn interpreter_with_enum_tag(discriminant: Option<u64>) -> Interpreter {
        let mut bytes = BTreeMap::new();
        if let Some(discriminant) = discriminant {
            for (offset, byte) in discriminant.to_le_bytes().into_iter().enumerate() {
                bytes.insert(u64::try_from(offset).unwrap(), byte);
            }
        }
        let mut interpreter = Interpreter::new(VirInterpreterConfig::default());
        interpreter.allocations.insert(
            0,
            Allocation {
                size_bytes: 16,
                alignment: 8,
                kind: RuntimeAllocationKind::LocalStorage,
                live: true,
                bytes,
                objects: vec![RuntimeObject {
                    offset_bytes: 0,
                    access: ENUM,
                }],
                resource_payloads: BTreeMap::new(),
            },
        );
        interpreter
    }

    fn enum_schema() -> VirMemorySchema {
        VirMemorySchema {
            target: VirTargetDataLayout {
                endianness: VirEndianness::Little,
                pointer_size_bytes: 8,
                pointer_alignment: 8,
                usize_size_bytes: 8,
                usize_alignment: 8,
            },
            types: vec![
                VirMemoryType {
                    id: WORD.ty,
                    kind: VirMemoryTypeKind::Integer(VirIntegerType::U64),
                    layout: WORD.layout,
                },
                VirMemoryType {
                    id: ENUM.ty,
                    kind: VirMemoryTypeKind::Enum {
                        variants: vec![VirVariantId::new(0), VirVariantId::new(1)],
                    },
                    layout: ENUM.layout,
                },
            ],
            type_capabilities: vec![
                crate::TypeCapabilities {
                    value: crate::ValueCapability::Copy,
                    drop: crate::DropCapability::TrivialDrop,
                    contains_resource: false,
                    size: crate::SizeCapability::Sized,
                };
                2
            ],
            layouts: vec![
                VirLayout {
                    id: WORD.layout,
                    ty: WORD.ty,
                    size_bytes: 8,
                    alignment: 8,
                    abi: VirAbiClass::Scalar,
                    fields: vec![],
                    variants: None,
                },
                VirLayout {
                    id: ENUM.layout,
                    ty: ENUM.ty,
                    size_bytes: 16,
                    alignment: 8,
                    abi: VirAbiClass::Aggregate,
                    fields: vec![],
                    variants: Some(VirVariantLayout {
                        tag_size_bytes: 8,
                        tag_alignment: 8,
                        cases: vec![
                            VirVariantCaseLayout {
                                variant: VirVariantId::new(0),
                                payload_offset_bytes: 8,
                                fields: vec![VirFieldLayout {
                                    field: VirFieldId::new(0),
                                    offset_bytes: 0,
                                }],
                            },
                            VirVariantCaseLayout {
                                variant: VirVariantId::new(1),
                                payload_offset_bytes: 8,
                                fields: vec![],
                            },
                        ],
                    }),
                },
            ],
            fields: vec![VirField {
                id: VirFieldId::new(0),
                owner: ENUM.ty,
                ty: WORD.ty,
            }],
            variants: vec![
                VirVariant {
                    id: VirVariantId::new(0),
                    owner: ENUM.ty,
                    fields: vec![VirFieldId::new(0)],
                    discriminant: 0,
                },
                VirVariant {
                    id: VirVariantId::new(1),
                    owner: ENUM.ty,
                    fields: vec![],
                    discriminant: 1,
                },
            ],
        }
    }
}
