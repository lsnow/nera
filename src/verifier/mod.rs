//! Static memory-verification infrastructure.
//!
//! Stage 5.1 defines the abstract resource domain, stage 5.2 applies local
//! instruction transfer, stage 5.3 computes function CFG fixed points, and
//! stage 5.4 adds checked contracts plus user-facing diagnostics. Stages
//! 5.5–5.7 pressure-test and accept that shared core against real cases,
//! mutations, property models and deterministic fuzzing. Stage 6.5.5 extends
//! the same allocation/CFG domain with typed aggregate object state and
//! object-effect transfer; stage 7.1.4 adds bounded guarded cases and
//! obligation-directed replay without creating a second verifier. Stage
//! 7.2.4 adds canonical loan facts, authority-aware transfer and conservative
//! CFG join/widen to that same resource state.

mod borrow_interface;
mod cfg;
mod contract;
mod finding;
mod guarded;
pub mod provenance;
pub mod relation;
mod resource;
mod spec;
pub mod summary;
mod transfer;
mod verify;

pub use cfg::{
    CfgAnalysisConfig, CfgAnalysisError, CfgBlockAnalysis, CfgObligation, CfgObligationOrigin,
    FunctionCfgAnalysis, FunctionReturnState, analyze_function_cfg,
    analyze_function_cfg_with_config, analyze_function_cfg_with_entry,
};
pub use contract::{ContractApplicationError, ContractFactOrigin};
pub use finding::{VerifierFinding, VerifierFindingSite, VerifierSpecEntity};
pub use guarded::{ConditionalResourceState, GuardedStatePrecisionLoss};

pub use resource::{
    AbstractAllocation, AbstractAllocationError, AbstractAllocationId, AbstractBool,
    AbstractByteRange, AbstractLoan, AbstractObjectOffsets, AbstractPermission, AbstractPointer,
    AbstractProvenance, AbstractValue, AccessPermission, ActiveVariantState, AffineExpression,
    ByteRange, ByteRangeError, ByteSet, EnumDiscriminantFact, FreeCapability, GuaranteedAlignment,
    GuaranteedAlignmentError, InitializationClass, InitializationState, LivenessState,
    LoanActivity, LoanPrecisionLoss, MemoryFootprint, MovePathState, ObjectState, ObjectStateKey,
    OwnershipState, PathCondition, PathFact, PermissionAuthority, PermissionAvailability,
    ResourceCase, ResourceJoinError, ResourcePayloadKey, ResourceState,
    ResourceStateDefinitionError, SymbolicRangeBound, TypedResourcePayload, U64Interval,
    U64IntervalError, VERIFIER_ACTIVE_VARIANT_MAX_ALTERNATIVES, VERIFIER_BYTE_SET_MAX_RANGES,
    VERIFIER_MAX_ACTIVE_LOANS_PER_CASE, VERIFIER_MAX_ALIASES_PER_LOAN, VERIFIER_MAX_REBORROW_DEPTH,
    VERIFIER_MAX_REGION_CONSTRAINTS_PER_FUNCTION, VERIFIER_OBJECT_OFFSET_MAX_CANDIDATES,
    VERIFIER_OBJECT_STATE_MAX_ENTRIES, VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES,
};
pub use spec::{SpecProof, TrustReportEntry};
pub use transfer::{
    InstructionSequenceTransfer, InstructionTransfer, ObligationStatus, ResourceObligation,
    ResourceObligationKind, TransferError, VIR_V0_MAX_ALLOCATION_BYTES, VIR_V0_WORD_BYTES,
    transfer_instruction, transfer_instruction_sequence, transfer_instruction_sequence_with_memory,
    transfer_instruction_with_memory,
};
pub use verify::{
    FunctionPostconditionCheck, FunctionVerification, ProgramVerification, VerificationError,
    VerifierDiagnostic, VerifierDiagnosticKind, VerifierTrustReport, verify_program,
};
