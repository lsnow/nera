//! Nera compiler library.
//!
//! The compiler is intentionally kept as one crate while the frontend is
//! bootstrapped. Stable phase boundaries can be split into workspace members
//! later without changing the command-line interface.

#![forbid(unsafe_code)]

pub mod backend;
mod borrow_interface;
mod capability;
pub mod capability_profile;
pub mod diagnostic;
pub mod frontend;
pub mod lexer;
mod module_interface;
pub mod session;
pub mod source;
pub mod verification;
pub mod verifier;
pub mod vir;

pub use borrow_interface::{
    BorrowAccess, BorrowGuardAtom, BorrowProjection, BorrowResultAlternative, BorrowResultRelation,
    BorrowSliceBound, MAX_BORROW_RESULT_ALTERNATIVES, MAX_BORROW_RESULT_GUARD_ATOMS,
    MAX_BORROW_SOURCE_FIXPOINT_ITERATIONS, MAX_BORROW_SOURCE_RELATIONS,
    MAX_BORROW_SOURCE_SCC_FUNCTIONS,
};

pub use capability::{
    CapabilityFailureKind, DropCapability, SizeCapability, TYPE_CAPABILITY_MAX_DEPTH,
    TypeCapabilities, ValueCapability,
};
pub use capability_profile::{
    CapabilityAxis, CapabilityFeature, CapabilityProfile, CapabilityProfileError, CapabilityStatus,
    current_capability_profile,
};
pub use diagnostic::{ByteSpan, Diagnostic, Severity};
pub use frontend::{
    AstBlock, AstEnum, AstEnumTupleField, AstEnumVariant, AstEnumVariantPayload, AstExpression,
    AstExpressionKind, AstFieldInitializer, AstFile, AstFunction, AstIntegerPredicate,
    AstLogicalExpression, AstLogicalExpressionKind, AstMatchArm, AstNamedPattern, AstParameter,
    AstPattern, AstPatternKind, AstPlace, AstPlaceProjection, AstStatement, AstStatementKind,
    AstStruct, AstStructField, AstType, AstVariantInitializer, AstVariantPatternPayload,
    Core0CompatibilityError, CoreInstruction, CoreProgramProposal, CstFile, CstFunction,
    FrontendIssue, FrontendIssueKind, FrontendOutput, FrontendStatus, HirAbiClass, HirBlock,
    HirBody, HirBoundsSource, HirCall, HirCallingConvention, HirContract, HirContractId,
    HirDeclaration, HirEndianness, HirExpression, HirExpressionKind, HirField, HirFieldId,
    HirFieldInitializer, HirFieldLayout, HirForSource, HirFunction, HirFunctionId,
    HirFunctionSignature, HirFunctionType, HirGenericParameter, HirGenericParameterId,
    HirIntegerPredicate, HirIntegerType, HirLayout, HirLayoutId, HirLocal, HirLocalId, HirLoopId,
    HirMatchArm, HirModule, HirModuleId, HirModulePath, HirMutability, HirNodeId, HirPattern,
    HirPatternKind, HirPlace, HirPlaceAccess, HirPlaceBase, HirPlaceResolutionError,
    HirPlaceResolutionErrorKind, HirPointerOffset, HirPredicate, HirPredicateId, HirProgram,
    HirProgramTables, HirProgramValidationError, HirProjection, HirProjectionKind, HirRegion,
    HirRegionConstraint, HirRegionConstraintId, HirRegionId, HirRegionOrigin, HirRegionOwner,
    HirScopeId, HirSpecBinder, HirSpecBinderId, HirSpecBinderOwner, HirSpecClause, HirSpecClauseId,
    HirSpecClauseOwner, HirSpecContractPosition, HirSpecEnvironment, HirSpecLocation,
    HirSpecLoopInvariant, HirSpecLoopInvariantId, HirSpecProve, HirSpecProveId, HirSpecSnapshot,
    HirSpecTerm, HirSpecTermId, HirSpecTermKind, HirStatement, HirStatementKind,
    HirTargetDataLayout, HirTrustEntry, HirTrustEntryId, HirTrustPolicyKind, HirTrustScope,
    HirTypeDefinition, HirTypeId, HirTypeKind, HirUseMode, HirVariant, HirVariantCaseLayout,
    HirVariantId, HirVariantLayout, HirVersion, HirVisibility, Register, ResolvedHirPlace,
    ResolvedHirProjection, ResolvedHirProjectionKind, SpannedCoreInstruction, analyze,
    project_core0_compat,
};
pub use lexer::{Keyword, LexErrorKind, LexIssue, Lexed, Punctuation, Token, TokenKind, lex};
pub use module_interface::{
    InterfaceArtifact, InterfaceArtifactError, InterfaceArtifactVersion,
    InterfaceDeclarationIdentity, InterfaceEffectSkeleton, InterfaceField, InterfaceFunction,
    InterfaceInputIdentity, InterfaceInstanceIdentity, InterfaceLayout, InterfaceMemoryRole,
    InterfaceModule, InterfaceModuleIdentity, InterfaceNominalKind, InterfaceParameterEffect,
    InterfacePrecondition, InterfaceSourceIdentity, InterfaceTransferMode, InterfaceType,
    InterfaceTypeDeclaration, InterfaceVariant,
};
pub use source::SourceFile;
pub use verifier::{
    AbstractAllocation, AbstractAllocationError, AbstractAllocationId, AbstractBool,
    AbstractByteRange, AbstractLoan, AbstractObjectOffsets, AbstractPermission, AbstractPointer,
    AbstractProvenance, AbstractValue, AccessPermission, ActiveVariantState, AffineExpression,
    ByteRange, ByteRangeError, ByteSet, CfgAnalysisConfig, CfgAnalysisError, CfgBlockAnalysis,
    CfgObligation, CfgObligationOrigin, ConditionalResourceState, ContractApplicationError,
    ContractFactOrigin, EnumDiscriminantFact, FreeCapability, FunctionCfgAnalysis,
    FunctionPostconditionCheck, FunctionReturnState, FunctionVerification, GuaranteedAlignment,
    GuaranteedAlignmentError, GuardedStatePrecisionLoss, InitializationClass, InitializationState,
    InstructionSequenceTransfer, InstructionTransfer, LivenessState, LoanActivity,
    LoanPrecisionLoss, MemoryFootprint, MovePathState, ObjectState, ObjectStateKey,
    ObligationStatus, OwnershipState, PathCondition, PathFact, PermissionAuthority,
    PermissionAvailability, ProgramVerification, ResourceCase, ResourceJoinError,
    ResourceObligation, ResourceObligationKind, ResourcePayloadKey, ResourceState,
    ResourceStateDefinitionError, SpecFailure, SpecProof, SymbolicRangeBound, TransferError,
    TrustReportEntry, TypedResourcePayload, U64Interval, U64IntervalError,
    VERIFIER_ACTIVE_VARIANT_MAX_ALTERNATIVES, VERIFIER_BYTE_SET_MAX_RANGES,
    VERIFIER_MAX_ACTIVE_LOANS_PER_CASE, VERIFIER_MAX_ALIASES_PER_LOAN, VERIFIER_MAX_REBORROW_DEPTH,
    VERIFIER_MAX_REGION_CONSTRAINTS_PER_FUNCTION, VERIFIER_OBJECT_OFFSET_MAX_CANDIDATES,
    VERIFIER_OBJECT_STATE_MAX_ENTRIES, VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES,
    VIR_V0_MAX_ALLOCATION_BYTES, VIR_V0_WORD_BYTES, VerificationError, VerifierDiagnostic,
    VerifierDiagnosticKind, VerifierFinding, VerifierFindingSite, VerifierSpecEntity,
    VerifierTrustReport, analyze_function_cfg, analyze_function_cfg_with_config,
    analyze_function_cfg_with_entry, transfer_instruction, transfer_instruction_sequence,
    transfer_instruction_sequence_with_memory, transfer_instruction_with_memory, verify_program,
};
mod spec_assertion;
pub use frontend::hir::{HirSpecAssertion, HirSpecAssertionId, HirSpecAssertionKind, HirSpecRoot};
pub use spec_assertion::{
    SpecAccess, SpecAssertionKind, SpecMemoryClaim, SpecMemoryIndex, SpecMemoryProjection,
    SpecMemoryRange,
};
pub use vir::{VirSpecAssertion, VirSpecAssertionId, VirSpecAssertionKind};

pub use vir::{
    ResolvedRuntimeVirView, ResolvedVirUnit, RuntimeVirProgram, RuntimeVirView,
    SpannedVirInstruction, SpannedVirTerminator, VIR_AGGREGATE_ABI_MAX_DIRECT_BYTES,
    VIR_AGGREGATE_ABI_MAX_DIRECT_LEAVES, VIR_INTERPRETER_MAX_ACTIVE_LOANS,
    VIR_INTERPRETER_MAX_ALIASES_PER_LOAN, VIR_INTERPRETER_MAX_OBJECT_ROOTS,
    VIR_INTERPRETER_MAX_REBORROW_DEPTH, VIR_INTERPRETER_MAX_RESOURCE_PAYLOADS,
    VIR_OBJECT_SHAPE_MAX_DEPTH, VIR_OBJECT_SHAPE_MAX_NODES, VIR_SYSTEM_SEMANTICS_V1,
    VIR_SYSTEM_SEMANTICS_V2, ValidatedVirUnit, VirAbiBinding, VirAbiClass, VirAbiEnvironment,
    VirAbiError, VirAbiErrorKind, VirAbiLeaf, VirAbiSignature, VirAbiValue, VirAddressStep,
    VirArithmeticSemantics, VirBasicBlock, VirBlockId, VirBlockTarget, VirBorrowEnvironment,
    VirBorrowRegion, VirBorrowRegionConstraint, VirBorrowRegionConstraintId, VirBorrowRegionId,
    VirBorrowRegionOrigin, VirBorrowRegionScope, VirCallTarget, VirComparisonSemantics,
    VirConstant, VirContract, VirContractAccess, VirContractBinder, VirContractBinderId,
    VirContractCallBinding, VirContractFree, VirContractId, VirContractInitialization,
    VirContractLiveness, VirContractOwnership, VirContractPermission, VirContractPointer,
    VirContractPosition, VirContractResource, VirContractResourceId, VirContractResourceSummary,
    VirDivergenceSemantics, VirEndianness, VirExecution, VirExecutionError, VirExecutionErrorKind,
    VirFailureDisposition, VirField, VirFieldId, VirFieldLayout, VirFunction, VirFunctionAbi,
    VirFunctionId, VirGeneratedReason, VirIndexBounds, VirInstruction, VirIntegerPredicate,
    VirIntegerType, VirInterfaceEffect, VirInterfaceStorage, VirInterfaceTransfer,
    VirInterpreterConfig, VirLayout, VirLayoutId, VirLoanAuthorityEffect, VirLoanEffect, VirLoanId,
    VirLoanKind, VirLoanRange, VirLocation, VirLocationOrigin, VirLoopBinding, VirLoopBoundary,
    VirLoopEdge, VirMemoryAccess, VirMemorySchema, VirMemorySchemaError, VirMemorySchemaErrorKind,
    VirMemoryType, VirMemoryTypeKind, VirMutability, VirNominalPath, VirObjectArrayShape,
    VirObjectByteRange, VirObjectDestinationMode, VirObjectLeaf, VirObjectPath,
    VirObjectPathSegment, VirObjectResourceLeaf, VirObjectShape, VirObjectShapeError,
    VirObjectShapeErrorKind, VirObjectSourceMode, VirObjectVariantShape, VirOrigin, VirOriginId,
    VirOriginKind, VirPointerDescription, VirPointerDomain, VirPointerKey, VirPointerKind,
    VirPointerOffsetSemantics, VirPointerPaths, VirPointerSource, VirPredicate, VirPredicateId,
    VirProveSemantics, VirProvenanceCatalog, VirRegionId, VirResolutionError,
    VirResolutionErrorKind, VirRuntimePermission, VirRuntimePointer, VirRuntimeSemanticProfile,
    VirRuntimeValue, VirSemanticProfileId, VirSequence, VirSequenceExtent, VirSignature, VirSource,
    VirSourceId, VirSourceMap, VirSourceMapErrorKind, VirSourceSpan, VirSpecBinder,
    VirSpecBinderId, VirSpecBinderOwner, VirSpecClause, VirSpecClauseId, VirSpecClauseKind,
    VirSpecClauseOrigin, VirSpecClauseOwner, VirSpecEnvironment, VirSpecLocation,
    VirSpecLoopInvariant, VirSpecLoopInvariantId, VirSpecProve, VirSpecProveId, VirSpecSnapshot,
    VirSpecTables, VirSpecTerm, VirSpecTermId, VirSpecTermKind, VirSpecType, VirSubobject,
    VirTargetDataLayout, VirTerminator, VirTraceEvent, VirTracePoint, VirTrustEntry,
    VirTrustEntryId, VirTrustPolicyKind, VirTrustScope, VirType, VirTypeId, VirUnit,
    VirUnitVersion, VirValidationError, VirValidationErrorKind, VirValue, VirValueId, VirVariant,
    VirVariantCaseLayout, VirVariantId, VirVariantLayout, interpret, interpret_with_config,
};
