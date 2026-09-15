//! Proof obligations and transfer results. These carry observations, not proof search.
use super::{
    AbstractAllocationId, AbstractByteRange, AccessPermission, ByteRange, ByteSpan,
    ContractFactOrigin, ResourceState, U64Interval, VirContractId, VirLoanId, VirMemoryAccess,
    VirSpecClauseId, VirValueId,
};

/// Whether one local proof obligation is discharged by the current facts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ObligationStatus {
    Proven,
    /// Current facts prove that the required condition is false.
    Refuted,
    /// Current facts are insufficient in either direction.
    Unknown,
}

impl ObligationStatus {
    #[must_use]
    pub const fn is_proven(self) -> bool {
        matches!(self, Self::Proven)
    }
}

/// One memory/resource condition required by a VIR instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ResourceObligationKind {
    /// The complete stable ledger, jointly with all scalar/resource clauses.
    LoopResourcesPreserved {
        invariant: crate::VirSpecLoopInvariantId,
    },
    /// A loop-local induction obligation, never an assumption/trust entry.
    LoopInvariantEstablished {
        invariant: crate::VirSpecLoopInvariantId,
        back_edge: bool,
    },
    PointerSameInstance {
        left: VirValueId,
        right: VirValueId,
    },
    PointerCompatibleDomain {
        left: VirValueId,
        right: VirValueId,
    },
    PointerDistanceNonnegative {
        begin: VirValueId,
        end: VirValueId,
    },
    PointerDomainContains {
        pointer: VirValueId,
        domain: AbstractByteRange,
        selection: AbstractByteRange,
    },
    /// The bounded slot cannot safely represent another concrete instance.
    /// `None` denotes exhaustion of the allocation identity slot budget.
    AllocationInstanceFresh {
        allocation: Option<AbstractAllocationId>,
    },
    LoanPairQueriesWithinBudget {
        queries: usize,
        limit: usize,
    },
    AllocationSizeNonZero {
        size: U64Interval,
    },
    AllocationSizeWithinLimit {
        size: U64Interval,
        limit: u64,
    },
    /// v0 needs an exact extent to construct its byte initialization map.
    AllocationExtentExact {
        size: U64Interval,
    },
    PointerProvenanceKnown {
        pointer: VirValueId,
    },
    AllocationTracked {
        allocation: AbstractAllocationId,
    },
    AllocationLive {
        allocation: AbstractAllocationId,
    },
    PointerOffsetNoOverflow {
        base: VirValueId,
        delta: U64Interval,
    },
    PointerOffsetWithinBounds {
        allocation: AbstractAllocationId,
        offset: U64Interval,
        size_bytes: u64,
    },
    PointerMemoryAccessMatches {
        pointer: VirValueId,
        expected: VirMemoryAccess,
        found: Option<VirMemoryAccess>,
    },
    IndexWithinBounds {
        index: VirValueId,
        values: U64Interval,
        length: u64,
    },
    IndexStrideNoOverflow {
        index: VirValueId,
        values: U64Interval,
        stride_bytes: u64,
    },
    SliceIndexWithinBounds {
        index: VirValueId,
        values: U64Interval,
        length: VirValueId,
        length_values: U64Interval,
    },
    SliceRangeOrdered {
        start: VirValueId,
        start_values: U64Interval,
        end: VirValueId,
        end_values: U64Interval,
    },
    SliceRangeWithinBounds {
        end: VirValueId,
        end_values: U64Interval,
        length_values: U64Interval,
    },
    SliceRangeStrideNoOverflow {
        length_values: U64Interval,
        stride_bytes: u64,
    },
    BorrowProjectionRangeOrdered {
        source_parameter: u32,
    },
    BorrowProjectionRangeWithinSource {
        source_parameter: u32,
    },
    AddressCalculationNoOverflow {
        base: VirValueId,
        delta: U64Interval,
    },
    AddressObjectWithinBounds {
        allocation: AbstractAllocationId,
        offset: U64Interval,
        object_bytes: u64,
        size_bytes: u64,
    },
    AddressObjectAligned {
        pointer: VirValueId,
        required_alignment: u64,
    },
    AccessWithinBounds {
        allocation: AbstractAllocationId,
        access: Option<ByteRange>,
        size_bytes: u64,
    },
    AccessAligned {
        pointer: VirValueId,
        required_alignment: u64,
    },
    MemoryInitialized {
        allocation: AbstractAllocationId,
        access: Option<ByteRange>,
    },
    MemoryUninitialized {
        allocation: AbstractAllocationId,
        access: Option<ByteRange>,
    },
    ObjectValueBytesInitialized {
        allocation: Option<AbstractAllocationId>,
        access: Option<ByteRange>,
        object: VirMemoryAccess,
    },
    ObjectValueBytesUninitialized {
        allocation: Option<AbstractAllocationId>,
        access: Option<ByteRange>,
        object: VirMemoryAccess,
    },
    ObjectRepresentationValid {
        allocation: Option<AbstractAllocationId>,
        access: Option<ByteRange>,
        object: VirMemoryAccess,
    },
    ObjectActiveVariantKnown {
        allocation: Option<AbstractAllocationId>,
        offset_bytes: Option<u64>,
        access: VirMemoryAccess,
    },
    ActiveVariantAllowsAccess {
        pointer: VirValueId,
        enum_access: VirMemoryAccess,
        enum_offset_bytes: u64,
    },
    ObjectAllocationLive {
        pointer: VirValueId,
        allocation: Option<AbstractAllocationId>,
    },
    ObjectWithinBounds {
        pointer: VirValueId,
        allocation: Option<AbstractAllocationId>,
        access: Option<ByteRange>,
        size_bytes: u64,
    },
    ObjectAligned {
        pointer: VirValueId,
        required_alignment: u64,
    },
    ObjectStateWithinBudget {
        allocation: AbstractAllocationId,
    },
    ObjectNonOverlapping {
        destination: VirValueId,
        source: VirValueId,
        size_bytes: u64,
    },
    ObjectTriviallyCopyable {
        access: VirMemoryAccess,
    },
    ObjectMoveSupported {
        access: VirMemoryAccess,
    },
    ObjectTriviallyDroppable {
        access: VirMemoryAccess,
    },
    ObjectBuiltinDroppable {
        access: VirMemoryAccess,
    },
    ObjectDropPayloadValid {
        allocation: Option<AbstractAllocationId>,
        offset_bytes: Option<u64>,
        access: VirMemoryAccess,
    },
    ObjectResourcePayloadEmpty {
        allocation: Option<AbstractAllocationId>,
        offset_bytes: Option<u64>,
        access: VirMemoryAccess,
    },
    AggregateAbiPayloadValid {
        allocation: Option<AbstractAllocationId>,
        offset_bytes: Option<u64>,
        access: VirMemoryAccess,
    },
    DropFlagKnown {
        condition: VirValueId,
    },
    ResourcePayloadLocationExact {
        pointer: VirValueId,
        access: VirMemoryAccess,
    },
    ResourcePayloadAvailable {
        allocation: Option<AbstractAllocationId>,
        offset_bytes: Option<u64>,
        access: VirMemoryAccess,
    },
    AllocationResourcePayloadEmpty {
        allocation: AbstractAllocationId,
    },
    PermissionAvailable {
        permission: VirValueId,
    },
    PermissionMatchesAllocation {
        permission: VirValueId,
        allocation: AbstractAllocationId,
    },
    PermissionCoversAccess {
        permission: VirValueId,
        access: Option<ByteRange>,
    },
    PermissionWritable {
        permission: VirValueId,
    },
    PointerAtAllocationBase {
        pointer: VirValueId,
    },
    AllocationOwned {
        allocation: AbstractAllocationId,
    },
    PermissionCanFree {
        permission: VirValueId,
    },
    PermissionCoversAllocation {
        permission: VirValueId,
        allocation: AbstractAllocationId,
    },
    OwnershipConserved {
        allocation: AbstractAllocationId,
    },
    PermissionSplitPointInRange {
        permission: VirValueId,
        split_at: U64Interval,
    },
    PermissionOperandsDistinct {
        left: VirValueId,
        right: VirValueId,
    },
    PermissionJoinCompatible {
        left: VirValueId,
        right: VirValueId,
    },
    LoanRangeContained {
        loan: VirLoanId,
        permission: VirValueId,
        range: ByteRange,
    },
    LoanCompatible {
        loan: Option<VirLoanId>,
        permission: VirValueId,
        access: Option<ByteRange>,
        required: AccessPermission,
    },
    /// Parent authority permits child creation: Active or Suspended, with
    /// matching authority/mutability and actual containment. Not read/write access.
    LoanParentActive {
        loan: VirLoanId,
        parent: VirLoanId,
    },
    LoanRegionIncluded {
        loan: VirLoanId,
        parent: VirLoanId,
    },
    LoanEndedExactlyOnce {
        loan: VirLoanId,
    },
    LoanWithinBudget {
        loan: VirLoanId,
        limit: usize,
    },
    LoanAliasWithinBudget {
        loan: VirLoanId,
        limit: usize,
    },
    LoanReborrowDepthWithinBudget {
        loan: VirLoanId,
        limit: usize,
    },
    CheckTrue {
        condition: VirValueId,
    },
    /// An opaque ID alone is not trusted; contract-aware transfer resolves it.
    CallContractAvailable {
        contract: VirContractId,
    },
    CallContractPrecondition {
        contract: VirContractId,
        clause: VirSpecClauseId,
        fact_origin: ContractFactOrigin,
    },
}

/// One deterministic obligation record tied to its exact source construct.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ResourceObligation {
    pub(super) kind: ResourceObligationKind,
    pub(super) status: ObligationStatus,
    pub(super) source_span: ByteSpan,
}

impl ResourceObligation {
    pub(in crate::verifier) const fn new(
        kind: ResourceObligationKind,
        status: ObligationStatus,
        source_span: ByteSpan,
    ) -> Self {
        Self {
            kind,
            status,
            source_span,
        }
    }

    #[must_use]
    pub const fn kind(&self) -> ResourceObligationKind {
        self.kind
    }

    #[must_use]
    pub const fn status(&self) -> ObligationStatus {
        self.status
    }

    #[must_use]
    pub const fn source_span(&self) -> ByteSpan {
        self.source_span
    }

    #[must_use]
    pub const fn is_proven(&self) -> bool {
        self.status.is_proven()
    }
}

/// Result of one instruction transfer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstructionTransfer {
    /// Complete call outcomes; `state` remains their conservative join for
    /// single-state clients and instruction-local evidence capture.
    pub(crate) cases: Option<Vec<ResourceState>>,
    pub(crate) queries: Option<Vec<crate::verifier::relation::audit::QueryObservation>>,
    pub(super) state: ResourceState,
    pub(super) obligations: Vec<ResourceObligation>,
}

impl InstructionTransfer {
    #[must_use]
    pub const fn state(&self) -> &ResourceState {
        &self.state
    }

    #[must_use]
    pub fn obligations(&self) -> &[ResourceObligation] {
        &self.obligations
    }

    #[must_use]
    pub fn all_obligations_proven(&self) -> bool {
        self.obligations.iter().all(ResourceObligation::is_proven)
    }
}

/// Result of transferring a straight-line instruction sequence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstructionSequenceTransfer {
    pub(super) state: ResourceState,
    pub(super) obligations: Vec<ResourceObligation>,
}

impl InstructionSequenceTransfer {
    #[must_use]
    pub const fn state(&self) -> &ResourceState {
        &self.state
    }

    #[must_use]
    pub fn obligations(&self) -> &[ResourceObligation] {
        &self.obligations
    }

    #[must_use]
    pub fn all_obligations_proven(&self) -> bool {
        self.obligations.iter().all(ResourceObligation::is_proven)
    }
}
