//! Presentation only: exhaustive vocabulary, never resource transfer or proof rules.
use crate::ResourceObligationKind as K;

pub(super) fn condition(kind: K) -> String {
    let text = match kind {
        K::LoopResourcesPreserved { .. } => {
            "loop allocation identities, permissions and loans are preserved"
        }
        K::LoopInvariantEstablished {
            back_edge: false, ..
        } => "loop invariant holds on entry",
        K::LoopInvariantEstablished {
            back_edge: true, ..
        } => "loop invariant is preserved on the back edge",
        K::PointerSameInstance { .. } => "pointers refer to the same allocation instance",
        K::PointerCompatibleDomain { .. } => "pointer arithmetic domains are compatible",
        K::PointerDistanceNonnegative { .. } => "pointer distance is nonnegative",
        K::PointerDomainContains { .. } => "selected range stays inside the pointer domain",
        K::AllocationInstanceFresh { .. } => {
            "a fresh allocation instance is representable without losing an owner or loan"
        }
        K::LoanPairQueriesWithinBudget { .. } => {
            "loan-pair comparisons stay within the analysis budget"
        }
        K::AllocationSizeNonZero { .. } => "allocation size is nonzero",
        K::AllocationSizeWithinLimit { limit, .. } => {
            return format!("allocation size is at most {limit} bytes");
        }
        K::AllocationExtentExact { .. } => "allocation extent is known exactly",
        K::PointerProvenanceKnown { .. } => "pointer provenance is known",
        K::AllocationTracked { .. } => "allocation is tracked",
        K::AllocationLive { .. } | K::ObjectAllocationLive { .. } => "allocation is live",
        K::PointerOffsetNoOverflow { .. } | K::AddressCalculationNoOverflow { .. } => {
            "address calculation does not overflow"
        }
        K::PointerOffsetWithinBounds { .. } => "pointer offset stays within allocation bounds",
        K::PointerMemoryAccessMatches { .. } => {
            "pointer and accessed object have matching canonical types"
        }
        K::IndexWithinBounds { length, .. } => {
            return format!("index is below array length {length}");
        }
        K::IndexStrideNoOverflow { stride_bytes, .. } => {
            return format!("index multiplied by stride {stride_bytes} does not overflow");
        }
        K::SliceIndexWithinBounds { .. } => "slice index is below its runtime length",
        K::SliceRangeOrdered { .. } => "slice start is at most its end",
        K::SliceRangeWithinBounds { .. } => "slice end stays within its source length",
        K::SliceRangeStrideNoOverflow { .. } => "slice byte length does not overflow",
        K::BorrowProjectionRangeOrdered { .. } => {
            "borrow-result slice start is at most its end at the call"
        }
        K::BorrowProjectionRangeWithinSource { .. } => {
            "borrow-result slice end stays within the caller source view"
        }
        K::AddressObjectWithinBounds { .. }
        | K::ObjectWithinBounds { .. }
        | K::AccessWithinBounds { .. } => "memory access stays within allocation bounds",
        K::AddressObjectAligned {
            required_alignment, ..
        }
        | K::AccessAligned {
            required_alignment, ..
        }
        | K::ObjectAligned {
            required_alignment, ..
        } => return format!("address is aligned to {required_alignment} bytes"),
        K::MemoryInitialized { .. } | K::ObjectValueBytesInitialized { .. } => {
            "all accessed value bytes are initialized"
        }
        K::MemoryUninitialized { .. } | K::ObjectValueBytesUninitialized { .. } => {
            "destination value bytes are uninitialized"
        }
        K::ObjectRepresentationValid { .. } => "object has a valid active representation",
        K::ObjectActiveVariantKnown { .. } => "active enum variant is known",
        K::ActiveVariantAllowsAccess { .. } => "access addresses the active enum payload",
        K::ObjectStateWithinBudget { .. } => "object state fits the analysis budget",
        K::ObjectNonOverlapping { .. } => "source and destination object ranges do not overlap",
        K::ObjectTriviallyCopyable { .. } => "object supports trivial copy",
        K::ObjectMoveSupported { .. } => "object has a supported move representation",
        K::ObjectTriviallyDroppable { .. } => "object supports trivial drop",
        K::ObjectBuiltinDroppable { .. } => "object has supported builtin drop glue",
        K::ObjectDropPayloadValid { .. } => "owner payload is valid for exactly-once drop",
        K::ObjectResourcePayloadEmpty { .. } | K::AllocationResourcePayloadEmpty { .. } => {
            "no live resource payload is discarded"
        }
        K::AggregateAbiPayloadValid { .. } => {
            "aggregate resource payload satisfies the calling convention"
        }
        K::DropFlagKnown { .. } => "conditional initialization/drop state is known",
        K::ResourcePayloadLocationExact { .. } => "resource payload location is known exactly",
        K::ResourcePayloadAvailable { .. } => {
            "resource payload is available and has not been moved or dropped"
        }
        K::PermissionAvailable { .. } => "permission is available and has not been consumed",
        K::PermissionMatchesAllocation { .. } => "permission belongs to the accessed allocation",
        K::PermissionCoversAccess { .. } => "permission covers the accessed range",
        K::PermissionWritable { .. } => "permission allows writing",
        K::PointerAtAllocationBase { .. } => "released pointer is at the allocation base",
        K::AllocationOwned { .. } => "allocation is owned",
        K::PermissionCanFree { .. } => "permission allows releasing the allocation",
        K::PermissionCoversAllocation { .. } => "permission covers the whole allocation",
        K::OwnershipConserved { .. } => "ownership is conserved across this control-flow edge",
        K::PermissionSplitPointInRange { .. } => "permission split point lies inside its range",
        K::PermissionOperandsDistinct { .. } => "permission operands are distinct",
        K::PermissionJoinCompatible { .. } => "permissions are compatible for joining",
        K::LoanRangeContained { .. } => "borrowed range is contained in its parent authority",
        K::LoanCompatible { .. } => "access is compatible with outstanding loans",
        K::LoanParentActive { .. } => "parent loan permits creating this reborrow",
        K::LoanRegionIncluded { .. } => "child loan region is included in its parent region",
        K::LoanEndedExactlyOnce { .. } => "loan is ended exactly once",
        K::LoanWithinBudget { .. } => "active loans fit the analysis budget",
        K::LoanAliasWithinBudget { .. } => "loan aliases fit the analysis budget",
        K::LoanReborrowDepthWithinBudget { .. } => "reborrow depth fits the analysis budget",
        K::CheckTrue { .. } => "checked condition is true",
        K::CallContractAvailable { .. } => "callee contract is available",
        K::CallContractPrecondition { .. } => "callee precondition holds for these arguments",
    };
    text.to_owned()
}
