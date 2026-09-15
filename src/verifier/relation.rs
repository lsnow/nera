//! Context-bound observations of numeric fast paths and bounded relation queries.
//!
//! These are derivation traces, not trusted certificates or state mutations.
//! A proposal is replayed against a fresh whole-program verification, never
//! against premises supplied by the proposal itself.

pub mod audit;
mod capture;
pub mod difference;
pub(super) mod kernel;
mod local;
pub mod range;
pub mod state;

use super::{
    AbstractAllocationId, AbstractPointer, CfgAnalysisConfig, ObligationStatus, PathCondition,
    ResourceObligationKind, U64Interval, VerificationError, VerifierFinding,
};
use crate::{ResolvedVirUnit, VirInstruction, VirMemoryAccess, VirType, VirValueId};

pub(super) use capture::capture;
pub(super) use local::compare;

/// Version of the trusted Rust observation protocol, not a Lean certificate.
pub const RELATION_KERNEL_VERSION: u32 = 19;

/// Canonical instruction-scoped term. Derived slots refer to intermediate
/// numeric results of that instruction, not freshly evaluated source syntax.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RelationTerm {
    Value {
        value: VirValueId,
        ty: VirType,
    },
    PointerOffset {
        pointer: VirValueId,
        access: VirMemoryAccess,
    },
    Constant(u64),
    Derived(u8),
}

/// Comparison normal form: greater-than goals are expressed by swapping terms.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RelationComparison {
    LessThan,
    LessOrEqual,
    Equal,
    NotEqual,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RelationArithmetic {
    Add,
    Multiply,
}

/// Closed arithmetic/range goals, independent of ResourceState. Range endpoints
/// and widths are allocation-relative bytes, with half-open semantics.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RelationGoal {
    Compare {
        comparison: RelationComparison,
        left: RelationTerm,
        right: RelationTerm,
    },
    NoOverflow {
        operation: RelationArithmetic,
        left: RelationTerm,
        right: RelationTerm,
    },
    Ordered {
        start: RelationTerm,
        end: RelationTerm,
    },
    Contained {
        allocation: AbstractAllocationId,
        start: RelationTerm,
        size_bytes: u64,
    },
    Disjoint {
        left: RelationTerm,
        right: RelationTerm,
        size_bytes: u64,
    },
    Aligned {
        pointer: RelationTerm,
        required_alignment: u64,
    },
}

/// Facts actually consulted at the query site. Source and path provenance are
/// supplied by the enclosing observation, not by an unchecked caller.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RelationPremise {
    Ranges {
        outer: Box<crate::AbstractByteRange>,
        inner: Box<crate::AbstractByteRange>,
    },
    Interval {
        term: RelationTerm,
        interval: U64Interval,
    },
    Pointer {
        term: RelationTerm,
        fact: Box<AbstractPointer>,
    },
    Allocation {
        allocation: AbstractAllocationId,
        size_bytes: u64,
        alignment: u64,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RelationRule {
    SymbolicPermissionContainment,
    BoundedDifference,
    IntervalComparison,
    CheckedEndpointArithmetic,
    AllocationContainment,
    AllocationOrAffineDisjointness,
    GuaranteedOrExactAlignment,
}

/// Untrusted, inspectable query/derivation proposal. Changing any field requires
/// replay; no compiler API installs this value as a fact or permission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationEvidence {
    pub finding: VerifierFinding,
    pub case_ordinal: usize,
    pub obligation_ordinal: usize,
    pub config: CfgAnalysisConfig,
    pub guard: PathCondition,
    pub instruction: VirInstruction,
    pub obligation: ResourceObligationKind,
    pub goal: RelationGoal,
    pub premises: Vec<RelationPremise>,
    pub rule: RelationRule,
    pub status: ObligationStatus,
    pub kernel_version: u32,
    pub difference: Option<difference::DifferenceEvidence>,
    pub bounds: Vec<range::BoundEvidence>,
    pub disjoint: Option<Box<range::DisjointEvidence>>,
}

/// Recompute the production CFG/contract analysis and compare the entire
/// context-bound observation. This is deliberately not a second proof checker,
/// and does not promote a numeric success to whole-program memory safety.
pub fn replay_relation_evidence(
    program: &ResolvedVirUnit<'_>,
    config: CfgAnalysisConfig,
    proposal: &RelationEvidence,
) -> Result<bool, VerificationError> {
    if proposal.config != config {
        return Ok(false);
    }
    let verification = super::verify_program(program, config)?;
    Ok(verification
        .functions()
        .get(&proposal.finding.site().function())
        .is_some_and(|f| {
            f.cfg()
                .relation_evidence()
                .iter()
                .any(|actual| actual == proposal)
        }))
}
