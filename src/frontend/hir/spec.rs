//! Typed, runtime-independent specification HIR arenas.

use super::{
    HirContractId, HirFunctionId, HirLocalId, HirLoopId, HirPredicateId, HirSpecBinderId,
    HirSpecClauseId, HirSpecLoopInvariantId, HirSpecProveId, HirSpecTermId, HirTrustEntryId,
    HirTypeId,
};
use crate::ByteSpan;

/// Entry/exit side of one function contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirSpecContractPosition {
    Requires,
    Ensures,
}

/// Stable logical program point. Stage 6.4.5 lowers function entry/result;
/// loop heads are named now but non-trivial invariants remain gated.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirSpecLocation {
    FunctionEntry {
        function: HirFunctionId,
    },
    FunctionResult {
        function: HirFunctionId,
    },
    LoopHead {
        function: HirFunctionId,
        loop_id: HirLoopId,
    },
}

impl HirSpecLocation {
    #[must_use]
    pub const fn function(self) -> HirFunctionId {
        match self {
            Self::FunctionEntry { function }
            | Self::FunctionResult { function }
            | Self::LoopHead { function, .. } => function,
        }
    }
}

/// Owner controlling visibility of a ghost binder.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirSpecBinderOwner {
    Clause(HirSpecClauseId),
    Predicate(HirPredicateId),
}

/// One typed ghost name. It is never a runtime local or ABI component.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirSpecBinder {
    pub id: HirSpecBinderId,
    pub owner: HirSpecBinderOwner,
    pub name: String,
    pub ty: HirTypeId,
    pub span: ByteSpan,
}

/// One-way read from runtime HIR into pure Spec HIR.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirSpecSnapshot {
    Local {
        function: HirFunctionId,
        local: HirLocalId,
    },
    Result {
        function: HirFunctionId,
    },
}

/// Flat pure-term node. Child IDs must name earlier terms owned by the same
/// clause, making cycles impossible and validation bounded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirSpecTerm {
    pub id: HirSpecTermId,
    pub clause: HirSpecClauseId,
    pub ty: HirTypeId,
    pub kind: HirSpecTermKind,
    pub span: ByteSpan,
}

/// Minimal stage-6.4.5 pure logic. Arithmetic, calls, quantifiers, `old` and
/// memory/resource predicates deliberately have no representation here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirSpecTermKind {
    Bool(bool),
    U64(u64),
    Binder(HirSpecBinderId),
    Snapshot(HirSpecSnapshot),
    Equal {
        left: HirSpecTermId,
        right: HirSpecTermId,
    },
    LessThan {
        left: HirSpecTermId,
        right: HirSpecTermId,
    },
    LessOrEqual {
        left: HirSpecTermId,
        right: HirSpecTermId,
    },
    Not(HirSpecTermId),
    And(Vec<HirSpecTermId>),
    Or(Vec<HirSpecTermId>),
}

/// Entity that owns one clause in the shared clause arena.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirSpecClauseOwner {
    Contract {
        contract: HirContractId,
        position: HirSpecContractPosition,
    },
    Prove(HirSpecProveId),
    TrustEntry(HirTrustEntryId),
    LoopInvariant(HirSpecLoopInvariantId),
}

/// One pure boolean clause shared by contracts, proves and invariants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirSpecClause {
    pub id: HirSpecClauseId,
    pub owner: HirSpecClauseOwner,
    pub location: HirSpecLocation,
    pub root: HirSpecTermId,
    pub span: ByteSpan,
}

/// A typed, runtime-independent `Prove` obligation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirSpecProve {
    pub id: HirSpecProveId,
    pub function: HirFunctionId,
    pub location: HirSpecLocation,
    pub clause: HirSpecClauseId,
    pub span: ByteSpan,
}

/// Scope at which an explicitly trusted fact may enter verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirTrustScope {
    FunctionEntry { function: HirFunctionId },
    FunctionResult { function: HirFunctionId },
}

impl HirTrustScope {
    #[must_use]
    pub const fn function(self) -> HirFunctionId {
        match self {
            Self::FunctionEntry { function } | Self::FunctionResult { function } => function,
        }
    }

    #[must_use]
    pub const fn location(self) -> HirSpecLocation {
        match self {
            Self::FunctionEntry { function } => HirSpecLocation::FunctionEntry { function },
            Self::FunctionResult { function } => HirSpecLocation::FunctionResult { function },
        }
    }
}

/// Closed policy classification. Stage 6.4.6 admits only an explicit entry
/// point assumption; reserved variants fail closed until their boundary exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirTrustPolicyKind {
    EntryPointAssumption,
    ForeignContract,
    ExternallyVerified,
}

/// One auditable assumption. There is deliberately no runtime/HIR `Assume`
/// statement: a trusted fact must own a typed clause in this table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirTrustEntry {
    pub id: HirTrustEntryId,
    pub scope: HirTrustScope,
    pub policy: HirTrustPolicyKind,
    pub clause: HirSpecClauseId,
    pub span: ByteSpan,
}

/// Typed loop-invariant identity. Non-trivial entries remain gated in 6.4.5.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HirSpecLoopInvariant {
    pub id: HirSpecLoopInvariantId,
    pub function: HirFunctionId,
    pub loop_id: HirLoopId,
    pub location: HirSpecLocation,
    pub clause: HirSpecClauseId,
    pub span: ByteSpan,
}

/// Separate pure specification arenas owned by one HIR program.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HirSpecEnvironment {
    pub binders: Vec<HirSpecBinder>,
    pub terms: Vec<HirSpecTerm>,
    pub clauses: Vec<HirSpecClause>,
    pub proves: Vec<HirSpecProve>,
    pub trust_entries: Vec<HirTrustEntry>,
    pub loop_invariants: Vec<HirSpecLoopInvariant>,
}

impl HirSpecEnvironment {
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            binders: Vec::new(),
            terms: Vec::new(),
            clauses: Vec::new(),
            proves: Vec::new(),
            trust_entries: Vec::new(),
            loop_invariants: Vec::new(),
        }
    }
}
