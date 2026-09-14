use super::{
    RuntimeVirProgram, VirContractId, VirFunction, VirFunctionId, VirLocation, VirOriginId,
    VirRegionId, VirSignature, VirType,
};

/// Dense identifier of one signature binder within a contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirContractBinderId(u32);

/// Dense identifier of one symbolic memory resource within a contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirContractResourceId(u32);

/// Dense identifier of one clause within a contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirSpecClauseId(u32);

/// Dense identifier of one ghost/specification binder.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirSpecBinderId(u32);

/// Dense identifier of one flat pure specification term.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirSpecTermId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirSpecAssertionId(u32);

pub type VirSpecAssertionKind = crate::SpecAssertionKind<
    VirSpecTermId,
    VirSpecAssertionId,
    VirSpecBinderId,
    VirSpecSnapshot,
    super::VirMemoryAccess,
>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirSpecAssertion {
    pub id: VirSpecAssertionId,
    pub clause: VirSpecClauseId,
    pub kind: VirSpecAssertionKind,
    pub origin: VirOriginId,
}

/// Dense identifier of one predicate declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirPredicateId(u32);

/// Dense identifier of one proof prove.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirSpecProveId(u32);

/// Dense identifier of one audited trust entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirTrustEntryId(u32);

/// Dense identifier of one loop invariant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VirSpecLoopInvariantId(u32);

macro_rules! impl_id {
    ($name:ident) => {
        impl $name {
            #[must_use]
            pub const fn new(raw: u32) -> Self {
                Self(raw)
            }

            #[must_use]
            pub const fn get(self) -> u32 {
                self.0
            }
        }
    };
}

impl_id!(VirContractBinderId);
impl_id!(VirContractResourceId);
impl_id!(VirSpecClauseId);
impl_id!(VirSpecBinderId);
impl_id!(VirSpecTermId);
impl_id!(VirSpecAssertionId);
impl_id!(VirPredicateId);
impl_id!(VirSpecProveId);
impl_id!(VirTrustEntryId);
impl_id!(VirSpecLoopInvariantId);

/// Closed scalar type set admitted by the stage-6.4.5 pure logic.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirSpecType {
    Bool,
    U64,
}

/// Stable logical point independent from a source byte span.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirSpecLocation {
    FunctionEntry { function: VirFunctionId },
    FunctionResult { function: VirFunctionId },
    Runtime(VirLocation),
}

impl VirSpecLocation {
    #[must_use]
    pub const fn function(self) -> VirFunctionId {
        match self {
            Self::FunctionEntry { function } | Self::FunctionResult { function } => function,
            Self::Runtime(location) => location.function(),
        }
    }
}

/// Visibility owner of one ghost binder.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirSpecBinderOwner {
    Clause(VirSpecClauseId),
    Predicate(VirPredicateId),
}

/// One pure ghost name. Runtime instructions cannot name this ID type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirSpecBinder {
    pub id: VirSpecBinderId,
    pub owner: VirSpecBinderOwner,
    pub name: String,
    pub ty: VirSpecType,
    pub origin: VirOriginId,
}

/// A one-way snapshot of a runtime signature slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirSpecSnapshot {
    /// A scalar pointee of one typed ABI pointer binding. None selects result.
    Memory {
        function: VirFunctionId,
        parameter: Option<u32>,
        old: bool,
        projection: crate::SpecMemoryProjection<super::VirFieldId>,
    },
    /// Immutable scalar entry value, owned only by a function ensures clause.
    EntryParameter {
        function: VirFunctionId,
        slot: u32,
    },
    Parameter {
        function: VirFunctionId,
        slot: u32,
    },
    Result {
        function: VirFunctionId,
        slot: u32,
    },
    /// Runtime SSA value observed at the clause's exact runtime location.
    Value {
        function: VirFunctionId,
        value: super::VirValueId,
    },
}

/// One globally dense, flat pure term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirSpecTerm {
    pub id: VirSpecTermId,
    pub clause: VirSpecClauseId,
    pub ty: VirSpecType,
    pub kind: VirSpecTermKind,
    pub origin: VirOriginId,
}

/// Minimal pure logic; child IDs must refer to earlier same-clause terms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirSpecTermKind {
    CheckedAdd {
        left: VirSpecTermId,
        right: VirSpecTermId,
    },
    CheckedSub {
        left: VirSpecTermId,
        right: VirSpecTermId,
    },
    CheckedScale {
        operand: VirSpecTermId,
        stride: u64,
    },
    RangeContains {
        outer_start: VirSpecTermId,
        outer_end: VirSpecTermId,
        inner_start: VirSpecTermId,
        inner_end: VirSpecTermId,
    },
    RangeDisjoint {
        left_start: VirSpecTermId,
        left_end: VirSpecTermId,
        right_start: VirSpecTermId,
        right_end: VirSpecTermId,
    },
    Bool(bool),
    U64(u64),
    Binder(VirSpecBinderId),
    Snapshot(VirSpecSnapshot),
    Equal {
        left: VirSpecTermId,
        right: VirSpecTermId,
    },
    LessThan {
        left: VirSpecTermId,
        right: VirSpecTermId,
    },
    LessOrEqual {
        left: VirSpecTermId,
        right: VirSpecTermId,
    },
    Not(VirSpecTermId),
    And(Vec<VirSpecTermId>),
    Or(Vec<VirSpecTermId>),
}

impl VirSpecTermKind {
    pub(crate) fn is_checked_numeric(&self) -> bool {
        matches!(
            self,
            Self::CheckedAdd { .. }
                | Self::CheckedSub { .. }
                | Self::CheckedScale { .. }
                | Self::RangeContains { .. }
                | Self::RangeDisjoint { .. }
        )
    }
}

/// Whether a contract binder or clause describes function entry or return.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirContractPosition {
    Requires,
    Ensures,
}

/// One typed name for a flattened runtime signature slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirContractBinder {
    pub id: VirContractBinderId,
    pub position: VirContractPosition,
    pub slot: u32,
    pub ty: VirType,
}

/// One symbolic resource name shared by the clauses of a contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirContractResource {
    pub id: VirContractResourceId,
}

/// Auditable source of one checked specification clause.
///
/// Entity-specific module, ghost and trait origins are deliberately absent:
/// those facts cannot enter a unit until their typed declaration tables exist.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirSpecClauseOrigin {
    InferredType { origin: VirOriginId },
    Explicit { origin: VirOriginId },
}

impl VirSpecClauseOrigin {
    #[must_use]
    pub const fn origin(self) -> VirOriginId {
        match self {
            Self::InferredType { origin } | Self::Explicit { origin } => origin,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirContractInitialization {
    Initialized,
    Uninitialized,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirContractLiveness {
    Live,
    Dead,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirContractOwnership {
    Owned,
    Unowned,
    /// Function-frame storage borrowed across one internal call boundary.
    Local,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirContractAccess {
    Read,
    Write,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VirContractFree {
    No,
    Yes,
}

/// Pointer guarantee attached to one signature binder.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirContractPointer {
    pub binder: VirContractBinderId,
    pub offset_lower: u64,
    pub offset_upper: u64,
    pub alignment: u64,
}

/// Permission guarantee attached to one signature binder.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirContractPermission {
    pub binder: VirContractBinderId,
    pub start_byte: u64,
    pub end_byte: u64,
    pub access: VirContractAccess,
    pub free: VirContractFree,
}

/// A verifier-independent memory-resource summary.
///
/// A single summary owns the allocation fact and every pointer/permission
/// view contributed by one clause. It contains no analysis allocation ID,
/// path state, join result or widening state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirContractResourceSummary {
    pub resource: VirContractResourceId,
    pub region: VirRegionId,
    pub size_bytes: u64,
    pub alignment: u64,
    pub liveness: VirContractLiveness,
    pub ownership: VirContractOwnership,
    pub initialization: VirContractInitialization,
    pub pointers: Vec<VirContractPointer>,
    pub permissions: Vec<VirContractPermission>,
}

/// Shared closed clause set established across stages 6.4.4 and 6.4.5.
///
/// Scalar ranges remain as a compatibility summary for the stage-5 verifier;
/// general pure logic points into the separate typed term arena.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirSpecClauseKind {
    /// Structurally checked, but proof rules remain gated in 8.1.2.
    Assertion {
        root: VirSpecAssertionId,
    },
    Resource(VirContractResourceSummary),
    U64Range {
        binder: VirContractBinderId,
        lower: u64,
        upper: u64,
    },
    BoolValue {
        binder: VirContractBinderId,
        value: bool,
    },
    Logic {
        root: VirSpecTermId,
    },
}

/// Entity that owns one entry in the shared clause arena.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirSpecClauseOwner {
    Contract {
        contract: VirContractId,
        position: VirContractPosition,
    },
    Prove(VirSpecProveId),
    TrustEntry(VirTrustEntryId),
    LoopInvariant(VirSpecLoopInvariantId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirSpecClause {
    pub id: VirSpecClauseId,
    pub owner: VirSpecClauseOwner,
    pub location: VirSpecLocation,
    pub origin: VirSpecClauseOrigin,
    pub kind: VirSpecClauseKind,
}

/// Predicate declaration without a body. Bodies/fold/unfold remain gated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirPredicate {
    pub id: VirPredicateId,
    pub name: String,
    pub binders: Vec<VirSpecBinderId>,
    pub origin: VirOriginId,
    pub body: Option<VirSpecClauseId>,
}

/// A typed, runtime-erased `Prove` obligation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirSpecProve {
    pub id: VirSpecProveId,
    pub function: VirFunctionId,
    pub location: VirSpecLocation,
    pub clause: VirSpecClauseId,
    pub origin: VirOriginId,
}

/// Logical scope of a registered assumption.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirTrustScope {
    FunctionEntry { function: VirFunctionId },
    FunctionResult { function: VirFunctionId },
    Runtime(VirLocation),
}

impl VirTrustScope {
    #[must_use]
    pub const fn function(self) -> VirFunctionId {
        match self {
            Self::FunctionEntry { function } | Self::FunctionResult { function } => function,
            Self::Runtime(location) => location.function(),
        }
    }

    #[must_use]
    pub const fn location(self) -> VirSpecLocation {
        match self {
            Self::FunctionEntry { function } => VirSpecLocation::FunctionEntry { function },
            Self::FunctionResult { function } => VirSpecLocation::FunctionResult { function },
            Self::Runtime(location) => VirSpecLocation::Runtime(location),
        }
    }
}

/// Closed trust-policy classification. Only `EntryPointAssumption` is admitted
/// in stage 6.4.6; the other variants are reserved and validation denies them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VirTrustPolicyKind {
    EntryPointAssumption,
    ForeignContract,
    ExternallyVerified,
}

/// One typed, sourced fact deliberately imported into verification.
///
/// This is the only VIR representation of an assumption. Runtime VIR has no
/// `Assume` opcode and cannot name this ID type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirTrustEntry {
    pub id: VirTrustEntryId,
    pub scope: VirTrustScope,
    pub policy: VirTrustPolicyKind,
    pub clause: VirSpecClauseId,
    pub origin: VirOriginId,
}

/// Typed loop-invariant identity; non-trivial entries are gated in 6.4.5.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirSpecLoopInvariant {
    pub id: VirSpecLoopInvariantId,
    pub function: VirFunctionId,
    pub location: VirSpecLocation,
    pub clause: VirSpecClauseId,
    pub origin: VirOriginId,
}

/// One function-owned contract in the canonical VIR specification table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirContract {
    pub id: VirContractId,
    pub function: VirFunctionId,
    pub signature: VirSignature,
    pub binders: Vec<VirContractBinder>,
    pub resources: Vec<VirContractResource>,
    pub clauses: Vec<VirSpecClauseId>,
}

impl VirContract {
    /// Creates a deterministic empty contract with one binder per signature
    /// slot. The returned raw contract may be extended before unit validation.
    #[must_use]
    pub fn implicit(function: &VirFunction) -> Self {
        let mut binders = Vec::with_capacity(
            function.signature.parameters.len() + function.signature.results.len(),
        );
        for (slot, ty) in function.signature.parameters.iter().copied().enumerate() {
            binders.push(VirContractBinder {
                id: VirContractBinderId::new(binders.len() as u32),
                position: VirContractPosition::Requires,
                slot: slot as u32,
                ty,
            });
        }
        for (slot, ty) in function.signature.results.iter().copied().enumerate() {
            binders.push(VirContractBinder {
                id: VirContractBinderId::new(binders.len() as u32),
                position: VirContractPosition::Ensures,
                slot: slot as u32,
                ty,
            });
        }
        Self {
            id: function.contract,
            function: function.id,
            signature: function.signature.clone(),
            binders,
            resources: Vec::new(),
            clauses: Vec::new(),
        }
    }

    #[must_use]
    pub fn binder(
        &self,
        position: VirContractPosition,
        slot: usize,
    ) -> Option<VirContractBinderId> {
        self.binders
            .iter()
            .find(|binder| binder.position == position && binder.slot as usize == slot)
            .map(|binder| binder.id)
    }

    /// Adds a dense resource name for a following clause.
    #[must_use]
    pub fn add_resource(&mut self) -> VirContractResourceId {
        let id = VirContractResourceId::new(self.resources.len() as u32);
        self.resources.push(VirContractResource { id });
        id
    }
}

/// Canonical specification tables owned by one VIR unit. Resource assertions
/// observe runtime identities but never extend its allocation/loan state.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VirSpecEnvironment {
    assertions: Vec<VirSpecAssertion>,
    contracts: Vec<VirContract>,
    predicates: Vec<VirPredicate>,
    binders: Vec<VirSpecBinder>,
    terms: Vec<VirSpecTerm>,
    clauses: Vec<VirSpecClause>,
    proves: Vec<VirSpecProve>,
    trust_entries: Vec<VirTrustEntry>,
    loop_invariants: Vec<VirSpecLoopInvariant>,
}

/// Unvalidated deterministic tables consumed atomically by
/// [`VirSpecEnvironment::from_tables`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VirSpecTables {
    pub assertions: Vec<VirSpecAssertion>,
    pub contracts: Vec<VirContract>,
    pub predicates: Vec<VirPredicate>,
    pub binders: Vec<VirSpecBinder>,
    pub terms: Vec<VirSpecTerm>,
    pub clauses: Vec<VirSpecClause>,
    pub proves: Vec<VirSpecProve>,
    pub trust_entries: Vec<VirTrustEntry>,
    pub loop_invariants: Vec<VirSpecLoopInvariant>,
}

impl VirSpecEnvironment {
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            assertions: Vec::new(),
            contracts: Vec::new(),
            predicates: Vec::new(),
            binders: Vec::new(),
            terms: Vec::new(),
            clauses: Vec::new(),
            proves: Vec::new(),
            trust_entries: Vec::new(),
            loop_invariants: Vec::new(),
        }
    }

    /// Creates raw tables. Unit validation checks density and every cross-table
    /// reference before a verifier can observe them.
    #[must_use]
    pub fn from_contracts(contracts: Vec<VirContract>) -> Self {
        Self {
            contracts,
            ..Self::empty()
        }
    }

    /// Constructs raw specification tables. Unit validation checks all IDs,
    /// ownership, typing, locations and cross-table references.
    #[must_use]
    pub fn from_tables(tables: VirSpecTables) -> Self {
        Self {
            assertions: tables.assertions,
            contracts: tables.contracts,
            predicates: tables.predicates,
            binders: tables.binders,
            terms: tables.terms,
            clauses: tables.clauses,
            proves: tables.proves,
            trust_entries: tables.trust_entries,
            loop_invariants: tables.loop_invariants,
        }
    }

    #[must_use]
    pub(crate) fn implicit(runtime: &RuntimeVirProgram) -> Self {
        Self {
            contracts: runtime
                .functions
                .iter()
                .map(VirContract::implicit)
                .collect(),
            ..Self::empty()
        }
    }

    #[must_use]
    pub fn contracts(&self) -> &[VirContract] {
        &self.contracts
    }

    #[must_use]
    pub fn contract(&self, id: VirContractId) -> Option<&VirContract> {
        self.contracts
            .get(id.get() as usize)
            .filter(|contract| contract.id == id)
    }

    #[must_use]
    pub fn contract_mut(&mut self, id: VirContractId) -> Option<&mut VirContract> {
        self.contracts
            .get_mut(id.get() as usize)
            .filter(|contract| contract.id == id)
    }

    #[must_use]
    pub fn predicates(&self) -> &[VirPredicate] {
        &self.predicates
    }

    #[must_use]
    pub fn binders(&self) -> &[VirSpecBinder] {
        &self.binders
    }

    #[must_use]
    pub fn terms(&self) -> &[VirSpecTerm] {
        &self.terms
    }

    #[must_use]
    pub fn assertions(&self) -> &[VirSpecAssertion] {
        &self.assertions
    }

    pub fn assertions_mut(&mut self) -> &mut Vec<VirSpecAssertion> {
        &mut self.assertions
    }

    #[must_use]
    pub fn clauses(&self) -> &[VirSpecClause] {
        &self.clauses
    }

    #[must_use]
    pub fn clause(&self, id: VirSpecClauseId) -> Option<&VirSpecClause> {
        self.clauses
            .get(id.get() as usize)
            .filter(|clause| clause.id == id)
    }

    #[must_use]
    pub fn proves(&self) -> &[VirSpecProve] {
        &self.proves
    }

    #[must_use]
    pub fn trust_entries(&self) -> &[VirTrustEntry] {
        &self.trust_entries
    }

    #[must_use]
    pub fn loop_invariants(&self) -> &[VirSpecLoopInvariant] {
        &self.loop_invariants
    }

    #[must_use]
    pub fn predicates_mut(&mut self) -> &mut Vec<VirPredicate> {
        &mut self.predicates
    }

    #[must_use]
    pub fn binders_mut(&mut self) -> &mut Vec<VirSpecBinder> {
        &mut self.binders
    }

    #[must_use]
    pub fn terms_mut(&mut self) -> &mut Vec<VirSpecTerm> {
        &mut self.terms
    }

    #[must_use]
    pub fn clauses_mut(&mut self) -> &mut Vec<VirSpecClause> {
        &mut self.clauses
    }

    #[must_use]
    pub fn proves_mut(&mut self) -> &mut Vec<VirSpecProve> {
        &mut self.proves
    }

    #[must_use]
    pub fn trust_entries_mut(&mut self) -> &mut Vec<VirTrustEntry> {
        &mut self.trust_entries
    }

    #[must_use]
    pub fn loop_invariants_mut(&mut self) -> &mut Vec<VirSpecLoopInvariant> {
        &mut self.loop_invariants
    }

    /// Adds one globally dense contract clause and records it in its owner.
    pub fn add_contract_clause(
        &mut self,
        contract: VirContractId,
        position: VirContractPosition,
        origin: VirSpecClauseOrigin,
        kind: VirSpecClauseKind,
    ) -> Option<VirSpecClauseId> {
        let function = self.contract(contract)?.function;
        let id = VirSpecClauseId::new(u32::try_from(self.clauses.len()).ok()?);
        let location = match position {
            VirContractPosition::Requires => VirSpecLocation::FunctionEntry { function },
            VirContractPosition::Ensures => VirSpecLocation::FunctionResult { function },
        };
        self.clauses.push(VirSpecClause {
            id,
            owner: VirSpecClauseOwner::Contract { contract, position },
            location,
            origin,
            kind,
        });
        self.contract_mut(contract)?.clauses.push(id);
        Some(id)
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.contracts.is_empty()
            && self.predicates.is_empty()
            && self.binders.is_empty()
            && self.terms.is_empty()
            && self.clauses.is_empty()
            && self.proves.is_empty()
            && self.trust_entries.is_empty()
            && self.loop_invariants.is_empty()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.contracts.len()
    }
}
