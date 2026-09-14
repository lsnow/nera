use std::collections::{BTreeMap, btree_map::Entry};
use std::error::Error;
use std::fmt;

use crate::{
    ByteSpan, ResolvedVirUnit, VirContractAccess, VirContractFree, VirContractId,
    VirContractInitialization, VirContractLiveness, VirContractOwnership, VirContractPosition,
    VirMemoryAccess, VirOriginId, VirRegionId, VirSignature, VirSpecClause, VirSpecClauseId,
    VirSpecClauseKind, VirSpecClauseOrigin, VirType, VirValueId,
};

use super::resource::{
    AbstractAllocation, AbstractAllocationId, AbstractBool, AbstractByteRange, AbstractPermission,
    AbstractPointer, AbstractProvenance, AbstractValue, AccessPermission, ByteRange,
    FreeCapability, GuaranteedAlignment, InitializationClass, LivenessState, OwnershipState,
    ResourceState, ResourceStateDefinitionError, U64Interval,
};
use super::transfer::ObligationStatus;

mod abi;
#[cfg(test)]
mod domain_tests;
pub(super) mod frame;
pub(super) mod pure;
mod resources;

/// Symbolic allocation name scoped to one function contract.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContractResourceId(u32);

impl ContractResourceId {
    #[must_use]
    pub const fn new(raw: u32) -> Self {
        Self(raw)
    }

    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }
}

/// Auditable origin of one imported, validated VIR contract clause.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ContractFactOrigin {
    clause: VirSpecClauseId,
    position: VirContractPosition,
    source: VirSpecClauseOrigin,
    source_span: ByteSpan,
}

impl ContractFactOrigin {
    #[must_use]
    pub const fn clause(self) -> VirSpecClauseId {
        self.clause
    }

    #[must_use]
    pub const fn position(self) -> VirContractPosition {
        self.position
    }

    #[must_use]
    pub const fn source(self) -> VirSpecClauseOrigin {
        self.source
    }

    #[must_use]
    pub const fn source_span(self) -> ByteSpan {
        self.source_span
    }
}

/// Initialization guarantee admitted by contract v0. Explicit byte contracts
/// cover the allocation; inferred indirect ABI contracts cover independently
/// derived canonical value bytes and never treat padding as part of the value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ContractInitialization {
    Initialized,
    Uninitialized,
    Unknown,
}

/// One symbolic allocation fact in a pre- or post-state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ContractAllocationFact {
    pub clause: VirSpecClauseId,
    pub origin: ContractFactOrigin,
    pub resource: ContractResourceId,
    pub region: Option<VirRegionId>,
    pub size_bytes: u64,
    pub alignment: u64,
    pub liveness: LivenessState,
    pub ownership: OwnershipState,
    pub initialization: ContractInitialization,
}

/// One abstract fact attached to a contract parameter or result slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ContractValueFactKind {
    U64(U64Interval),
    Bool(AbstractBool),
    Pointer {
        resource: ContractResourceId,
        offset_bytes: U64Interval,
        alignment: u64,
        access: VirMemoryAccess,
    },
    Permission {
        resource: ContractResourceId,
        range: AbstractByteRange,
        access: AccessPermission,
        free: FreeCapability,
    },
}

impl ContractValueFactKind {
    #[must_use]
    pub const fn ty(self) -> VirType {
        match self {
            Self::U64(_) => VirType::U64,
            Self::Bool(_) => VirType::Bool,
            Self::Pointer { access, .. } => VirType::Pointer { access },
            Self::Permission { .. } => VirType::Permission,
        }
    }
}

/// A sourced contract value fact.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ContractValueFact {
    pub clause: VirSpecClauseId,
    pub origin: ContractFactOrigin,
    pub kind: ContractValueFactKind,
}

/// A complete abstract pre- or post-state over signature slots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContractState {
    values: Vec<Option<ContractValueFact>>,
    allocations: BTreeMap<ContractResourceId, ContractAllocationFact>,
    /// Canonical value bytes for inferred indirect ABI storage. Explicit raw
    /// contracts retain their original whole-allocation byte semantics.
    value_ranges: BTreeMap<ContractResourceId, Vec<ByteRange>>,
}

impl ContractState {
    #[must_use]
    pub fn new(value_count: usize) -> Self {
        Self {
            values: vec![None; value_count],
            allocations: BTreeMap::new(),
            value_ranges: BTreeMap::new(),
        }
    }

    pub fn set_value(
        &mut self,
        slot: usize,
        fact: ContractValueFact,
    ) -> Result<(), ContractDefinitionError> {
        let Some(current) = self.values.get_mut(slot) else {
            return Err(ContractDefinitionError::ValueSlotOutOfRange {
                slot,
                count: self.values.len(),
            });
        };
        if current.replace(fact).is_some() {
            return Err(ContractDefinitionError::DuplicateValueSlot(slot));
        }
        Ok(())
    }

    pub fn add_allocation(
        &mut self,
        fact: ContractAllocationFact,
    ) -> Result<(), ContractDefinitionError> {
        match self.allocations.entry(fact.resource) {
            Entry::Vacant(entry) => {
                validate_allocation_fact(fact)?;
                entry.insert(fact);
                Ok(())
            }
            Entry::Occupied(_) => Err(ContractDefinitionError::DuplicateResource(fact.resource)),
        }
    }
}

/// Checked, signature-bound function contract.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct InstantiatedContract {
    pub(super) pure: Option<pure::PureContract>,
    pub(super) resources: Option<resources::ResourceContract>,
    has_frame: bool,
    id: VirContractId,
    signature: VirSignature,
    requires: ContractState,
    ensures: ContractState,
    pub(super) borrow_parameters: std::collections::BTreeSet<usize>,
}

impl InstantiatedContract {
    pub(super) fn has_explicit_contract(&self) -> bool {
        self.pure.is_some() || self.resources.is_some() || self.has_frame
    }
    pub(super) fn observes_memory(&self) -> bool {
        self.resources.is_some() || self.pure.as_ref().is_some_and(|p| p.observes_memory())
    }
    pub(super) fn mapped_postcondition_instances(
        &self,
        mapping: &ResourceInstantiation,
    ) -> std::collections::BTreeSet<AbstractAllocationId> {
        self.ensures
            .allocations
            .keys()
            .filter_map(|resource| mapping.get(resource).copied())
            .collect()
    }
    pub fn new(
        id: VirContractId,
        signature: VirSignature,
        requires: ContractState,
        ensures: ContractState,
    ) -> Result<Self, ContractDefinitionError> {
        validate_state(&requires, &signature.parameters, ContractPosition::Requires)?;
        validate_state(&ensures, &signature.results, ContractPosition::Ensures)?;
        Ok(Self {
            pure: None,
            resources: None,
            has_frame: false,
            id,
            signature,
            requires,
            ensures,
            borrow_parameters: std::collections::BTreeSet::new(),
        })
    }

    #[must_use]
    pub const fn id(&self) -> VirContractId {
        self.id
    }

    #[must_use]
    pub const fn signature(&self) -> &VirSignature {
        &self.signature
    }
}

/// Deterministic registry used by function entry, calls and return checking.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct InstantiatedContracts {
    contracts: BTreeMap<VirContractId, InstantiatedContract>,
}

impl InstantiatedContracts {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            contracts: BTreeMap::new(),
        }
    }

    pub fn insert(
        &mut self,
        contract: InstantiatedContract,
    ) -> Result<(), ContractDefinitionError> {
        match self.contracts.entry(contract.id()) {
            Entry::Vacant(entry) => {
                entry.insert(contract);
                Ok(())
            }
            Entry::Occupied(_) => Err(ContractDefinitionError::DuplicateContract(contract.id())),
        }
    }

    #[must_use]
    pub fn get(&self, id: VirContractId) -> Option<&InstantiatedContract> {
        self.contracts.get(&id)
    }
}

/// Instantiates the verifier's analysis-only entry/exit states from the
/// checked VIR contract table. No analysis object is stored back into VIR.
pub(super) fn instantiate_contracts(
    program: &ResolvedVirUnit<'_>,
) -> Result<InstantiatedContracts, ContractDefinitionError> {
    let mut environment = InstantiatedContracts::new();
    for contract in program.as_unit().specs.contracts() {
        let mut requires = ContractState::new(contract.signature.parameters.len());
        let mut ensures = ContractState::new(contract.signature.results.len());
        for clause_id in &contract.clauses {
            let clause = program
                .as_unit()
                .specs
                .clause(*clause_id)
                .ok_or(ContractDefinitionError::MissingClause(*clause_id))?;
            let position = contract_clause_position(contract.id, clause)?;
            let source_span = program
                .as_unit()
                .source_map
                .source_span_for_origin(clause.origin.origin())
                .ok_or(ContractDefinitionError::MissingOrigin(
                    clause.origin.origin(),
                ))?
                .span;
            let origin = ContractFactOrigin {
                clause: clause.id,
                position,
                source: clause.origin,
                source_span,
            };
            let state = match position {
                VirContractPosition::Requires => &mut requires,
                VirContractPosition::Ensures => &mut ensures,
            };
            if !matches!(
                clause.kind,
                VirSpecClauseKind::Logic { .. } | VirSpecClauseKind::Assertion { .. }
            ) {
                instantiate_clause(contract, clause, origin, state)?;
            }
        }
        abi::install_value_ranges(program, contract, &mut requires, &mut ensures)?;
        let mut instantiated =
            InstantiatedContract::new(contract.id, contract.signature.clone(), requires, ensures)?;
        instantiated.pure = pure::PureContract::new(program, contract)?;
        instantiated.resources = resources::ResourceContract::new(program, contract)?;
        instantiated.has_frame = contract.clauses.iter().any(|id| {
            matches!(program.as_unit().specs.clause(*id).unwrap().kind,
                VirSpecClauseKind::Assertion { root } if matches!(
                    program.as_unit().specs.assertions()[root.get() as usize].kind,
                    crate::SpecAssertionKind::Footprint { .. }))
        });
        instantiated.borrow_parameters = program
            .runtime()
            .borrows
            .regions()
            .iter()
            .filter(|region| region.owner == contract.function)
            .filter_map(|region| match region.origin {
                crate::VirBorrowRegionOrigin::Parameter { index } => Some(index as usize),
                _ => None,
            })
            .collect();
        environment.insert(instantiated)?;
    }
    Ok(environment)
}

fn instantiate_clause(
    contract: &crate::VirContract,
    clause: &VirSpecClause,
    origin: ContractFactOrigin,
    state: &mut ContractState,
) -> Result<(), ContractDefinitionError> {
    match &clause.kind {
        VirSpecClauseKind::Resource(summary) => {
            let resource = ContractResourceId::new(summary.resource.get());
            state.add_allocation(ContractAllocationFact {
                clause: clause.id,
                origin,
                resource,
                region: (!matches!(summary.ownership, VirContractOwnership::Local))
                    .then_some(summary.region),
                size_bytes: summary.size_bytes,
                alignment: summary.alignment,
                liveness: match summary.liveness {
                    VirContractLiveness::Live => LivenessState::Live,
                    VirContractLiveness::Dead => LivenessState::Dead,
                },
                ownership: match summary.ownership {
                    VirContractOwnership::Owned => OwnershipState::Owned,
                    VirContractOwnership::Unowned => OwnershipState::Unowned,
                    VirContractOwnership::Local => OwnershipState::Unowned,
                },
                initialization: match summary.initialization {
                    VirContractInitialization::Initialized => ContractInitialization::Initialized,
                    VirContractInitialization::Uninitialized => {
                        ContractInitialization::Uninitialized
                    }
                    VirContractInitialization::Unknown => ContractInitialization::Unknown,
                },
            })?;
            for pointer in &summary.pointers {
                let slot = binder_slot(contract, clause, pointer.binder)?;
                let access = contract
                    .binders
                    .get(pointer.binder.get() as usize)
                    .and_then(|binder| match binder.ty {
                        VirType::Pointer { access } => Some(access),
                        _ => None,
                    })
                    .ok_or(ContractDefinitionError::MissingBinder(pointer.binder))?;
                state.set_value(
                    slot,
                    ContractValueFact {
                        clause: clause.id,
                        origin,
                        kind: ContractValueFactKind::Pointer {
                            resource,
                            offset_bytes: U64Interval::new(
                                pointer.offset_lower,
                                pointer.offset_upper,
                            )
                            .map_err(|_| ContractDefinitionError::InvalidRange)?,
                            alignment: pointer.alignment,
                            access,
                        },
                    },
                )?;
            }
            for permission in &summary.permissions {
                let slot = binder_slot(contract, clause, permission.binder)?;
                state.set_value(
                    slot,
                    ContractValueFact {
                        clause: clause.id,
                        origin,
                        kind: ContractValueFactKind::Permission {
                            resource,
                            range: AbstractByteRange::Exact(
                                ByteRange::new(permission.start_byte, permission.end_byte)
                                    .map_err(|_| ContractDefinitionError::InvalidRange)?,
                            ),
                            access: match permission.access {
                                VirContractAccess::Read => AccessPermission::Read,
                                VirContractAccess::Write => AccessPermission::Write,
                            },
                            free: match permission.free {
                                VirContractFree::No => FreeCapability::No,
                                VirContractFree::Yes => FreeCapability::Yes,
                            },
                        },
                    },
                )?;
            }
        }
        VirSpecClauseKind::U64Range {
            binder,
            lower,
            upper,
        } => {
            let slot = binder_slot(contract, clause, *binder)?;
            state.set_value(
                slot,
                ContractValueFact {
                    clause: clause.id,
                    origin,
                    kind: ContractValueFactKind::U64(
                        U64Interval::new(*lower, *upper)
                            .map_err(|_| ContractDefinitionError::InvalidRange)?,
                    ),
                },
            )?;
        }
        VirSpecClauseKind::BoolValue { binder, value } => {
            let slot = binder_slot(contract, clause, *binder)?;
            state.set_value(
                slot,
                ContractValueFact {
                    clause: clause.id,
                    origin,
                    kind: ContractValueFactKind::Bool(if *value {
                        AbstractBool::True
                    } else {
                        AbstractBool::False
                    }),
                },
            )?;
        }
        VirSpecClauseKind::Logic { .. } | VirSpecClauseKind::Assertion { .. } => {
            return Err(ContractDefinitionError::UnsupportedLogicalClause(clause.id));
        }
    }
    Ok(())
}

fn binder_slot(
    contract: &crate::VirContract,
    clause: &VirSpecClause,
    binder: crate::VirContractBinderId,
) -> Result<usize, ContractDefinitionError> {
    let position = contract_clause_position(contract.id, clause)?;
    contract
        .binders
        .get(binder.get() as usize)
        .filter(|candidate| candidate.id == binder && candidate.position == position)
        .map(|binder| binder.slot as usize)
        .ok_or(ContractDefinitionError::MissingBinder(binder))
}

fn contract_clause_position(
    contract: VirContractId,
    clause: &VirSpecClause,
) -> Result<VirContractPosition, ContractDefinitionError> {
    match clause.owner {
        crate::VirSpecClauseOwner::Contract {
            contract: owner,
            position,
        } if owner == contract => Ok(position),
        _ => Err(ContractDefinitionError::ForeignClause {
            contract,
            clause: clause.id,
        }),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContractPosition {
    Requires,
    Ensures,
}

fn validate_state(
    state: &ContractState,
    types: &[VirType],
    position: ContractPosition,
) -> Result<(), ContractDefinitionError> {
    if state.values.len() != types.len() {
        return Err(ContractDefinitionError::StateArity {
            position,
            found: state.values.len(),
            expected: types.len(),
        });
    }
    for (slot, (fact, expected)) in state.values.iter().zip(types).enumerate() {
        let Some(fact) = fact else { continue };
        let found = fact.kind.ty();
        if found != *expected {
            return Err(ContractDefinitionError::ValueTypeMismatch {
                position,
                slot,
                expected: *expected,
                found,
            });
        }
        if let Some(resource) = value_resource(fact.kind)
            && !state.allocations.contains_key(&resource)
        {
            return Err(ContractDefinitionError::MissingResource(resource));
        }
        validate_value_fact(fact.kind)?;
        validate_fact_origin(fact.clause, fact.origin)?;
    }
    for fact in state.allocations.values().copied() {
        validate_fact_origin(fact.clause, fact.origin)?;
    }
    Ok(())
}

fn validate_fact_origin(
    clause: VirSpecClauseId,
    origin: ContractFactOrigin,
) -> Result<(), ContractDefinitionError> {
    if origin.clause != clause {
        Err(ContractDefinitionError::FactClauseMismatch {
            fact: clause,
            origin: origin.clause,
        })
    } else {
        Ok(())
    }
}

fn validate_allocation_fact(fact: ContractAllocationFact) -> Result<(), ContractDefinitionError> {
    if let Some(region) = fact.region {
        AbstractAllocation::new(region, fact.size_bytes, fact.alignment)
    } else {
        AbstractAllocation::new_local(fact.size_bytes, fact.alignment)
    }
    .map_err(ContractDefinitionError::InvalidAllocation)?;
    if matches!(fact.liveness, LivenessState::Dead)
        && !matches!(fact.ownership, OwnershipState::Unowned)
    {
        return Err(ContractDefinitionError::DeadAllocationOwned(fact.resource));
    }
    Ok(())
}

fn validate_value_fact(fact: ContractValueFactKind) -> Result<(), ContractDefinitionError> {
    match fact {
        ContractValueFactKind::Pointer { alignment, .. } => {
            GuaranteedAlignment::new(alignment)
                .map_err(|_| ContractDefinitionError::InvalidAlignment(alignment))?;
        }
        ContractValueFactKind::Permission {
            range: AbstractByteRange::Symbolic { .. },
            ..
        } => return Err(ContractDefinitionError::SymbolicPermissionRange),
        ContractValueFactKind::U64(_)
        | ContractValueFactKind::Bool(_)
        | ContractValueFactKind::Permission { .. } => {}
    }
    Ok(())
}

const fn value_resource(fact: ContractValueFactKind) -> Option<ContractResourceId> {
    match fact {
        ContractValueFactKind::Pointer { resource, .. }
        | ContractValueFactKind::Permission { resource, .. } => Some(resource),
        ContractValueFactKind::U64(_) | ContractValueFactKind::Bool(_) => None,
    }
}

/// One pre/postcondition clause check retained for derivation and diagnostics.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ContractCheck {
    pub clause: VirSpecClauseId,
    pub origin: ContractFactOrigin,
    pub status: ObligationStatus,
}

pub(super) type ResourceInstantiation = BTreeMap<ContractResourceId, AbstractAllocationId>;

pub(super) fn entry_state(
    contract: &InstantiatedContract,
    entry_parameters: &[(VirValueId, VirType)],
) -> Result<ResourceState, ContractApplicationError> {
    if entry_parameters.len() != contract.signature.parameters.len() {
        return Err(ContractApplicationError::SignatureMismatch(contract.id));
    }
    let mapping = contract
        .requires
        .allocations
        .keys()
        .copied()
        .map(|resource| (resource, AbstractAllocationId::new(resource.get())))
        .collect::<BTreeMap<_, _>>();
    let mut state = ResourceState::new();
    install_allocations(&mut state, &contract.requires, &mapping, false)?;
    for ((id, ty), fact) in entry_parameters
        .iter()
        .copied()
        .zip(&contract.requires.values)
    {
        let value = match fact {
            Some(fact) => instantiate_value(fact.kind, &mapping)?,
            None => unknown_value(ty),
        };
        state.define_value(id, value)?;
    }
    if let Some(pure) = &contract.pure {
        pure.install_entry(&mut state, entry_parameters)?;
    }
    Ok(state)
}

pub(super) fn check_preconditions(
    state: &ResourceState,
    arguments: &[VirValueId],
    contract: &InstantiatedContract,
    config: crate::CfgAnalysisConfig,
) -> (ResourceInstantiation, Vec<ContractCheck>) {
    let actual = arguments
        .iter()
        .map(|id| state.value(*id).copied())
        .collect::<Vec<_>>();
    let (mapping, mut checks) =
        check_contract_state(state, &actual, &contract.requires, BTreeMap::new());
    if let Some(pure) = &contract.pure {
        checks.extend(pure.check(
            state,
            state,
            arguments,
            &[],
            VirContractPosition::Requires,
            config.relation_limits,
        ));
    }
    if let Some(resources) = &contract.resources {
        checks.extend(resources.check(
            state,
            state,
            arguments,
            &[],
            VirContractPosition::Requires,
            config,
        ));
    }
    (mapping, checks)
}

pub(super) fn apply_postconditions(
    state: &ResourceState,
    contract: &InstantiatedContract,
    mut mapping: ResourceInstantiation,
    call_site: u64,
) -> Result<(ResourceState, Vec<AbstractValue>), ContractApplicationError> {
    let mut output = state.clone();
    for resource in contract.ensures.allocations.keys().copied() {
        if let Entry::Vacant(entry) = mapping.entry(resource) {
            let id = AbstractAllocationId::contract_instance(call_site, resource.get());
            let allocation = instantiate_allocation(
                contract.ensures.allocations[&resource],
                contract
                    .ensures
                    .value_ranges
                    .get(&resource)
                    .map(Vec::as_slice),
            )?;
            output.introduce_allocation_instance(id, allocation)?;
            entry.insert(id);
        }
    }
    install_allocations(&mut output, &contract.ensures, &mapping, true)?;
    let values = contract
        .ensures
        .values
        .iter()
        .zip(&contract.signature.results)
        .map(|(fact, ty)| {
            fact.map_or_else(
                || Ok(unknown_value(*ty)),
                |fact| instantiate_value(fact.kind, &mapping),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((output, values))
}

pub(super) fn check_postconditions(
    state: &ResourceState,
    values: &[AbstractValue],
    contract: &InstantiatedContract,
) -> Vec<ContractCheck> {
    let seed = contract
        .requires
        .allocations
        .keys()
        .copied()
        .map(|resource| (resource, AbstractAllocationId::new(resource.get())))
        .collect();
    check_contract_state(
        state,
        &values.iter().copied().map(Some).collect::<Vec<_>>(),
        &contract.ensures,
        seed,
    )
    .1
}

fn check_contract_state(
    state: &ResourceState,
    actual_values: &[Option<AbstractValue>],
    expected: &ContractState,
    mut mapping: ResourceInstantiation,
) -> (ResourceInstantiation, Vec<ContractCheck>) {
    let mut checks = Vec::new();
    for (actual, expected_value) in actual_values.iter().zip(&expected.values) {
        let Some(expected_value) = expected_value else {
            continue;
        };
        let status = match actual {
            Some(actual) => {
                let matched = match_value(*actual, expected_value.kind, &mut mapping);
                // The legacy contract carrier reconstructs allocation-wide
                // pointers. Until domain summaries exist, it must establish
                // that premise on both call inputs and function outputs.
                let domain = match (actual, expected_value.kind) {
                    (
                        AbstractValue::Pointer(pointer),
                        ContractValueFactKind::Pointer { resource, .. },
                    ) => match pointer.domain() {
                        crate::VirPointerDomain::Allocation => ObligationStatus::Proven,
                        crate::VirPointerDomain::Unknown => ObligationStatus::Unknown,
                        crate::VirPointerDomain::Restricted(range) => expected
                            .allocations
                            .get(&resource)
                            .map_or(ObligationStatus::Unknown, |allocation| {
                                super::relation::range::interval_coverage(
                                    range,
                                    AbstractPointer::new(
                                        pointer.provenance(),
                                        U64Interval::exact(0),
                                        GuaranteedAlignment::one(),
                                    ),
                                    allocation.size_bytes,
                                )
                            }),
                    },
                    _ => ObligationStatus::Proven,
                };
                let nominal = match actual {
                    AbstractValue::Pointer(pointer) => {
                        pointer
                            .memory_access()
                            .map_or(ObligationStatus::Unknown, |access| {
                                if pointer.paths() == crate::VirPointerPaths::root(access) {
                                    ObligationStatus::Proven
                                } else {
                                    ObligationStatus::Unknown
                                }
                            })
                    }
                    _ => ObligationStatus::Proven,
                };
                combine([matched, domain, nominal])
            }
            None => ObligationStatus::Unknown,
        };
        record_check(
            &mut checks,
            ContractCheck {
                clause: expected_value.clause,
                origin: expected_value.origin,
                status,
            },
        );
    }
    for allocation_fact in expected.allocations.values() {
        let status = mapping.get(&allocation_fact.resource).map_or(
            ObligationStatus::Unknown,
            |allocation| {
                match_allocation(
                    state.allocation(*allocation),
                    *allocation_fact,
                    expected
                        .value_ranges
                        .get(&allocation_fact.resource)
                        .map(Vec::as_slice),
                )
            },
        );
        record_check(
            &mut checks,
            ContractCheck {
                clause: allocation_fact.clause,
                origin: allocation_fact.origin,
                status,
            },
        );
    }
    (mapping, checks)
}

fn record_check(checks: &mut Vec<ContractCheck>, check: ContractCheck) {
    if let Some(existing) = checks
        .iter_mut()
        .find(|existing| existing.clause == check.clause && existing.origin == check.origin)
    {
        existing.status = combine([existing.status, check.status]);
    } else {
        checks.push(check);
    }
}

fn match_value(
    actual: AbstractValue,
    expected: ContractValueFactKind,
    mapping: &mut ResourceInstantiation,
) -> ObligationStatus {
    match (actual, expected) {
        (AbstractValue::U64(actual), ContractValueFactKind::U64(expected)) => {
            interval_subset_status(actual, expected)
        }
        (AbstractValue::Bool(actual), ContractValueFactKind::Bool(expected)) => {
            bool_guarantee_status(actual, expected)
        }
        (
            AbstractValue::Pointer(actual),
            ContractValueFactKind::Pointer {
                resource,
                offset_bytes,
                alignment,
                access,
            },
        ) => combine([
            bind_provenance(actual.provenance(), resource, mapping),
            interval_subset_status(actual.offset_bytes(), offset_bytes),
            if actual.alignment().bytes() >= alignment {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Refuted
            },
            match actual.memory_access() {
                Some(found) if found == access => ObligationStatus::Proven,
                Some(_) => ObligationStatus::Refuted,
                None => ObligationStatus::Unknown,
            },
        ]),
        (
            AbstractValue::Permission(actual),
            ContractValueFactKind::Permission {
                resource,
                range,
                access,
                free,
            },
        ) => combine([
            bind_provenance(actual.provenance(), resource, mapping),
            range_guarantee_status(actual.range(), range),
            access_guarantee_status(actual.access(), access),
            free_guarantee_status(actual.free_capability(), free),
            match actual.availability() {
                super::resource::PermissionAvailability::Available => ObligationStatus::Proven,
                super::resource::PermissionAvailability::Consumed => ObligationStatus::Refuted,
                super::resource::PermissionAvailability::MaybeConsumed => ObligationStatus::Unknown,
            },
        ]),
        _ => ObligationStatus::Refuted,
    }
}

fn bind_provenance(
    provenance: AbstractProvenance,
    resource: ContractResourceId,
    mapping: &mut ResourceInstantiation,
) -> ObligationStatus {
    let AbstractProvenance::Known(actual) = provenance else {
        return ObligationStatus::Unknown;
    };
    match mapping.entry(resource) {
        Entry::Vacant(entry) => {
            entry.insert(actual);
            ObligationStatus::Proven
        }
        Entry::Occupied(entry) if *entry.get() == actual => ObligationStatus::Proven,
        Entry::Occupied(_) => ObligationStatus::Refuted,
    }
}

fn match_allocation(
    actual: Option<&AbstractAllocation>,
    expected: ContractAllocationFact,
    ranges: Option<&[ByteRange]>,
) -> ObligationStatus {
    let Some(actual) = actual else {
        return ObligationStatus::Unknown;
    };
    combine([
        if actual.region() == expected.region && actual.size_bytes() == expected.size_bytes {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Refuted
        },
        if actual.alignment().bytes() >= expected.alignment {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Refuted
        },
        enum_guarantee_status(actual.liveness(), expected.liveness),
        ownership_guarantee_status(actual.ownership(), expected.ownership),
        initialization_guarantee_status(actual, expected.initialization, ranges),
    ])
}

fn install_allocations(
    state: &mut ResourceState,
    contract: &ContractState,
    mapping: &ResourceInstantiation,
    replace: bool,
) -> Result<(), ContractApplicationError> {
    for fact in contract.allocations.values().copied() {
        let id = *mapping
            .get(&fact.resource)
            .ok_or(ContractApplicationError::MissingResource(fact.resource))?;
        let allocation = instantiate_allocation(
            fact,
            contract.value_ranges.get(&fact.resource).map(Vec::as_slice),
        )?;
        if replace && state.allocation(id).is_some() {
            state.replace_allocation(id, allocation);
        } else {
            state.define_allocation(id, allocation)?;
        }
    }
    Ok(())
}

fn instantiate_allocation(
    fact: ContractAllocationFact,
    ranges: Option<&[ByteRange]>,
) -> Result<AbstractAllocation, ContractApplicationError> {
    let mut allocation = if let Some(region) = fact.region {
        AbstractAllocation::new(region, fact.size_bytes, fact.alignment)
    } else {
        AbstractAllocation::new_local(fact.size_bytes, fact.alignment)
    }
    .map_err(ContractApplicationError::InvalidAllocation)?;
    allocation.set_liveness(fact.liveness);
    allocation.set_ownership(fact.ownership);
    let whole =
        ByteRange::new(0, fact.size_bytes).map_err(|_| ContractApplicationError::InvalidRange)?;
    if ranges.is_some() {
        allocation.forget_initialization(whole)?;
    }
    for &range in ranges.unwrap_or(std::slice::from_ref(&whole)) {
        match fact.initialization {
            ContractInitialization::Initialized => {
                allocation.mark_initialized(range)?;
                allocation.mark_valid(range)?;
            }
            ContractInitialization::Uninitialized => allocation.mark_uninitialized(range)?,
            ContractInitialization::Unknown => allocation.forget_initialization(range)?,
        }
    }
    Ok(allocation)
}

fn instantiate_value(
    fact: ContractValueFactKind,
    mapping: &ResourceInstantiation,
) -> Result<AbstractValue, ContractApplicationError> {
    Ok(match fact {
        ContractValueFactKind::U64(value) => AbstractValue::U64(value),
        ContractValueFactKind::Bool(value) => AbstractValue::Bool(value),
        ContractValueFactKind::Pointer {
            resource,
            offset_bytes,
            alignment,
            access,
        } => AbstractValue::Pointer(
            AbstractPointer::new(
                AbstractProvenance::Known(
                    *mapping
                        .get(&resource)
                        .ok_or(ContractApplicationError::MissingResource(resource))?,
                ),
                offset_bytes,
                GuaranteedAlignment::new(alignment)
                    .map_err(|_| ContractApplicationError::InvalidAlignment(alignment))?,
            )
            .with_memory_access(Some(access)),
        ),
        ContractValueFactKind::Permission {
            resource,
            range,
            access,
            free,
        } => AbstractValue::Permission(AbstractPermission::new(
            AbstractProvenance::Known(
                *mapping
                    .get(&resource)
                    .ok_or(ContractApplicationError::MissingResource(resource))?,
            ),
            range,
            access,
            free,
        )),
    })
}

const fn unknown_value(ty: VirType) -> AbstractValue {
    match ty {
        VirType::U64 => AbstractValue::U64(U64Interval::unknown()),
        VirType::Bool => AbstractValue::Bool(AbstractBool::Unknown),
        VirType::Pointer { access } => AbstractValue::Pointer(
            AbstractPointer::new(
                AbstractProvenance::Unknown,
                U64Interval::unknown(),
                GuaranteedAlignment::one(),
            )
            .with_memory_access(Some(access)),
        ),
        VirType::Permission => AbstractValue::Permission(
            AbstractPermission::new(
                AbstractProvenance::Unknown,
                AbstractByteRange::Unknown,
                AccessPermission::MaybeWrite,
                FreeCapability::Maybe,
            )
            .with_authority(super::resource::PermissionAuthority::Unknown),
        ),
    }
}

const fn combine<const N: usize>(statuses: [ObligationStatus; N]) -> ObligationStatus {
    let mut index = 0;
    let mut unknown = false;
    while index < N {
        match statuses[index] {
            ObligationStatus::Refuted => return ObligationStatus::Refuted,
            ObligationStatus::Unknown => unknown = true,
            ObligationStatus::Proven => {}
        }
        index += 1;
    }
    if unknown {
        ObligationStatus::Unknown
    } else {
        ObligationStatus::Proven
    }
}

const fn interval_subset_status(actual: U64Interval, expected: U64Interval) -> ObligationStatus {
    if actual.lower() >= expected.lower() && actual.upper() <= expected.upper() {
        ObligationStatus::Proven
    } else if actual.upper() < expected.lower() || actual.lower() > expected.upper() {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Unknown
    }
}

const fn bool_guarantee_status(actual: AbstractBool, expected: AbstractBool) -> ObligationStatus {
    match (actual, expected) {
        (_, AbstractBool::Unknown)
        | (AbstractBool::True, AbstractBool::True)
        | (AbstractBool::False, AbstractBool::False) => ObligationStatus::Proven,
        (AbstractBool::Unknown, _) => ObligationStatus::Unknown,
        _ => ObligationStatus::Refuted,
    }
}

const fn range_guarantee_status(
    actual: AbstractByteRange,
    expected: AbstractByteRange,
) -> ObligationStatus {
    match (actual, expected) {
        (_, AbstractByteRange::Unknown) => ObligationStatus::Proven,
        (AbstractByteRange::Exact(actual), AbstractByteRange::Exact(expected)) => {
            if actual.contains(expected) {
                ObligationStatus::Proven
            } else if !actual.overlaps(expected) {
                ObligationStatus::Refuted
            } else {
                ObligationStatus::Unknown
            }
        }
        (AbstractByteRange::Unknown, AbstractByteRange::Exact(_))
        | (AbstractByteRange::Symbolic { .. }, AbstractByteRange::Exact(_))
        | (_, AbstractByteRange::Symbolic { .. }) => ObligationStatus::Unknown,
    }
}

const fn access_guarantee_status(
    actual: AccessPermission,
    expected: AccessPermission,
) -> ObligationStatus {
    match expected {
        AccessPermission::Read | AccessPermission::MaybeWrite => ObligationStatus::Proven,
        AccessPermission::Write => match actual {
            AccessPermission::Write => ObligationStatus::Proven,
            AccessPermission::Read => ObligationStatus::Refuted,
            AccessPermission::MaybeWrite => ObligationStatus::Unknown,
        },
    }
}

const fn free_guarantee_status(
    actual: FreeCapability,
    expected: FreeCapability,
) -> ObligationStatus {
    match expected {
        FreeCapability::No | FreeCapability::Maybe => ObligationStatus::Proven,
        FreeCapability::Yes => match actual {
            FreeCapability::Yes => ObligationStatus::Proven,
            FreeCapability::No => ObligationStatus::Refuted,
            FreeCapability::Maybe => ObligationStatus::Unknown,
        },
    }
}

const fn enum_guarantee_status(actual: LivenessState, expected: LivenessState) -> ObligationStatus {
    match (actual, expected) {
        (_, LivenessState::MaybeLive)
        | (LivenessState::Live, LivenessState::Live)
        | (LivenessState::Dead, LivenessState::Dead) => ObligationStatus::Proven,
        (LivenessState::MaybeLive, _) => ObligationStatus::Unknown,
        _ => ObligationStatus::Refuted,
    }
}

const fn ownership_guarantee_status(
    actual: OwnershipState,
    expected: OwnershipState,
) -> ObligationStatus {
    match (actual, expected) {
        (_, OwnershipState::MaybeOwned)
        | (_, OwnershipState::Unowned)
        | (OwnershipState::Owned, OwnershipState::Owned) => ObligationStatus::Proven,
        (OwnershipState::MaybeOwned, OwnershipState::Owned) => ObligationStatus::Unknown,
        (OwnershipState::Unowned, OwnershipState::Owned) => ObligationStatus::Refuted,
    }
}

fn initialization_guarantee_status(
    actual: &AbstractAllocation,
    expected: ContractInitialization,
    ranges: Option<&[ByteRange]>,
) -> ObligationStatus {
    let range = ByteRange::new(0, actual.size_bytes()).expect("allocation range is valid");
    let typed = ranges.is_some();
    ranges
        .unwrap_or(std::slice::from_ref(&range))
        .iter()
        .map(
            |range| match (actual.initialization().classify(*range), expected) {
                (InitializationClass::Initialized, ContractInitialization::Initialized)
                    if typed && !actual.valid_value_bytes().contains(*range) =>
                {
                    ObligationStatus::Unknown
                }
                (_, ContractInitialization::Unknown)
                | (InitializationClass::Initialized, ContractInitialization::Initialized)
                | (InitializationClass::Uninitialized, ContractInitialization::Uninitialized) => {
                    ObligationStatus::Proven
                }
                (InitializationClass::MaybeInitialized, _) => ObligationStatus::Unknown,
                _ => ObligationStatus::Refuted,
            },
        )
        .fold(ObligationStatus::Proven, |status, next| {
            combine([status, next])
        })
}

/// Invalid contract schema rejected before it can import facts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContractDefinitionError {
    DuplicateContract(VirContractId),
    DuplicateResource(ContractResourceId),
    DuplicateValueSlot(usize),
    ValueSlotOutOfRange {
        slot: usize,
        count: usize,
    },
    StateArity {
        position: ContractPosition,
        found: usize,
        expected: usize,
    },
    ValueTypeMismatch {
        position: ContractPosition,
        slot: usize,
        expected: VirType,
        found: VirType,
    },
    MissingResource(ContractResourceId),
    DeadAllocationOwned(ContractResourceId),
    FactClauseMismatch {
        fact: VirSpecClauseId,
        origin: VirSpecClauseId,
    },
    MissingOrigin(VirOriginId),
    MissingBinder(crate::VirContractBinderId),
    MissingClause(VirSpecClauseId),
    ForeignClause {
        contract: VirContractId,
        clause: VirSpecClauseId,
    },
    UnsupportedLogicalClause(VirSpecClauseId),
    InvalidAllocation(super::resource::AbstractAllocationError),
    InvalidAlignment(u64),
    InvalidRange,
    SymbolicPermissionRange,
}

impl fmt::Display for ContractDefinitionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateContract(contract) => write!(
                formatter,
                "verifier contract{} is registered more than once",
                contract.get()
            ),
            Self::DuplicateResource(resource) => write!(
                formatter,
                "contract resource {} is defined more than once",
                resource.get()
            ),
            Self::DuplicateValueSlot(slot) => {
                write!(
                    formatter,
                    "contract value slot {slot} is defined more than once"
                )
            }
            Self::ValueSlotOutOfRange { slot, count } => write!(
                formatter,
                "contract value slot {slot} is outside the {count}-value state"
            ),
            Self::StateArity {
                position,
                found,
                expected,
            } => write!(
                formatter,
                "contract {position:?} state has {found} values; expected {expected}"
            ),
            Self::ValueTypeMismatch {
                position,
                slot,
                expected,
                found,
            } => write!(
                formatter,
                "contract {position:?} slot {slot} has type {found:?}; expected {expected:?}"
            ),
            Self::MissingResource(resource) => write!(
                formatter,
                "contract value refers to missing resource {}",
                resource.get()
            ),
            Self::DeadAllocationOwned(resource) => write!(
                formatter,
                "dead contract resource {} cannot remain owned",
                resource.get()
            ),
            Self::FactClauseMismatch { fact, origin } => write!(
                formatter,
                "contract fact clause {} disagrees with source clause {}",
                fact.get(),
                origin.get()
            ),
            Self::MissingOrigin(origin) => {
                write!(
                    formatter,
                    "contract refers to missing origin{}",
                    origin.get()
                )
            }
            Self::MissingBinder(binder) => {
                write!(
                    formatter,
                    "contract refers to missing binder{}",
                    binder.get()
                )
            }
            Self::MissingClause(clause) => {
                write!(
                    formatter,
                    "contract refers to missing clause{}",
                    clause.get()
                )
            }
            Self::ForeignClause { contract, clause } => write!(
                formatter,
                "contract{} refers to foreign clause{}",
                contract.get(),
                clause.get()
            ),
            Self::UnsupportedLogicalClause(clause) => write!(
                formatter,
                "logical contract clause{} is not handled by the stage-6.4.5 verifier",
                clause.get()
            ),
            Self::InvalidAllocation(error) => error.fmt(formatter),
            Self::InvalidAlignment(alignment) => write!(
                formatter,
                "contract pointer alignment {alignment} is not a nonzero power of two"
            ),
            Self::InvalidRange => formatter.write_str("contract contains an invalid byte range"),
            Self::SymbolicPermissionRange => formatter.write_str(
                "contract permission ranges must not contain function-local symbolic values",
            ),
        }
    }
}

impl Error for ContractDefinitionError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::InvalidAllocation(error) => Some(error),
            _ => None,
        }
    }
}

/// Failure while instantiating an already validated contract.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContractApplicationError {
    SignatureMismatch(VirContractId),
    MissingResource(ContractResourceId),
    InvalidAllocation(super::resource::AbstractAllocationError),
    InvalidAlignment(u64),
    InvalidRange,
    StateDefinition(ResourceStateDefinitionError),
}

impl From<ResourceStateDefinitionError> for ContractApplicationError {
    fn from(error: ResourceStateDefinitionError) -> Self {
        Self::StateDefinition(error)
    }
}

impl From<super::resource::AbstractAllocationError> for ContractApplicationError {
    fn from(error: super::resource::AbstractAllocationError) -> Self {
        Self::InvalidAllocation(error)
    }
}

impl fmt::Display for ContractApplicationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SignatureMismatch(contract) => write!(
                formatter,
                "contract{} does not match the function entry signature",
                contract.get()
            ),
            Self::MissingResource(resource) => write!(
                formatter,
                "contract instantiation has no resource {}",
                resource.get()
            ),
            Self::InvalidAllocation(error) => error.fmt(formatter),
            Self::InvalidAlignment(alignment) => write!(
                formatter,
                "contract instantiation has invalid alignment {alignment}"
            ),
            Self::InvalidRange => {
                formatter.write_str("contract instantiation produced an invalid byte range")
            }
            Self::StateDefinition(error) => error.fmt(formatter),
        }
    }
}

impl Error for ContractApplicationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::InvalidAllocation(error) => Some(error),
            Self::StateDefinition(error) => Some(error),
            _ => None,
        }
    }
}
