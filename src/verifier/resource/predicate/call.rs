//! Exact, linear call mapping for the internal predicate calculus. No predicate
//! body or declared postcondition is imported as a trusted callee result.
use super::*;
mod scalars;
use scalars::copy_scalars;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PredicateCallBinding {
    pub caller: PredicateHolder,
    pub callee: PredicateHolder,
}

/// Explicit scalar ABI for the internal calculus. Entry copies caller to
/// callee; return copies callee to a fresh caller SSA slot. No authority travels
/// through these slots, and matching numeric intervals never imply a mapping.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PredicateScalarCallBinding {
    pub caller: VirValueId,
    pub callee: VirValueId,
}

/// A suspended caller. Returning consumes the frame; the only accepted result
/// is an actual callee resource state with restored boundaries and no leaks.
#[derive(Debug)]
pub struct PredicateCallFrame {
    caller: ResourceState,
    allocations: BTreeSet<AbstractAllocationId>,
    definitions: Vec<PredicateDefinition>,
}

pub fn enter_predicate_call(
    caller: &ResourceState,
    bindings: &[PredicateCallBinding],
) -> Result<(PredicateCallFrame, ResourceState), PredicateError> {
    enter_predicate_call_with_scalars(caller, bindings, &[])
}

pub fn enter_predicate_call_with_scalars(
    caller: &ResourceState,
    bindings: &[PredicateCallBinding],
    scalars: &[PredicateScalarCallBinding],
) -> Result<(PredicateCallFrame, ResourceState), PredicateError> {
    if !caller.path_condition().is_reachable() {
        return Err(PredicateError::InvalidBinding);
    }
    if bindings.len() > MAX_PREDICATE_INSTANCES || scalars.len() > MAX_PREDICATE_LOCAL_ALIASES {
        return Err(PredicateError::Budget);
    }
    // Every potentially observing call is a representation boundary, including
    // calls which receive none of the currently held predicates.
    if caller.predicates.values().any(|p| !p.folded) {
        return Err(PredicateError::OpenBoundary);
    }
    // Suspended holders also remain live representation obligations. An empty
    // binding list must not turn a violated snapshot into a valid call frame.
    if caller
        .predicates
        .values()
        .any(|p| !caller.predicate_representation_valid(p))
    {
        return Err(PredicateError::UnprovedRepresentation);
    }
    let mut suspended = caller.clone();
    let mut callee = ResourceState::new();
    callee.next_predicate_scope = caller.next_predicate_scope;
    let mut sources = BTreeSet::new();
    let mut targets = BTreeSet::new();
    let mut allocations = BTreeSet::new();
    let mut definitions = Vec::new();
    let mut scopes = BTreeMap::new();
    let mut budget = crate::predicate_logic::LogicBudget::default();
    let mut histories = ScalarOriginTransport::default();
    let scalar_pairs = scalars
        .iter()
        .map(|s| (s.caller, s.callee))
        .collect::<Vec<_>>();
    copy_scalars(
        caller,
        &mut callee,
        &scalar_pairs,
        &mut histories,
        &mut budget,
    )?;
    let remapper = ExpressionRemapper::new(caller, &scalar_pairs);
    for binding in bindings {
        if !sources.insert(binding.caller) || !targets.insert(binding.callee) {
            return Err(PredicateError::AliasedAuthority);
        }
        let mut instance = suspended
            .predicates
            .remove(&binding.caller)
            .ok_or(PredicateError::MissingHolder)?;
        for resource in &instance.resources {
            // This internal mapping has no loan ABI. A live external view
            // must stay in the caller frame rather than disappear at entry.
            if resource.permission.authority() != PermissionAuthority::Owner
                || !caller.loan_precision_losses.is_empty()
                || caller.loans.values().any(|loan| {
                    loan.activity() != LoanActivity::Ended
                        && (loan.provenance() == resource.pointer.provenance()
                            || loan.provenance() == AbstractProvenance::Unknown)
                })
            {
                return Err(PredicateError::Borrowed);
            }
            if !allocations.insert(resource.allocation) {
                return Err(PredicateError::AliasedAuthority);
            }
            let allocation = suspended
                .allocations
                .get_mut(&resource.allocation)
                .ok_or(PredicateError::UnprovedRepresentation)?;
            if allocation.liveness() != LivenessState::Live
                || allocation.ownership() != OwnershipState::Owned
            {
                return Err(PredicateError::UnprovedRepresentation);
            }
            let mut transferred = allocation.clone();
            transferred.reduce_initialization_prefixes(&caller.values);
            transferred.project_call_initialization(
                &remapper,
                &caller.values,
                !scalar_pairs.is_empty(),
            );
            histories
                .allocation(
                    &mut transferred,
                    &mut callee.next_predicate_scope,
                    &mut budget,
                )
                .map_err(logic::map_error)?;
            callee.allocations.insert(resource.allocation, transferred);
            allocation.set_ownership(OwnershipState::Unowned);
        }
        if !caller.predicate_representation_valid(&instance) {
            return Err(PredicateError::UnprovedRepresentation);
        }
        // Scalar slots do not map permission carriers. Never import caller
        // authority identities into the callee namespace.
        for resource in &mut instance.resources {
            resource.carrier = None;
        }
        definitions.push(instance.definition.clone());
        callee.predicates.insert(binding.callee, instance);
    }
    // Build the whole memory mapping before substituting any package. A saved
    // relation may mention a history carried by another resource in the group.
    for instance in callee.predicates.values_mut() {
        logic::freshen_instance(
            instance,
            &mut callee.next_predicate_scope,
            &mut scopes,
            &mut budget,
            &histories,
            &scalar_pairs,
        )?;
    }
    if callee
        .predicates
        .values()
        .any(|p| !callee.predicate_representation_valid(p))
    {
        return Err(PredicateError::UnprovedRepresentation);
    }
    Ok((
        PredicateCallFrame {
            caller: suspended,
            allocations,
            definitions,
        },
        callee,
    ))
}

impl PredicateCallFrame {
    pub fn resume(
        self,
        callee: &ResourceState,
        results: &[PredicateCallBinding],
    ) -> Result<ResourceState, PredicateError> {
        self.resume_with_scalars(callee, results, &[])
    }

    pub fn resume_with_scalars(
        mut self,
        callee: &ResourceState,
        results: &[PredicateCallBinding],
        scalars: &[PredicateScalarCallBinding],
    ) -> Result<ResourceState, PredicateError> {
        self.caller.next_predicate_scope = self
            .caller
            .next_predicate_scope
            .max(callee.next_predicate_scope);
        if !callee.path_condition().is_reachable() {
            return Err(PredicateError::InvalidBinding);
        }
        if results.len() > MAX_PREDICATE_INSTANCES || scalars.len() > MAX_PREDICATE_LOCAL_ALIASES {
            return Err(PredicateError::Budget);
        }
        if callee
            .loans
            .values()
            .any(|loan| loan.activity() != LoanActivity::Ended || !loan.authorities().is_empty())
        {
            return Err(PredicateError::Borrowed);
        }
        callee.check_predicate_boundary(&results.iter().map(|r| r.callee).collect::<Vec<_>>())?;
        let mut returned = BTreeSet::new();
        let mut destinations = BTreeSet::new();
        let mut scopes = BTreeMap::new();
        let mut budget = crate::predicate_logic::LogicBudget::default();
        let mut histories = ScalarOriginTransport::default();
        let scalar_pairs = scalars
            .iter()
            .map(|s| (s.callee, s.caller))
            .collect::<Vec<_>>();
        copy_scalars(
            callee,
            &mut self.caller,
            &scalar_pairs,
            &mut histories,
            &mut budget,
        )?;
        let remapper = ExpressionRemapper::new(callee, &scalar_pairs);
        for result in results {
            if !destinations.insert(result.caller)
                || self.caller.predicates.contains_key(&result.caller)
            {
                return Err(PredicateError::HolderOccupied);
            }
            let instance = &callee.predicates[&result.callee];
            if !self.definitions.contains(&instance.definition) {
                return Err(PredicateError::WrongDeclaration);
            }
            for resource in &instance.resources {
                if !self.allocations.contains(&resource.allocation)
                    || !returned.insert(resource.allocation)
                {
                    return Err(PredicateError::InvalidBinding);
                }
            }
            let mut returned_instance = instance.clone();
            for resource in &mut returned_instance.resources {
                resource.carrier = None;
            }
            self.caller
                .predicates
                .insert(result.caller, returned_instance);
        }
        // New allocations and temporary objects must be cleaned by the actual
        // body. No postcondition can erase an outstanding callee obligation.
        for (id, allocation) in &callee.allocations {
            if !returned.contains(id)
                && allocation.liveness() != LivenessState::Dead
                && allocation.ownership() != OwnershipState::Unowned
            {
                return Err(PredicateError::OutstandingCleanup);
            }
        }
        for id in self.allocations {
            let allocation = callee
                .allocation(id)
                .ok_or(PredicateError::OutstandingCleanup)?;
            if returned.contains(&id) {
                if allocation.liveness() != LivenessState::Live
                    || allocation.ownership() != OwnershipState::Owned
                {
                    return Err(PredicateError::UnprovedRepresentation);
                }
            } else if allocation.liveness() != LivenessState::Dead {
                return Err(PredicateError::OutstandingCleanup);
            }
            let mut transferred = allocation.clone();
            transferred.reduce_initialization_prefixes(&callee.values);
            transferred.project_call_initialization(
                &remapper,
                &callee.values,
                !scalar_pairs.is_empty(),
            );
            histories
                .allocation(
                    &mut transferred,
                    &mut self.caller.next_predicate_scope,
                    &mut budget,
                )
                .map_err(logic::map_error)?;
            self.caller.allocations.insert(id, transferred);
        }
        for result in results {
            let instance = self
                .caller
                .predicates
                .get_mut(&result.caller)
                .ok_or(PredicateError::MissingHolder)?;
            logic::freshen_instance(
                instance,
                &mut self.caller.next_predicate_scope,
                &mut scopes,
                &mut budget,
                &histories,
                &scalar_pairs,
            )?;
        }
        if self
            .caller
            .predicates
            .values()
            .any(|instance| !self.caller.predicate_representation_valid(instance))
        {
            return Err(PredicateError::UnprovedRepresentation);
        }
        Ok(self.caller)
    }
}
