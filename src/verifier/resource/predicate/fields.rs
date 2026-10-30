//! Typed field payload admission. Pure logic receives identities only after
//! this adapter has checked the actual storage and capability carriers.
use super::*;

impl ResourceState {
    pub(in crate::verifier) fn bounded_field_payload(
        &self,
        storage: AbstractAllocationId,
        field: &crate::vir::PredicateResourceField,
    ) -> Result<TypedResourcePayload, PredicateError> {
        let object = self
            .allocation(storage)
            .ok_or(PredicateError::UnprovedRepresentation)?;
        let key = ResourcePayloadKey::new(field.offset, field.access);
        let MovePathState::Available(payload) = object.resource_payload(key) else {
            return Err(PredicateError::MissingAuthority);
        };
        let pointer = payload.pointer();
        let permission = payload.permission();
        let AbstractProvenance::Known(child) = pointer.provenance() else {
            return Err(PredicateError::MissingAuthority);
        };
        let allocation = self
            .allocation(child)
            .ok_or(PredicateError::UnprovedRepresentation)?;
        let base = pointer
            .offset_bytes()
            .exact_value()
            .ok_or(PredicateError::InvalidBinding)?;
        let whole = ByteRange::from_start_and_length(base, field.size)
            .map_err(|_| PredicateError::InvalidDefinition)?;
        let cell = ByteRange::from_start_and_length(field.offset, 8)
            .map_err(|_| PredicateError::InvalidDefinition)?;
        if child == storage
            || object.liveness() != LivenessState::Live
            || object.initialization().classify(cell) != InitializationClass::Initialized
            || !object.valid_value_bytes().contains(cell)
            || allocation.liveness() != LivenessState::Live
            || field.value_bytes.iter().any(|(start, end)| {
                base.checked_add(*start)
                    .zip(base.checked_add(*end))
                    .and_then(|(s, e)| ByteRange::new(s, e).ok())
                    .is_none_or(|range| {
                        allocation.initialization().classify(range)
                            != InitializationClass::Initialized
                            || !allocation.valid_value_bytes().contains(range)
                    })
            })
            || pointer.memory_access() != Some(field.pointee)
            || whole.end() > allocation.size_bytes()
            || permission.provenance() != pointer.provenance()
            || permission.range() != AbstractByteRange::Exact(whole)
            || permission.availability() != PermissionAvailability::Available
        {
            return Err(PredicateError::UnprovedRepresentation);
        }
        match (field.kind, permission.authority()) {
            (crate::VirPointerKind::Own, PermissionAuthority::Owner) => {
                let borrowed = self.loans.values().any(|loan| {
                    loan.activity() != LoanActivity::Ended
                        && loan.provenance() == pointer.provenance()
                });
                let aliases_value = self.values.values().any(|value| {
                    matches!(value, AbstractValue::Permission(p)
                        if p.availability() != PermissionAvailability::Consumed
                        && (p.provenance() == pointer.provenance() || p.provenance() == AbstractProvenance::Unknown))
                });
                let aliases_storage = self.allocations.iter().any(|(id, allocation)| {
                    allocation.object_state().resource_payloads().iter().any(|(other, state)| {
                        (*id != storage || *other != key)
                            && matches!(state, MovePathState::Available(p)
                                if p.permission().availability() != PermissionAvailability::Consumed
                                && (p.pointer().provenance() == pointer.provenance() || p.pointer().provenance() == AbstractProvenance::Unknown))
                    })
                });
                if base != 0
                    || allocation.size_bytes() != field.size
                    || allocation.ownership() != OwnershipState::Owned
                    || permission.access() != AccessPermission::Write
                    || permission.free_capability() != FreeCapability::Yes
                    || borrowed
                    || aliases_value
                    || aliases_storage
                {
                    return Err(PredicateError::AliasedAuthority);
                }
            }
            (crate::VirPointerKind::Reference, PermissionAuthority::Loan(id)) => {
                let expected = if field.mutability == crate::VirMutability::Const {
                    crate::VirLoanKind::Shared
                } else {
                    crate::VirLoanKind::Mutable
                };
                let access = if expected == crate::VirLoanKind::Shared {
                    AccessPermission::Read
                } else {
                    AccessPermission::Write
                };
                let loan = self.loan(id).ok_or(PredicateError::MissingAuthority)?;
                let carriers_valid = loan.authorities().iter().all(|authority| match *authority {
                    AbstractLoanAuthority::Value(value) => self.value(value) == Some(&AbstractValue::Permission(permission)),
                    AbstractLoanAuthority::Stored { allocation, payload } => self.allocation(allocation).is_some_and(|object| {
                        object.liveness() == LivenessState::Live && matches!(object.resource_payload(payload), MovePathState::Available(value) if value.permission() == permission)
                    }),
                });
                if permission.free_capability() != FreeCapability::No
                    || permission.access() != access
                    || loan.activity() != LoanActivity::Active
                    || loan.kind() != expected
                    || loan.provenance() != pointer.provenance()
                    || loan.actual_range() != permission.range()
                    || !loan
                        .authorities()
                        .contains(&AbstractLoanAuthority::stored(storage, key))
                    || !carriers_valid
                    || (expected == crate::VirLoanKind::Mutable && loan.authorities().len() != 1)
                    || self.loans.values().any(|child| {
                        child.parent() == Some(id) && child.activity() != LoanActivity::Ended
                    })
                {
                    return Err(PredicateError::MissingAuthority);
                }
            }
            _ => return Err(PredicateError::MissingAuthority),
        }
        Ok(*payload)
    }

    pub(super) fn predicate_fields_valid(
        &self,
        definition: &PredicateDefinition,
        index: usize,
        storage: AbstractAllocationId,
    ) -> Result<(), PredicateError> {
        let fields = definition
            .resource_fields
            .get(index)
            .ok_or(PredicateError::InvalidDefinition)?;
        let allocation = self
            .allocation(storage)
            .ok_or(PredicateError::UnprovedRepresentation)?;
        for (key, state) in allocation.object_state().resource_payloads() {
            if !matches!(state, MovePathState::Moved)
                && !fields
                    .iter()
                    .any(|field| *key == ResourcePayloadKey::new(field.offset, field.access))
            {
                return Err(PredicateError::UnsupportedStorage);
            }
        }
        for field in fields {
            self.bounded_field_payload(storage, field)?;
        }
        Ok(())
    }
}
