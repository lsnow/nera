//! Resource adapter for typed scalar observations. These checks grant no free
//! authority and prove no logical constraint: they supply actual readable values
//! and surviving histories to the predicate expression adapter.
use super::*;
use crate::predicate_logic::LogicType;

impl ResourceState {
    pub(super) fn predicate_memory_location(
        &self,
        ty: LogicType<VirMemoryAccess>,
        base: VirValueId,
        offset: u64,
    ) -> Result<(AbstractAllocationId, ByteRange), PredicateError> {
        let width = match ty {
            LogicType::Bool => 1,
            LogicType::U64 | LogicType::Usize => 8,
            _ => return Err(PredicateError::InvalidBinding),
        };
        let Some(AbstractValue::Pointer(pointer)) = self.value(base) else {
            return Err(PredicateError::InvalidBinding);
        };
        let AbstractProvenance::Known(id) = pointer.provenance() else {
            return Err(PredicateError::InvalidBinding);
        };
        let offset = pointer
            .offset_bytes()
            .exact_value()
            .and_then(|base| base.checked_add(offset))
            .ok_or(PredicateError::InvalidBinding)?;
        let range = ByteRange::from_start_and_length(offset, width)
            .map_err(|_| PredicateError::InvalidBinding)?;
        let allocation = self
            .allocation(id)
            .ok_or(PredicateError::MissingAuthority)?;
        if pointer.memory_access().is_none()
            || allocation.liveness() != LivenessState::Live
            || range.end() > allocation.size_bytes()
            || allocation.initialization().classify(range) != InitializationClass::Initialized
            || !allocation.valid_value_bytes().contains(range)
            || !self.loan_precision_losses.is_empty()
        {
            return Err(PredicateError::UnprovedRepresentation);
        }
        let readable = self.values.iter().any(|(carrier, value)| {
            let AbstractValue::Permission(permission) = value else { return false; };
            if permission.availability() != PermissionAvailability::Available
                || permission.provenance() != pointer.provenance()
                || !matches!(permission.range(), AbstractByteRange::Exact(allowed) if allowed.contains(range))
            { return false; }
            let own_loan = match permission.authority() {
                // An available ordinary token can read local/ABI storage too.
                // Allocation ownership is free authority, not read authority;
                // requiring it here rejects real initialized return buffers.
                PermissionAuthority::Owner => None,
                PermissionAuthority::Loan(loan) if self.loan(loan).is_some_and(|loan| loan.activity() == LoanActivity::Active && loan.has_value_authority(*carrier) && loan.provenance() == pointer.provenance() && loan.actual_range() == permission.range()) => Some(loan),
                _ => return false,
            };
            let mut ancestors=BTreeSet::new();
            let mut parent=own_loan.and_then(|id| self.loan(id)).and_then(|loan| loan.parent());
            for _ in 0..64 {
                let Some(id)=parent else { break; };
                let Some(loan)=self.loan(id) else { return false; };
                if !ancestors.insert(id) || loan.activity()!=LoanActivity::Suspended || loan.provenance()!=pointer.provenance()
                    || !matches!(loan.actual_range(),AbstractByteRange::Exact(allowed) if allowed.contains(range)) { return false; }
                parent=loan.parent();
            }
            if parent.is_some() { return false; }
            !self.loans.iter().any(|(id, loan)| loan.activity() != LoanActivity::Ended && Some(*id) != own_loan && !ancestors.contains(id)
                && (loan.provenance() == AbstractProvenance::Unknown || (loan.provenance() == pointer.provenance()
                    && loan.kind() != crate::VirLoanKind::Shared
                    && !matches!(loan.actual_range(), AbstractByteRange::Exact(other) if !other.overlaps(range)))))
        });
        if !readable {
            return Err(PredicateError::MissingAuthority);
        }
        Ok((id, range))
    }

    pub(in crate::verifier::resource) fn predicate_memory_snapshot(
        &self,
        ty: LogicType<VirMemoryAccess>,
        base: VirValueId,
        offset: u64,
        access: VirMemoryAccess,
    ) -> Result<(AbstractValue, Option<ScalarOrigin>, Option<BoolOrigin>), PredicateError> {
        let view = self.predicate_observation_view();
        let (id, range) = view.predicate_memory_location(ty, base, offset)?;
        let allocation = view.allocation(id).ok_or(PredicateError::InvalidBinding)?;
        let value = match (ty, allocation.scalar_content(range, access)) {
            (LogicType::Bool, Some(value @ AbstractValue::Bool(_))) => value,
            (LogicType::Bool, None) => AbstractValue::Bool(AbstractBool::Unknown),
            (LogicType::U64 | LogicType::Usize, Some(value @ AbstractValue::U64(_))) => value,
            (LogicType::U64 | LogicType::Usize, None) => AbstractValue::U64(U64Interval::unknown()),
            _ => return Err(PredicateError::InvalidBinding),
        };
        Ok((
            value,
            allocation.scalar_origin(range, access),
            allocation.bool_origin(range, access),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn local() -> (ResourceState, AbstractAllocationId, VirValueId, VirValueId) {
        let allocation_id = AbstractAllocationId::vir_local_storage_site(VirValueId::new(0));
        let pointer = VirValueId::new(0);
        let permission = VirValueId::new(1);
        let bytes = ByteRange::new(0, 8).unwrap();
        let access = VirMemoryAccess::core_u64();
        let mut allocation = AbstractAllocation::new_local(8, 8).unwrap();
        allocation.mark_initialized(bytes).unwrap();
        allocation.mark_valid(bytes).unwrap();
        allocation.record_scalar_content(bytes, access, AbstractValue::U64(U64Interval::exact(42)));
        let mut state = ResourceState::new();
        state.define_allocation(allocation_id, allocation).unwrap();
        state
            .define_value(
                pointer,
                AbstractValue::Pointer(
                    AbstractPointer::new(
                        AbstractProvenance::Known(allocation_id),
                        U64Interval::exact(0),
                        GuaranteedAlignment::new(8).unwrap(),
                    )
                    .with_memory_access(Some(access)),
                ),
            )
            .unwrap();
        state
            .define_value(
                permission,
                AbstractValue::Permission(AbstractPermission::new(
                    AbstractProvenance::Known(allocation_id),
                    AbstractByteRange::Exact(bytes),
                    AccessPermission::Write,
                    FreeCapability::No,
                )),
            )
            .unwrap();
        (state, allocation_id, pointer, permission)
    }

    #[test]
    fn initialized_local_storage_is_readable_without_heap_free_authority() {
        let (state, allocation, pointer, _) = local();
        let before = state.clone();
        assert_eq!(
            state.allocation(allocation).unwrap().ownership(),
            OwnershipState::Unowned
        );
        assert_eq!(
            state
                .predicate_memory_snapshot(LogicType::U64, pointer, 0, VirMemoryAccess::core_u64())
                .unwrap()
                .0,
            AbstractValue::U64(U64Interval::exact(42))
        );
        assert_eq!(
            state, before,
            "observation must not install authority or change storage"
        );
    }

    #[test]
    fn local_observations_still_require_actual_live_initialized_authorized_bytes() {
        for mutation in 0..6 {
            let (mut state, allocation, pointer, permission) = local();
            match mutation {
                0 => state.allocation_mut(allocation).unwrap().mark_dead(),
                1 => state
                    .allocation_mut(allocation)
                    .unwrap()
                    .forget_initialization(ByteRange::new(0, 8).unwrap())
                    .unwrap(),
                2 => {
                    state.values.remove(&permission);
                }
                3 => {
                    let AbstractValue::Permission(token) = *state.value(permission).unwrap() else {
                        unreachable!()
                    };
                    *state.value_mut(permission).unwrap() = AbstractValue::Permission(
                        token.with_availability(PermissionAvailability::Consumed),
                    );
                }
                4 | 5 => {
                    *state.value_mut(permission).unwrap() =
                        AbstractValue::Permission(AbstractPermission::new(
                            if mutation == 4 {
                                AbstractProvenance::Unknown
                            } else {
                                AbstractProvenance::Known(allocation)
                            },
                            AbstractByteRange::Exact(
                                ByteRange::new(0, if mutation == 5 { 4 } else { 8 }).unwrap(),
                            ),
                            AccessPermission::Write,
                            FreeCapability::No,
                        ));
                }
                _ => unreachable!(),
            }
            assert!(
                state
                    .predicate_memory_snapshot(
                        LogicType::U64,
                        pointer,
                        0,
                        VirMemoryAccess::core_u64()
                    )
                    .is_err(),
                "mutation {mutation}"
            );
        }
    }
}
