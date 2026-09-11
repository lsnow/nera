//! Bounded single-instance slots. No generation counter advances during CFG replay.
//!
//! A fresh producer may reuse a retired slot, but must first invalidate all old
//! carriers, even if a join already discarded the allocation's dead tombstone.
//! Multiple outstanding heap instances at one site are deliberately rejected.
use super::*;

pub(super) const MAX_ALLOCATION_SLOTS: usize = 4_096;

impl ResourceState {
    /// A consumed ABI owner may have been freed or replaced in the callee.
    /// This forgets a lifetime guarantee, not outstanding resource/loan state.
    pub(in crate::verifier) fn transfer_opaque_instance(&mut self, id: AbstractAllocationId) {
        if let Some(allocation) = self.allocations.get_mut(&id) {
            allocation.ownership = OwnershipState::Unowned;
            if allocation.liveness != LivenessState::Dead {
                allocation.liveness = LivenessState::MaybeLive;
            }
        }
    }
    pub(in crate::verifier) fn introduce_allocation_instance(
        &mut self,
        id: AbstractAllocationId,
        allocation: AbstractAllocation,
    ) -> Result<(), ResourceStateDefinitionError> {
        let provenance = AbstractProvenance::Known(id);
        // Preflight before mutation: never erase a live/maybe-live resource
        // responsibility or a loan, including an imprecise loan after a join.
        if self.allocations.get(&id).is_some_and(|old| {
            old.liveness != LivenessState::Dead
                && (old.ownership != OwnershipState::Unowned
                    || old
                        .object_state
                        .resource_payloads
                        .values()
                        .any(|p| !matches!(p, MovePathState::Moved)))
        }) || self.loans.values().any(|loan| {
            (loan.provenance == provenance
                || loan.provenance == AbstractProvenance::Unknown
                || loan.authorities.iter().any(|authority| {
                    matches!(authority,
                    AbstractLoanAuthority::Stored { allocation, .. } if *allocation == id)
                }))
                && (loan.activity != LoanActivity::Ended || !loan.authorities.is_empty())
        }) {
            return Err(ResourceStateDefinitionError::AllocationInstanceStillReferenced(id));
        }
        if !self.allocations.contains_key(&id) && self.allocations.len() >= MAX_ALLOCATION_SLOTS {
            return Err(ResourceStateDefinitionError::AllocationInstanceBudget);
        }
        for (value_id, value) in &mut self.values {
            if forget_value(value, provenance) {
                self.relations.forget_value(*value_id);
            }
        }
        for stored in self.allocations.values_mut() {
            for payload in stored.object_state.resource_payloads.values_mut() {
                if let MovePathState::Available(payload) = payload {
                    forget_pointer(&mut payload.pointer, provenance);
                    forget_permission(&mut payload.permission, provenance);
                }
            }
        }
        // Ended records have no remaining authority; discard them so a later
        // loan at the same site cannot attach to an old parent instance.
        self.loans.retain(|_, loan| loan.provenance != provenance);
        self.allocations.insert(id, allocation);
        Ok(())
    }
}

fn forget_pointer(pointer: &mut AbstractPointer, provenance: AbstractProvenance) -> bool {
    if pointer.provenance != provenance {
        return false;
    }
    pointer.provenance = AbstractProvenance::Unknown;
    pointer.slice_footprint = None;
    pointer.domain = crate::VirPointerDomain::Unknown;
    pointer.paths = crate::VirPointerPaths::default();
    true
}

fn forget_permission(permission: &mut AbstractPermission, provenance: AbstractProvenance) -> bool {
    if permission.provenance != provenance {
        return false;
    }
    permission.provenance = AbstractProvenance::Unknown;
    permission.authority = PermissionAuthority::Unknown;
    permission.free = FreeCapability::No;
    true
}

fn forget_value(value: &mut AbstractValue, provenance: AbstractProvenance) -> bool {
    match value {
        AbstractValue::Pointer(pointer) => forget_pointer(pointer, provenance),
        AbstractValue::Permission(permission) => forget_permission(permission, provenance),
        AbstractValue::EnumDiscriminant(fact) if fact.pointer.provenance == provenance => {
            // Keep the scalar observation, not a refinement of the new object.
            *value = AbstractValue::U64(fact.interval);
            true
        }
        _ => false,
    }
}

pub(super) fn join_allocations(
    left: &BTreeMap<AbstractAllocationId, AbstractAllocation>,
    right: &BTreeMap<AbstractAllocationId, AbstractAllocation>,
) -> Result<BTreeMap<AbstractAllocationId, AbstractAllocation>, ResourceJoinError> {
    let mut joined = BTreeMap::new();
    for id in left.keys().chain(right.keys()) {
        if joined.contains_key(id) {
            continue;
        }
        let fact = match (left.get(id), right.get(id)) {
            (Some(left), Some(right)) => left.join(*id, right)?,
            (Some(fact), None) | (None, Some(fact))
                if fact.liveness != LivenessState::Dead
                    && fact.ownership != OwnershipState::Unowned =>
            {
                // Absence is not a proof that the other path freed its owner.
                let mut absent = fact.clone();
                absent.mark_dead();
                fact.join(*id, &absent)?
            }
            // A dead tombstone or frame storage has no independent heap
            // responsibility. Missing layout facts cannot authorize an access;
            // future fresh introduction still invalidates all surviving aliases.
            _ => continue,
        };
        if joined.len() >= MAX_ALLOCATION_SLOTS {
            return Err(ResourceJoinError::AllocationInstanceBudget);
        }
        joined.insert(*id, fact);
    }
    Ok(joined)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opaque_transfer_forgets_liveness_without_erasing_payload_or_loan_debt() {
        let id = AbstractAllocationId::new(0);
        let mut state = ResourceState::new();
        let (pointer, permission) = carriers(id);
        let key = ResourcePayloadKey::new(0, VirMemoryAccess::core_u64());
        let mut allocation = heap();
        allocation
            .set_resource_payload(
                key,
                MovePathState::available(TypedResourcePayload::new(pointer, permission)),
            )
            .unwrap();
        state.define_allocation(id, allocation).unwrap();
        let loan = VirLoanId::new(0);
        state
            .define_loan(
                loan,
                AbstractLoan::new(
                    AbstractProvenance::Unknown,
                    ByteRange::new(0, 8).unwrap(),
                    VirLoanKind::Shared,
                    VirBorrowRegionId::new(0),
                    None,
                    LoanActivity::MaybeActive,
                ),
            )
            .unwrap();
        let loans = state.loans.clone();
        let payload = state.allocation(id).unwrap().resource_payload(key);
        state.transfer_opaque_instance(id);
        assert_eq!(
            state.allocation(id).unwrap().liveness(),
            LivenessState::MaybeLive
        );
        assert_eq!(
            state.allocation(id).unwrap().ownership(),
            OwnershipState::Unowned
        );
        assert_eq!(state.allocation(id).unwrap().resource_payload(key), payload);
        assert_eq!(state.loans, loans);
        assert!(state.introduce_allocation_instance(id, heap()).is_err());
    }

    fn heap() -> AbstractAllocation {
        AbstractAllocation::new(VirRegionId::new(0), 8, 8).unwrap()
    }

    fn carriers(id: AbstractAllocationId) -> (AbstractPointer, AbstractPermission) {
        let provenance = AbstractProvenance::Known(id);
        (
            AbstractPointer::new(
                provenance,
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            ),
            AbstractPermission::new(
                provenance,
                AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap()),
                AccessPermission::Write,
                FreeCapability::Yes,
            ),
        )
    }

    #[test]
    fn retired_slots_recycle_without_generations_or_old_authority() {
        for id in [
            AbstractAllocationId::vir_allocation_site(VirValueId::new(0)),
            AbstractAllocationId::vir_local_storage_site(VirValueId::new(0)),
            AbstractAllocationId::contract_instance(0, 0),
            AbstractAllocationId::abi_call_payload(0, 0, 0),
        ] {
            let mut state = ResourceState::new();
            state.introduce_allocation_instance(id, heap()).unwrap();
            let (pointer, mut permission) = carriers(id);
            permission.mark_consumed();
            state
                .define_value(VirValueId::new(1), AbstractValue::Pointer(pointer))
                .unwrap();
            state
                .define_value(VirValueId::new(2), AbstractValue::Permission(permission))
                .unwrap();
            for _ in 0..32 {
                state.allocation_mut(id).unwrap().mark_dead();
                state.introduce_allocation_instance(id, heap()).unwrap();
                assert_eq!(state.allocations.len(), 1);
                let AbstractValue::Pointer(old) = state.values[&VirValueId::new(1)] else {
                    panic!()
                };
                let AbstractValue::Permission(old_permission) = state.values[&VirValueId::new(2)]
                else {
                    panic!()
                };
                assert_eq!(old.provenance(), AbstractProvenance::Unknown);
                assert_eq!(old_permission.provenance(), AbstractProvenance::Unknown);
                assert_eq!(
                    old_permission.availability(),
                    PermissionAvailability::Consumed
                );
                assert_eq!(old_permission.authority(), PermissionAuthority::Unknown);
            }
        }
    }

    #[test]
    fn discarded_tombstones_do_not_hide_stored_aliases_or_tag_origins() {
        let id = AbstractAllocationId::vir_allocation_site(VirValueId::new(0));
        let (pointer, permission) = carriers(id);
        let mut state = ResourceState::new();
        // The old allocation record is already gone, but other carriers remain.
        let container = AbstractAllocationId::new(10);
        let key = ResourcePayloadKey::new(0, VirMemoryAccess::core_u64());
        let mut storage = AbstractAllocation::new_local(8, 8).unwrap();
        storage
            .set_resource_payload(
                key,
                MovePathState::available(TypedResourcePayload::new(pointer, permission)),
            )
            .unwrap();
        state.define_allocation(container, storage).unwrap();
        state
            .define_value(
                VirValueId::new(1),
                AbstractValue::EnumDiscriminant(EnumDiscriminantFact::new(
                    U64Interval::exact(1),
                    pointer,
                    VirMemoryAccess::core_u64(),
                )),
            )
            .unwrap();
        state.introduce_allocation_instance(id, heap()).unwrap();
        assert_eq!(
            state.value(VirValueId::new(1)),
            Some(&AbstractValue::U64(U64Interval::exact(1)))
        );
        let MovePathState::Available(old) = state
            .allocation(container)
            .unwrap()
            .object_state()
            .resource_payload(key)
        else {
            panic!()
        };
        assert_eq!(old.pointer().provenance(), AbstractProvenance::Unknown);
        assert_eq!(old.permission().authority(), PermissionAuthority::Unknown);
    }

    #[test]
    fn live_or_maybe_live_instances_cannot_be_overwritten_even_after_join() {
        let id = AbstractAllocationId::contract_instance(0, 0);
        let mut live = ResourceState::new();
        live.define_allocation(id, heap()).unwrap();
        let joined = live.join(&ResourceState::new()).unwrap();
        assert_eq!(
            joined.allocation(id).unwrap().liveness(),
            LivenessState::MaybeLive
        );
        assert_eq!(
            joined.allocation(id).unwrap().ownership(),
            OwnershipState::MaybeOwned
        );
        assert_eq!(joined, ResourceState::new().join(&live).unwrap());
        assert_eq!(joined, joined.widen(&joined).unwrap());
        for mut state in [live, joined] {
            let before = state.clone();
            assert_eq!(
                state.introduce_allocation_instance(id, heap()),
                Err(ResourceStateDefinitionError::AllocationInstanceStillReferenced(id))
            );
            assert_eq!(state, before);
        }
    }

    #[test]
    fn active_or_unknown_loan_blocks_reuse_without_losing_its_obligation() {
        let id = AbstractAllocationId::vir_local_storage_site(VirValueId::new(0));
        for provenance in [AbstractProvenance::Known(id), AbstractProvenance::Unknown] {
            let mut state = ResourceState::new();
            let loan = AbstractLoan::new(
                provenance,
                ByteRange::new(0, 8).unwrap(),
                VirLoanKind::Shared,
                VirBorrowRegionId::new(0),
                None,
                LoanActivity::MaybeActive,
            );
            state.loans.insert(VirLoanId::new(0), loan);
            let before = state.clone();
            assert_eq!(
                state.introduce_allocation_instance(id, heap()),
                Err(ResourceStateDefinitionError::AllocationInstanceStillReferenced(id))
            );
            assert_eq!(state, before);
        }
    }

    #[test]
    fn frame_storage_reuse_forgets_aliases_but_cannot_discard_owned_payloads() {
        let id = AbstractAllocationId::vir_local_storage_site(VirValueId::new(0));
        let mut state = ResourceState::new();
        state
            .define_allocation(id, AbstractAllocation::new_local(8, 8).unwrap())
            .unwrap();
        let (pointer, permission) = carriers(id);
        state
            .define_value(VirValueId::new(1), AbstractValue::Pointer(pointer))
            .unwrap();
        state
            .introduce_allocation_instance(id, AbstractAllocation::new_local(8, 8).unwrap())
            .unwrap();
        let AbstractValue::Pointer(old) = state.values[&VirValueId::new(1)] else {
            panic!()
        };
        assert_eq!(old.provenance(), AbstractProvenance::Unknown);
        let key = ResourcePayloadKey::new(0, VirMemoryAccess::core_u64());
        state
            .allocation_mut(id)
            .unwrap()
            .set_resource_payload(
                key,
                MovePathState::available(TypedResourcePayload::new(pointer, permission)),
            )
            .unwrap();
        assert_eq!(
            state.introduce_allocation_instance(id, AbstractAllocation::new_local(8, 8).unwrap()),
            Err(ResourceStateDefinitionError::AllocationInstanceStillReferenced(id))
        );
    }

    #[test]
    fn stored_loan_authority_prevents_reuse_of_its_container() {
        let id = AbstractAllocationId::vir_local_storage_site(VirValueId::new(0));
        let key = ResourcePayloadKey::new(0, VirMemoryAccess::core_u64());
        let mut state = ResourceState::new();
        let mut loan = AbstractLoan::new(
            AbstractProvenance::Known(AbstractAllocationId::new(1)),
            ByteRange::new(0, 8).unwrap(),
            VirLoanKind::Shared,
            VirBorrowRegionId::new(0),
            None,
            LoanActivity::Active,
        );
        loan.authorities
            .insert(AbstractLoanAuthority::stored(id, key));
        state.loans.insert(VirLoanId::new(0), loan);
        let before = state.clone();
        assert_eq!(
            state.introduce_allocation_instance(id, AbstractAllocation::new_local(8, 8).unwrap()),
            Err(ResourceStateDefinitionError::AllocationInstanceStillReferenced(id))
        );
        assert_eq!(state, before);
    }

    #[test]
    fn slot_budget_never_evicts_owners_or_restores_old_permissions() {
        let mut left = ResourceState::new();
        for index in 0..MAX_ALLOCATION_SLOTS {
            left.define_allocation(AbstractAllocationId::new(index as u32), heap())
                .unwrap();
        }
        let extra = AbstractAllocationId::new(MAX_ALLOCATION_SLOTS as u32);
        let before = left.clone();
        for _ in 0..2 {
            assert_eq!(
                left.introduce_allocation_instance(extra, heap()),
                Err(ResourceStateDefinitionError::AllocationInstanceBudget)
            );
            assert_eq!(left, before);
        }
        let mut right = ResourceState::new();
        right.define_allocation(extra, heap()).unwrap();
        assert_eq!(
            left.join(&right),
            Err(ResourceJoinError::AllocationInstanceBudget)
        );
        assert_eq!(left, before);
    }
}
