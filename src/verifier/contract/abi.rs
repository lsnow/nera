//! Typed ABI summaries describe value bytes, not padding. Derive their ranges
//! again from the canonical ABI/schema, never from lowering-supplied masks.

use super::*;

pub(super) fn install_value_ranges(
    program: &ResolvedVirUnit<'_>,
    contract: &crate::VirContract,
    requires: &mut ContractState,
    ensures: &mut ContractState,
) -> Result<(), ContractDefinitionError> {
    let Some(abi) = program.runtime().abis.function(contract.function) else {
        return Ok(());
    };
    for (binding, result_buffer) in abi
        .signature
        .parameters()
        .iter()
        .map(|binding| (binding, false))
        .chain(
            abi.signature
                .results()
                .iter()
                .map(|binding| (binding, true)),
        )
    {
        let crate::VirAbiValue::IndirectAggregate { access } = binding.value() else {
            continue;
        };
        let [pointer_slot, permission_slot] = binding.parameter_slots() else {
            return Err(ContractDefinitionError::InvalidRange);
        };
        let [returned_slot] = binding.result_slots() else {
            return Err(ContractDefinitionError::InvalidRange);
        };
        let Some(pointer) = requires
            .values
            .get(*pointer_slot as usize)
            .copied()
            .flatten()
        else {
            return Err(ContractDefinitionError::InvalidRange);
        };
        let ContractValueFactKind::Pointer {
            resource,
            offset_bytes,
            access: pointer_access,
            ..
        } = pointer.kind
        else {
            return Err(ContractDefinitionError::InvalidRange);
        };
        // Explicit summaries retain byte-oriented semantics, even on a typed ABI.
        let inferred = matches!(
            pointer.origin.source,
            VirSpecClauseOrigin::InferredType { .. }
        );
        if offset_bytes.exact_value() != Some(0) || pointer_access != *access {
            return Err(ContractDefinitionError::InvalidRange);
        }
        let shape = program
            .runtime()
            .memory
            .object_shape(*access)
            .map_err(|_| ContractDefinitionError::InvalidRange)?;
        // Variant-dependent summaries remain outside this unconditional model.
        if !shape.variants().is_empty() {
            return Err(ContractDefinitionError::InvalidRange);
        }
        let ranges = shape
            .value_bytes()
            .iter()
            .map(|bytes| {
                ByteRange::new(bytes.start_bytes(), bytes.end_bytes())
                    .map_err(|_| ContractDefinitionError::InvalidRange)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let before = if result_buffer {
            ContractInitialization::Uninitialized
        } else {
            ContractInitialization::Initialized
        };
        let after = if !result_buffer
            && binding.interface().transfer == crate::VirInterfaceTransfer::Move
        {
            ContractInitialization::Uninitialized
        } else {
            ContractInitialization::Initialized
        };
        for (state, slot, initialization) in [
            (&mut *requires, *permission_slot, before),
            (&mut *ensures, *returned_slot, after),
        ] {
            let fact = state
                .allocations
                .get(&resource)
                .ok_or(ContractDefinitionError::MissingResource(resource))?;
            let permission = state
                .values
                .get(slot as usize)
                .copied()
                .flatten()
                .ok_or(ContractDefinitionError::InvalidRange)?;
            if matches!(fact.origin.source, VirSpecClauseOrigin::InferredType { .. }) != inferred
                || fact.region.is_some()
                || fact.size_bytes != shape.size_bytes()
                || fact.initialization != initialization
                || !matches!(permission.kind, ContractValueFactKind::Permission { resource: id, range: AbstractByteRange::Exact(range), .. } if id == resource && range.start() == 0 && range.end() == shape.size_bytes())
            {
                return Err(ContractDefinitionError::InvalidRange);
            }
            if inferred {
                state.value_ranges.insert(resource, ranges.clone());
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typed_value_masks_ignore_padding_but_explicit_byte_contracts_do_not() {
        let ranges = [
            ByteRange::new(0, 1).unwrap(),
            ByteRange::new(8, 24).unwrap(),
        ];
        let mut allocation = AbstractAllocation::new_local(24, 8).unwrap();
        allocation
            .forget_initialization(ByteRange::new(1, 8).unwrap())
            .unwrap();
        for range in ranges {
            allocation.mark_initialized(range).unwrap();
            allocation.mark_valid(range).unwrap();
        }
        assert_eq!(
            initialization_guarantee_status(
                &allocation,
                ContractInitialization::Initialized,
                Some(&ranges)
            ),
            ObligationStatus::Proven
        );
        assert_ne!(
            initialization_guarantee_status(&allocation, ContractInitialization::Initialized, None),
            ObligationStatus::Proven
        );
        allocation.forget_validity(ranges[0]).unwrap();
        assert_eq!(
            initialization_guarantee_status(
                &allocation,
                ContractInitialization::Initialized,
                Some(&ranges)
            ),
            ObligationStatus::Unknown
        );
        allocation.mark_uninitialized(ranges[1]).unwrap();
        assert_eq!(
            initialization_guarantee_status(
                &allocation,
                ContractInitialization::Initialized,
                Some(&ranges)
            ),
            ObligationStatus::Refuted
        );
    }

    #[test]
    fn typed_instantiation_leaves_padding_unknown_in_both_directions() {
        let clause = VirSpecClauseId::new(0);
        let ranges = [
            ByteRange::new(0, 1).unwrap(),
            ByteRange::new(8, 24).unwrap(),
        ];
        for initialization in [
            ContractInitialization::Initialized,
            ContractInitialization::Uninitialized,
        ] {
            let allocation = instantiate_allocation(
                ContractAllocationFact {
                    clause,
                    origin: ContractFactOrigin {
                        clause,
                        position: VirContractPosition::Requires,
                        source: VirSpecClauseOrigin::InferredType {
                            origin: VirOriginId::new(0),
                        },
                        source_span: ByteSpan::new(0, 1).unwrap(),
                    },
                    resource: ContractResourceId::new(0),
                    region: None,
                    size_bytes: 24,
                    alignment: 8,
                    liveness: LivenessState::Live,
                    ownership: OwnershipState::Unowned,
                    initialization,
                },
                Some(&ranges),
            )
            .unwrap();
            assert_eq!(
                initialization_guarantee_status(&allocation, initialization, Some(&ranges)),
                ObligationStatus::Proven
            );
            assert_eq!(
                allocation
                    .initialization()
                    .classify(ByteRange::new(1, 8).unwrap()),
                InitializationClass::MaybeInitialized
            );
        }
    }
}
