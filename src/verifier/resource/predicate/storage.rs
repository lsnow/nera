//! Typed storage carries the sealed token, never an available memory permission.
use super::*;

impl ResourceState {
    pub(in crate::verifier) fn predicate_carrier_to_store(
        &self,
        source: VirValueId,
        pointer: AbstractPointer,
    ) -> Option<(PredicateHolder, AbstractPermission)> {
        let mut matches = self.predicates.iter().flat_map(|(h, p)| {
            p.resources
                .iter()
                .filter(move |r| r.carrier == Some(source))
                .map(move |r| (h, p, r))
        });
        let (h, p, r) = matches.next()?;
        if matches.next().is_some()
            || !p.folded
            || !p.borrowed_by.is_empty()
            || r.storage.is_some()
            || match r.permission.authority() {
                PermissionAuthority::Owner => false,
                PermissionAuthority::Loan(id) => self.loan(id).is_none_or(|loan| {
                    loan.activity() != LoanActivity::Active || !loan.has_value_authority(source)
                }),
                PermissionAuthority::Unknown => true,
            }
            || r.pointer != pointer
            || !self.predicate_representation_valid(p)
            || self.value(source)
                != Some(&AbstractValue::Permission(
                    r.permission
                        .with_availability(PermissionAvailability::Consumed),
                ))
        {
            return None;
        }
        Some((*h, r.permission))
    }

    pub(in crate::verifier) fn store_predicate_carrier(
        &mut self,
        source: VirValueId,
        allocation: AbstractAllocationId,
        key: ResourcePayloadKey,
    ) -> bool {
        if self.predicates.values().any(|p| {
            p.resources.iter().any(|r| {
                r.storage == Some((allocation, key))
                    && (!p.dropping || !self.predicate_resource_retired(r))
            })
        }) {
            return false;
        }
        let Some(r) = self
            .predicates
            .values_mut()
            .flat_map(|p| &mut p.resources)
            .find(|r| r.carrier == Some(source))
        else {
            return false;
        };
        r.carrier = None;
        r.storage = Some((allocation, key));
        true
    }

    pub(in crate::verifier) fn take_predicate_carrier(
        &mut self,
        allocation: AbstractAllocationId,
        key: ResourcePayloadKey,
        payload: TypedResourcePayload,
        destination: VirValueId,
    ) -> Result<bool, PredicateError> {
        let state = &*self;
        let matches = state
            .predicates
            .iter()
            .flat_map(|(h, p)| {
                p.resources
                    .iter()
                    .enumerate()
                    .filter(move |(_, r)| {
                        r.storage == Some((allocation, key))
                            && (!p.dropping || !state.predicate_resource_retired(r))
                    })
                    .map(move |(i, _)| (*h, i))
            })
            .collect::<Vec<_>>();
        let [(h, i)] = matches.as_slice() else {
            return if matches.is_empty() {
                Ok(false)
            } else {
                Err(PredicateError::AliasedAuthority)
            };
        };
        let p = &self.predicates[h];
        let r = &p.resources[*i];
        if !p.folded
            || !p.borrowed_by.is_empty()
            || r.carrier.is_some()
            || match r.permission.authority() {
                PermissionAuthority::Owner => false,
                // Both the stored token and its real authority must still be
                // present. They move together only after all checks succeed.
                PermissionAuthority::Loan(id) => self.loan(id).is_none_or(|loan| {
                    loan.activity() != LoanActivity::Active
                        || !loan.authorities().contains(
                            &crate::verifier::resource::AbstractLoanAuthority::stored(
                                allocation, key,
                            ),
                        )
                }),
                PermissionAuthority::Unknown => true,
            }
            || payload.pointer() != r.pointer
            || payload.permission()
                != r.permission
                    .with_availability(PermissionAvailability::Consumed)
            || !self.predicate_representation_valid(p)
            || self.values.contains_key(&destination)
            || self
                .loans
                .values()
                .any(|loan| loan.has_value_authority(destination))
        {
            return Err(PredicateError::MissingAuthority);
        }
        if let PermissionAuthority::Loan(id) = r.permission.authority()
            && !self
                .loans
                .get_mut(&id)
                .is_some_and(|loan| loan.move_authority_from_storage(allocation, key, destination))
        {
            return Err(PredicateError::MissingAuthority);
        }
        let r = &mut self.predicates.get_mut(h).unwrap().resources[*i];
        r.storage = None;
        r.carrier = Some(destination);
        Ok(true)
    }

    /// Admit the requested fields only after checking the entire live group.
    /// Untouched fields and SSA carriers remain sealed cleanup responsibilities.
    pub(in crate::verifier) fn predicate_owner_to_drop(
        &self,
        storage: AbstractAllocationId,
        key: ResourcePayloadKey,
        payload: &TypedResourcePayload,
        scope: &BTreeSet<(AbstractAllocationId, ResourcePayloadKey)>,
    ) -> Option<(PredicateHolder, TypedResourcePayload)> {
        let matches = self
            .predicates
            .iter()
            .filter(|(_, p)| {
                p.resources.iter().any(|r| {
                    r.storage == Some((storage, key))
                        && (!p.dropping || !self.predicate_resource_retired(r))
                })
            })
            .collect::<Vec<_>>();
        let [(holder, p)] = matches.as_slice() else {
            return None;
        };
        if !scope.contains(&(storage, key)) || !self.predicate_drop_ready(p) {
            return None;
        }
        let mut locations = BTreeSet::new();
        for r in &p.resources {
            if p.dropping && self.predicate_resource_retired(r) {
                continue;
            }
            let location = match (r.carrier, r.storage) {
                (Some(carrier), None) => AbstractLoanAuthority::value(carrier),
                (None, Some((storage, key))) => AbstractLoanAuthority::stored(storage, key),
                _ => return None,
            };
            if r.permission.authority() != PermissionAuthority::Owner
                || !locations.insert(location)
                || self.loans.values().any(|l| {
                    l.activity() != LoanActivity::Ended
                        && (l.provenance() == r.pointer.provenance()
                            || l.provenance() == AbstractProvenance::Unknown)
                })
            {
                return None;
            }
        }
        let r = p
            .resources
            .iter()
            .find(|r| r.storage == Some((storage, key)))?;
        if payload.pointer() != r.pointer
            || payload.permission()
                != r.permission
                    .with_availability(PermissionAvailability::Consumed)
        {
            return None;
        }
        Some((**holder, TypedResourcePayload::new(r.pointer, r.permission)))
    }

    /// Borrowed members use the same staged destruction protocol as owners.
    /// No loan ends during admission and no parent predicate is restored early.
    pub(in crate::verifier) fn predicate_borrowed_to_drop(
        &self,
        storage: AbstractAllocationId,
        key: ResourcePayloadKey,
        payload: &TypedResourcePayload,
        scope: &BTreeSet<(AbstractAllocationId, ResourcePayloadKey)>,
    ) -> Option<PredicateHolder> {
        let mut matches = self.predicates.iter().filter(|(_, p)| {
            p.resources.iter().any(|r| {
                r.storage == Some((storage, key))
                    && (!p.dropping || !self.predicate_resource_retired(r))
            })
        });
        let (holder, instance) = matches.next()?;
        if matches.next().is_some()
            || !scope.contains(&(storage, key))
            || !self.predicate_drop_ready(instance)
        {
            return None;
        }
        if !self.predicate_borrow_carriers_valid(instance) {
            return None;
        }
        let r = instance
            .resources
            .iter()
            .find(|r| r.storage == Some((storage, key)))?;
        if payload.pointer() != r.pointer
            || payload.permission()
                != r.permission
                    .with_availability(PermissionAvailability::Consumed)
        {
            return None;
        }
        Some(*holder)
    }

    pub(in crate::verifier) fn move_stored_predicate_carrier(
        &mut self,
        source: AbstractAllocationId,
        source_key: ResourcePayloadKey,
        destination: AbstractAllocationId,
        destination_key: ResourcePayloadKey,
    ) {
        // Retired responsibilities remember their former slot. Only the real
        // pending carrier moves; a replacement may have its own sealed group.
        let pending = self
            .predicates
            .iter()
            .flat_map(|(holder, group)| {
                group
                    .resources
                    .iter()
                    .enumerate()
                    .filter(|(_, r)| {
                        r.storage == Some((source, source_key))
                            && (!group.dropping || !self.predicate_resource_retired(r))
                    })
                    .map(move |(index, _)| (*holder, index))
            })
            .collect::<Vec<_>>();
        for (holder, index) in pending {
            self.predicates.get_mut(&holder).unwrap().resources[index].storage =
                Some((destination, destination_key));
        }
    }
}

impl ResourceState {
    /// Atomic adapter between typed aggregate payloads and existing predicate
    /// transfer rules. Scratch SSA values never escape into a summary or CFG.
    #[cfg(test)]
    pub(in crate::verifier) fn predicate_storage_interface(
        &mut self,
        definition: &PredicateDefinition,
        roots: &[PredicateBinding],
        projections: &[Option<(u64, crate::VirMemoryAccess)>],
        import: Option<(PredicateHolder, bool)>,
    ) -> Result<(), PredicateError> {
        self.predicate_storage_interface_with_arguments(
            definition,
            roots,
            projections,
            import,
            &Default::default(),
        )
    }

    pub(in crate::verifier) fn predicate_storage_interface_with_arguments(
        &mut self,
        definition: &PredicateDefinition,
        roots: &[PredicateBinding],
        projections: &[Option<(u64, crate::VirMemoryAccess)>],
        import: Option<(PredicateHolder, bool)>,
        arguments: &crate::predicate_logic::WitnessArguments<VirMemoryAccess, VirValueId>,
    ) -> Result<(), PredicateError> {
        if roots.len() != projections.len() {
            return Err(PredicateError::InvalidBinding);
        }
        let mut next = self.clone();
        let mut bindings = Vec::new();
        let mut stored = Vec::new();
        let mut fresh = next
            .values
            .keys()
            .map(|v| v.get())
            .chain(next.loans.values().flat_map(|loan| {
                loan.authorities()
                    .iter()
                    .filter_map(|authority| match authority {
                        crate::verifier::resource::AbstractLoanAuthority::Value(value) => {
                            Some(value.get())
                        }
                        crate::verifier::resource::AbstractLoanAuthority::Stored { .. } => None,
                    })
            }))
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(PredicateError::Budget)?;
        let mut locations = BTreeSet::new();
        for (root, projection) in roots.iter().zip(projections) {
            let Some((offset, access)) = projection else {
                bindings.push(*root);
                continue;
            };
            let Some(AbstractValue::Pointer(pointer)) = next.value(root.pointer).copied() else {
                return Err(PredicateError::InvalidBinding);
            };
            let Some(AbstractValue::Permission(permission)) = next.value(root.permission).copied()
            else {
                return Err(PredicateError::MissingAuthority);
            };
            let AbstractProvenance::Known(storage) = pointer.provenance() else {
                return Err(PredicateError::InvalidBinding);
            };
            let offset = pointer
                .offset_bytes()
                .exact_value()
                .and_then(|base| base.checked_add(*offset))
                .ok_or(PredicateError::InvalidBinding)?;
            let bytes = ByteRange::from_start_and_length(offset, 8)
                .map_err(|_| PredicateError::InvalidBinding)?;
            if permission.availability() != PermissionAvailability::Available
                || permission.access() != AccessPermission::Write
                || permission.provenance() != pointer.provenance()
                || !matches!(permission.range(),AbstractByteRange::Exact(range) if range.contains(bytes))
            {
                return Err(PredicateError::MissingAuthority);
            }
            let key = ResourcePayloadKey::new(offset, *access);
            if !locations.insert((storage, key)) {
                return Err(PredicateError::AliasedAuthority);
            }
            let allocation = next
                .allocation(storage)
                .ok_or(PredicateError::MissingAuthority)?;
            if allocation.liveness() != LivenessState::Live {
                return Err(PredicateError::MissingAuthority);
            }
            let MovePathState::Available(payload) = allocation.resource_payload(key) else {
                return Err(PredicateError::MissingAuthority);
            };
            let payload = *payload;
            let binding = PredicateBinding {
                pointer: VirValueId::new(fresh),
                permission: VirValueId::new(fresh.checked_add(1).ok_or(PredicateError::Budget)?),
            };
            fresh = fresh.checked_add(2).ok_or(PredicateError::Budget)?;
            if import.is_none()
                && !next.take_predicate_carrier(storage, key, payload, binding.permission)?
            {
                return Err(PredicateError::MissingHolder);
            }
            // Import starts from an ordinary ABI payload, whereas export's
            // sealed carrier was moved by take_predicate_carrier above. In
            // both cases the actual loan authority must follow the scratch
            // permission; predicate metadata alone cannot authorize access.
            if import.is_some()
                && let PermissionAuthority::Loan(id) = payload.permission().authority()
                && !next.loans.get_mut(&id).is_some_and(|loan| {
                    loan.activity() == LoanActivity::Active
                        && loan.move_authority_from_storage(storage, key, binding.permission)
                })
            {
                return Err(PredicateError::MissingAuthority);
            }
            next.values
                .insert(binding.pointer, AbstractValue::Pointer(payload.pointer()));
            next.values.insert(
                binding.permission,
                AbstractValue::Permission(payload.permission()),
            );
            next.allocation_mut(storage)
                .unwrap()
                .set_resource_payload(key, MovePathState::Moved)
                .map_err(|_| PredicateError::InvalidBinding)?;
            if import.is_some_and(|(_, entry)| entry) {
                let AbstractProvenance::Known(id) = payload.pointer().provenance() else {
                    return Err(PredicateError::InvalidBinding);
                };
                let allocation = next
                    .allocation_mut(id)
                    .ok_or(PredicateError::MissingAuthority)?;
                let whole = ByteRange::new(0, allocation.size_bytes())
                    .map_err(|_| PredicateError::InvalidBinding)?;
                allocation
                    .forget_initialization(whole)
                    .map_err(|_| PredicateError::InvalidBinding)?;
            }
            stored.push((storage, key, binding));
            bindings.push(binding);
        }
        if let Some((holder, entry)) = import {
            next.import_predicate_interface_with_arguments(
                definition, &bindings, holder, arguments, entry,
            )?;
        } else {
            let holder = next.carried_predicate_holder(definition, &bindings)?;
            next.check_predicate_arguments(definition, holder, arguments)?;
            next.export_predicate_interface(definition, &bindings)?;
        }
        for (storage, key, binding) in stored {
            if import.is_some() && !next.store_predicate_carrier(binding.permission, storage, key) {
                return Err(PredicateError::MissingAuthority);
            }
            let Some(AbstractValue::Pointer(pointer)) = next.values.remove(&binding.pointer) else {
                return Err(PredicateError::InvalidBinding);
            };
            let Some(AbstractValue::Permission(permission)) =
                next.values.remove(&binding.permission)
            else {
                return Err(PredicateError::InvalidBinding);
            };
            // Do not leave a loan pointing at an SSA value that is about to
            // disappear. The adapter restores the original storage location
            // even when export has removed the sealed predicate instance.
            if let PermissionAuthority::Loan(id) = permission.authority()
                && !next.loans.get_mut(&id).is_some_and(|loan| {
                    loan.activity() == LoanActivity::Active
                        && loan.move_authority_to_storage(binding.permission, storage, key)
                })
            {
                return Err(PredicateError::MissingAuthority);
            }
            next.allocation_mut(storage)
                .unwrap()
                .set_resource_payload(
                    key,
                    MovePathState::available(TypedResourcePayload::new(pointer, permission)),
                )
                .map_err(|_| PredicateError::InvalidBinding)?;
        }
        *self = next;
        Ok(())
    }
}

impl ResourceState {
    /// Bind postcondition entry values and positions in a disposable view.
    /// Old fields use entry contents; current fields use an entry pointer with
    /// current contents and current authority. No permission is restored.
    /// All scratch IDs and their aliases are removed before committing.
    pub(in crate::verifier) fn with_predicate_input_snapshots(
        &mut self,
        entry: &ResourceState,
        inputs: &[VirValueId],
        arguments: &crate::predicate_logic::WitnessArguments<VirMemoryAccess, u32>,
        apply: impl FnOnce(
            &mut Self,
            &[VirValueId],
            &crate::predicate_logic::WitnessArguments<VirMemoryAccess, u32>,
        ) -> Result<(), PredicateError>,
    ) -> Result<(), PredicateError> {
        use crate::predicate_logic::{LogicType, MAX_LOGIC_PARAMETERS, WitnessInput};
        if arguments.inputs.len() > MAX_LOGIC_PARAMETERS || !arguments.values.is_empty() {
            return Err(PredicateError::InvalidBinding);
        }
        let mut next = self.clone();
        let mut bound = inputs.to_vec();
        let mut scratch = BTreeMap::new();
        let mut fresh = next
            .values
            .keys()
            .chain(entry.values.keys())
            .chain(next.word_origins.keys())
            .chain(next.bool_origins.keys())
            .chain(next.word_expressions.keys())
            .map(|id| id.get())
            .chain(next.loans.values().flat_map(|loan| {
                loan.authorities().iter().filter_map(|authority| {
                    if let crate::verifier::resource::AbstractLoanAuthority::Value(id) = authority {
                        Some(id.get())
                    } else {
                        None
                    }
                })
            }))
            .max()
            .unwrap_or(0);
        let mut normalized = arguments.clone();
        for (ty, input) in &mut normalized.inputs {
            let pointer_slot = match input {
                WitnessInput::ResultField { base, .. }
                | WitnessInput::Memory {
                    base,
                    time: crate::predicate_logic::ObservationTime::Current,
                    ..
                } => Some(*base),
                _ => None,
            };
            if let Some(slot) = pointer_slot {
                if scratch.contains_key(&slot) {
                    continue;
                }
                let original = *inputs
                    .get(slot as usize)
                    .ok_or(PredicateError::InvalidBinding)?;
                let Some(value @ AbstractValue::Pointer(_)) = entry.value(original).copied() else {
                    return Err(PredicateError::InvalidBinding);
                };
                fresh = fresh.checked_add(1).ok_or(PredicateError::Budget)?;
                let id = VirValueId::new(fresh);
                next.values.insert(id, value);
                bound[slot as usize] = id;
                scratch.insert(slot, id);
                continue;
            }
            if let WitnessInput::Memory {
                base,
                offset,
                access,
                time,
            } = *input
            {
                if time == crate::predicate_logic::ObservationTime::Current {
                    continue;
                }
                let pointer = *inputs
                    .get(base as usize)
                    .ok_or(PredicateError::InvalidBinding)?;
                let (value, word_origin, bool_origin) =
                    entry.predicate_memory_snapshot(*ty, pointer, offset, access)?;
                fresh = fresh.checked_add(1).ok_or(PredicateError::Budget)?;
                let id = VirValueId::new(fresh);
                next.values.insert(id, value);
                if let Some(origin) = word_origin {
                    next.set_word_origin(id, origin);
                }
                if let Some(origin) = bool_origin {
                    next.set_bool_origin(id, origin);
                }
                let slot = u32::try_from(bound.len()).map_err(|_| PredicateError::Budget)?;
                bound.push(id);
                scratch.insert(slot, id);
                *input = WitnessInput::Scalar(slot);
                continue;
            }
            if matches!(
                input,
                WitnessInput::Result(_) | WitnessInput::ResultField { .. }
            ) {
                continue;
            }
            let WitnessInput::Scalar(slot) = input else {
                return Err(PredicateError::InvalidBinding);
            };
            let original = *inputs
                .get(*slot as usize)
                .ok_or(PredicateError::InvalidBinding)?;
            let value = *entry
                .value(original)
                .ok_or(PredicateError::InvalidBinding)?;
            if !matches!(
                (ty, value),
                (LogicType::U64 | LogicType::Usize, AbstractValue::U64(_))
                    | (LogicType::Bool, AbstractValue::Bool(_))
            ) {
                return Err(PredicateError::InvalidBinding);
            }
            if scratch.contains_key(slot) {
                continue;
            }
            fresh = fresh.checked_add(1).ok_or(PredicateError::Budget)?;
            let id = VirValueId::new(fresh);
            next.values.insert(id, value);
            if let Some(origin) = entry.word_origin(original) {
                next.set_word_origin(id, origin);
            }
            if let Some(origin) = entry.bool_origin(original) {
                next.set_bool_origin(id, origin);
            }
            bound[*slot as usize] = id;
            scratch.insert(*slot, id);
        }
        apply(&mut next, &bound, &normalized)?;
        for id in scratch.into_values() {
            next.forget_predicate_local_alias(id);
            for allocation in next.allocations.values_mut() {
                allocation.initialization_prefixes.forget_value(id);
            }
            next.values.remove(&id);
            next.word_origins.remove(&id);
            next.bool_origins.remove(&id);
            next.word_expressions.remove(&id);
        }
        *self = next;
        Ok(())
    }
}
