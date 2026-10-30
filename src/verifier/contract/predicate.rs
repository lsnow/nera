//! Finite predicate ownership at checked owner ABI boundaries.
use super::*;
use crate::verifier::{PredicateBinding, PredicateDefinition, PredicateError, PredicateHolder};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::verifier) struct Interface {
    pub definition: PredicateDefinition,
    pub metadata: crate::VirPredicateInterface,
    pub projections: Vec<Option<(u64, crate::VirMemoryAccess)>>,
}

impl Interface {
    fn arguments(
        &self,
        values: &[VirValueId],
        results: &[VirValueId],
    ) -> Result<
        crate::predicate_logic::WitnessArguments<crate::VirMemoryAccess, VirValueId>,
        PredicateError,
    > {
        let args = &self.metadata.arguments;
        if !args.values.is_empty() {
            return Err(PredicateError::InvalidBinding);
        }
        Ok(crate::predicate_logic::WitnessArguments {
            values: vec![],
            arguments: args.arguments.clone(),
            inputs: args
                .inputs
                .iter()
                .map(|(ty, input)| {
                    if let crate::predicate_logic::WitnessInput::Memory {
                        base,
                        offset,
                        access,
                        time,
                    } = input
                    {
                        return Ok((
                            *ty,
                            crate::predicate_logic::WitnessInput::Memory {
                                base: *values
                                    .get(*base as usize)
                                    .ok_or(PredicateError::InvalidBinding)?,
                                offset: *offset,
                                access: *access,
                                time: *time,
                            },
                        ));
                    }
                    if let crate::predicate_logic::WitnessInput::ResultField {
                        base,
                        offset,
                        access,
                    } = input
                    {
                        if !self.metadata.ensures {
                            return Err(PredicateError::InvalidBinding);
                        }
                        return Ok((
                            *ty,
                            crate::predicate_logic::WitnessInput::ResultField {
                                base: *values
                                    .get(*base as usize)
                                    .ok_or(PredicateError::InvalidBinding)?,
                                offset: *offset,
                                access: *access,
                            },
                        ));
                    }
                    let (slot, values) = match input {
                        crate::predicate_logic::WitnessInput::Scalar(slot) => (slot, values),
                        crate::predicate_logic::WitnessInput::Result(slot)
                            if self.metadata.ensures =>
                        {
                            (slot, results)
                        }
                        _ => return Err(PredicateError::InvalidBinding),
                    };
                    Ok((
                        *ty,
                        crate::predicate_logic::WitnessInput::Scalar(
                            *values
                                .get(*slot as usize)
                                .ok_or(PredicateError::InvalidBinding)?,
                        ),
                    ))
                })
                .collect::<Result<_, _>>()?,
        })
    }
    fn bindings(
        &self,
        values: &[VirValueId],
        inputs: &[VirValueId],
    ) -> Result<Vec<PredicateBinding>, PredicateError> {
        self.metadata
            .bindings
            .iter()
            .zip(&self.projections)
            .map(|((p, q), projection)| {
                Ok(PredicateBinding {
                    pointer: *(if self.metadata.in_place
                        || (self.metadata.ensures && projection.is_some())
                    {
                        inputs
                    } else {
                        values
                    })
                    .get(*p as usize)
                    .ok_or(PredicateError::InvalidBinding)?,
                    permission: *values
                        .get(*q as usize)
                        .ok_or(PredicateError::InvalidBinding)?,
                })
            })
            .collect()
    }
    pub fn projected_allocations(
        &self,
        state: &ResourceState,
        values: &[VirValueId],
        inputs: &[VirValueId],
    ) -> Vec<AbstractAllocationId> {
        self.metadata
            .bindings
            .iter()
            .zip(&self.projections)
            .filter_map(|((p, _), projection)| {
                let (offset, access) = (*projection)?;
                let AbstractValue::Pointer(pointer) = state.value(
                    *(if self.metadata.ensures {
                        inputs
                    } else {
                        values
                    })
                    .get(*p as usize)?,
                )?
                else {
                    return None;
                };
                let AbstractProvenance::Known(storage) = pointer.provenance() else {
                    return None;
                };
                let key = super::super::ResourcePayloadKey::new(
                    pointer.offset_bytes().exact_value()?.checked_add(offset)?,
                    access,
                );
                let super::super::MovePathState::Available(payload) =
                    state.allocation(storage)?.resource_payload(key)
                else {
                    return None;
                };
                let AbstractProvenance::Known(id) = payload.pointer().provenance() else {
                    return None;
                };
                Some(id)
            })
            .collect()
    }

    pub fn export(
        &self,
        state: &mut ResourceState,
        values: &[VirValueId],
        inputs: &[VirValueId],
    ) -> Result<(), PredicateError> {
        // Atomic even when a later resource or pointer comparison fails.
        let mut next = state.clone();
        next.predicate_storage_interface_with_arguments(
            &self.definition,
            &self.bindings(values, inputs)?,
            &self.projections,
            None,
            &self.arguments(
                if self.metadata.ensures {
                    inputs
                } else {
                    values
                },
                if self.metadata.ensures { values } else { &[] },
            )?,
        )?;
        *state = next;
        Ok(())
    }
    pub fn export_post(
        &self,
        state: &mut ResourceState,
        results: &[VirValueId],
        inputs: &[VirValueId],
        abi: &crate::VirAbiSignature,
        entry: &ResourceState,
    ) -> Result<(), PredicateError> {
        state.with_predicate_input_snapshots(
            entry,
            inputs,
            &self.metadata.arguments,
            |state, inputs, arguments| {
                let mut interface = self.clone();
                interface.metadata.arguments = arguments.clone();
                interface.export_post_with_inputs(state, results, inputs, abi)
            },
        )
    }

    fn export_post_with_inputs(
        &self,
        state: &mut ResourceState,
        results: &[VirValueId],
        inputs: &[VirValueId],
        abi: &crate::VirAbiSignature,
    ) -> Result<(), PredicateError> {
        if !self.metadata.in_place {
            return self.export(state, results, inputs);
        }
        let parameters = self
            .metadata
            .bindings
            .iter()
            .map(|(pointer, permission)| {
                let parameter = abi
                    .parameters()
                    .iter()
                    .position(|binding| {
                        binding.parameter_slots().first() == Some(pointer)
                            && binding.result_slots() == [*permission]
                    })
                    .ok_or(PredicateError::InvalidBinding)?;
                Ok((
                    crate::vir::interface_loan_id(parameter as u32),
                    *results
                        .get(*permission as usize)
                        .ok_or(PredicateError::InvalidBinding)?,
                ))
            })
            .collect::<Result<Vec<_>, PredicateError>>()?;
        let mut next = state.clone();
        next.export_predicate_parameters_with_arguments(
            &self.definition,
            &parameters,
            &self.arguments(inputs, results)?,
        )?;
        *state = next;
        Ok(())
    }

    pub fn import_post(
        &self,
        state: &mut ResourceState,
        results: &[VirValueId],
        inputs: &[VirValueId],
        entry: &ResourceState,
    ) -> Result<(), PredicateError> {
        state.with_predicate_input_snapshots(
            entry,
            inputs,
            &self.metadata.arguments,
            |state, inputs, arguments| {
                let mut interface = self.clone();
                interface.metadata.arguments = arguments.clone();
                interface.import(state, results, false, inputs)
            },
        )
    }

    pub fn import(
        &self,
        state: &mut ResourceState,
        values: &[VirValueId],
        entry: bool,
        inputs: &[VirValueId],
    ) -> Result<(), PredicateError> {
        let holder = if entry {
            PredicateHolder(self.metadata.holder)
        } else {
            state.available_predicate_holder()?
        };
        state.predicate_storage_interface_with_arguments(
            &self.definition,
            &self.bindings(values, inputs)?,
            &self.projections,
            Some((holder, entry)),
            &self.arguments(
                if self.metadata.ensures {
                    inputs
                } else {
                    values
                },
                if self.metadata.ensures { values } else { &[] },
            )?,
        )
    }
}

impl InstantiatedContract {
    pub(in crate::verifier) fn install_predicate_entry(
        &self,
        state: &mut ResourceState,
        parameters: &[VirValueId],
    ) -> Result<(), (crate::VirPredicateId, PredicateError)> {
        for interface in self.predicates.iter().filter(|i| !i.metadata.ensures) {
            interface
                .import(state, parameters, true, &[])
                .map_err(|error| (interface.definition.id(), error))?;
        }
        Ok(())
    }
    /// Summary inputs describe the existing owner ABI. The call adapter separately
    /// checks and consumes each closed predicate before it can use this view.
    pub(in crate::verifier) fn predicate_entry_abi_view(
        &self,
        state: &ResourceState,
        parameters: &[VirValueId],
    ) -> Result<ResourceState, PredicateError> {
        let mut result = state.clone();
        for interface in self.predicates.iter().filter(|i| !i.metadata.ensures) {
            interface.export(&mut result, parameters, &[])?;
        }
        Ok(result)
    }
}
