//! The sole call transfer: contract application, ABI resource mapping and restoration.
//! No body traversal or interprocedural scheduling belongs in instruction transfer.
use super::{
    AbstractAllocation, AbstractAllocationId, AbstractByteRange, AbstractLoan, AbstractPermission,
    AbstractPointer, AbstractProvenance, AbstractValue, AccessPermission, BTreeMap, BTreeSet,
    ByteRange, ContractApplicationError, FreeCapability, GuaranteedAlignment, InitializationClass,
    InitializationRequirement, InstantiatedContracts, LoanAccess, LoanActivity, MovePathState,
    ObligationStatus, PermissionAuthority, RelationComparison, RelationTerm,
    ResourceObligationKind, ResourcePayloadKey, ResourceState, TransferBuilder, TransferError,
    TypedResourcePayload, U64Interval, VirCallTarget, VirLoanKind, VirMemoryAccess,
    VirMemorySchema, VirPointerKind, VirRegionId, VirType, VirValue, VirValueId,
    abstract_value_type, active_object_mask, apply_postconditions, check_preconditions,
    combine_statuses, ensure_fact_type, exact_abstract_range, loan_authority_access_status,
    mark_permission_consumed, memory_access_status, movable_object_status,
    object_drop_payload_status, owned_resource_pointee, owner_authority_status,
    permission_availability_status, permission_fact, pointer_fact, subtract_intervals,
    unknown_value, word, word_expression,
};

#[derive(Clone, Copy)]
pub(in crate::verifier) struct ContractTransferContext<'environment> {
    pub(in crate::verifier) contracts: &'environment InstantiatedContracts,
    pub(in crate::verifier) call_site: u64,
    pub(in crate::verifier) summary:
        Option<crate::verifier::summary::SummaryTransferContext<'environment>>,
}

impl TransferBuilder<'_> {
    pub(super) fn call(
        &mut self,
        results: &[VirValue],
        target: &VirCallTarget,
        arguments: &[VirValueId],
    ) -> Result<(), TransferError> {
        let before = self.state.clone();
        if arguments.len() != target.signature.parameters.len()
            || results.len() != target.signature.results.len()
        {
            return Err(TransferError::InvalidValidatedCallShape {
                arguments: arguments.len(),
                parameters: target.signature.parameters.len(),
                results: results.len(),
                expected_results: target.signature.results.len(),
            });
        }

        let contract = self
            .contract_context
            .and_then(|context| context.contracts.get(target.contract));
        let contract_matches =
            contract.is_some_and(|contract| contract.signature() == &target.signature);
        self.require(
            ResourceObligationKind::CallContractAvailable {
                contract: target.contract,
            },
            if contract_matches {
                ObligationStatus::Proven
            } else if contract.is_some() {
                ObligationStatus::Refuted
            } else {
                ObligationStatus::Unknown
            },
        );

        let instantiation = if contract_matches {
            let (mapping, checks) = check_preconditions(
                &self.state,
                arguments,
                contract.expect("matching contract exists"),
            );
            for check in checks {
                self.require(
                    ResourceObligationKind::CallContractPrecondition {
                        contract: target.contract,
                        clause: check.clause,
                        fact_origin: check.origin,
                    },
                    check.status,
                );
            }
            Some(mapping)
        } else {
            None
        };

        let mut abi_permission_restorations = BTreeMap::new();
        let mut abi_word_restorations = BTreeMap::new();
        let mut borrowed_permission_slots = BTreeSet::new();
        let mut borrowed_authority_results = Vec::new();
        let mut moved_permission_slots = BTreeSet::new();
        let mut aggregate_payload_allocations = BTreeSet::new();
        if let Some(abi) = &target.abi {
            self.require_borrow_projection_range(abi, arguments)?;
            for (parameter_index, binding) in abi.parameters().iter().enumerate() {
                if binding.interface().transfer.is_borrow() {
                    let permission_slot = *binding
                        .parameter_slots()
                        .last()
                        .ok_or(TransferError::InvalidDerivedRange)?
                        as usize;
                    let argument = arguments[permission_slot];
                    let permission = permission_fact(&self.state, argument)?;
                    let safe_interface =
                        matches!(binding.value(), crate::VirAbiValue::Pointer { .. })
                            || contract.is_some_and(|contract| {
                                contract.borrow_parameters.contains(&parameter_index)
                            });
                    if safe_interface
                        && !matches!(permission.authority(), PermissionAuthority::Loan(_))
                    {
                        self.require(
                            ResourceObligationKind::LoanCompatible {
                                loan: None,
                                permission: argument,
                                access: exact_abstract_range(permission.range()),
                                required: if binding.interface().transfer
                                    == crate::VirInterfaceTransfer::BorrowShared
                                {
                                    AccessPermission::Read
                                } else {
                                    AccessPermission::Write
                                },
                            },
                            if permission.authority() == PermissionAuthority::Owner {
                                ObligationStatus::Refuted
                            } else {
                                ObligationStatus::Unknown
                            },
                        );
                    }
                    if let PermissionAuthority::Loan(loan_id) = permission.authority() {
                        self.require(
                            ResourceObligationKind::CallContractAvailable {
                                contract: target.contract,
                            },
                            if contract.is_some_and(|contract| {
                                contract.borrow_parameters.contains(&parameter_index)
                            }) {
                                ObligationStatus::Proven
                            } else {
                                ObligationStatus::Unknown
                            },
                        );
                        borrowed_permission_slots.insert(permission_slot);
                        let pointer_id = arguments[binding.parameter_slots()[0] as usize];
                        let pointer = pointer_fact(&self.state, pointer_id)?;
                        let required = if binding.interface().transfer
                            == crate::VirInterfaceTransfer::BorrowShared
                        {
                            AccessPermission::Read
                        } else {
                            AccessPermission::Write
                        };
                        let range = permission.range().bounds().and_then(|(start, end)| {
                            ByteRange::new(start.interval().lower(), end.interval().upper()).ok()
                        });
                        self.require(
                            ResourceObligationKind::LoanCompatible {
                                loan: Some(loan_id),
                                permission: argument,
                                access: range,
                                required,
                            },
                            combine_statuses([
                                loan_authority_access_status(
                                    &self.state,
                                    loan_id,
                                    argument,
                                    LoanAccess {
                                        pointer,
                                        envelope: range,
                                        range: permission.range(),
                                        required,
                                    },
                                    self.relation_limits,
                                    &self.relations,
                                ),
                                if self.state.loan(loan_id).is_some_and(|loan| {
                                    (loan.kind() == VirLoanKind::Shared)
                                        == (binding.interface().transfer
                                            == crate::VirInterfaceTransfer::BorrowShared)
                                }) {
                                    ObligationStatus::Proven
                                } else {
                                    ObligationStatus::Refuted
                                },
                            ]),
                        );
                        if let crate::VirAbiValue::Pointer { pointee, .. } = binding.value() {
                            let object =
                                self.object_access_facts(pointer_id, argument, *pointee, required)?;
                            let mask = active_object_mask(&object);
                            self.require_object_initialization(
                                &object,
                                &mask.possible_value_bytes,
                                InitializationRequirement::Initialized,
                            );
                            self.require_object_validity(&object, &mask.possible_value_bytes);
                        }
                        if let crate::VirAbiValue::Slice { element, .. } = binding.value() {
                            self.require_slice_argument(
                                pointer_id,
                                argument,
                                arguments[binding.parameter_slots()[1] as usize],
                                *element,
                            )?;
                        }
                        let mut permission_results = binding.result_slots().to_vec();
                        if abi.borrow_result_parameter() == Some(parameter_index) {
                            if binding.interface().transfer
                                == crate::VirInterfaceTransfer::BorrowShared
                            {
                                let limits = self
                                    .loan_context
                                    .ok_or(TransferError::MissingLoanTransferContext)?
                                    .limits;
                                if !self.require_alias_budget(loan_id, limits).is_proven()
                                    && let Some(loan) = self.state.loan_mut(loan_id)
                                {
                                    loan.set_activity(LoanActivity::MaybeActive);
                                }
                            }
                            let result_binding = &abi.results()[0];
                            for (slot, input_slot) in result_binding
                                .result_slots()
                                .iter()
                                .zip(binding.parameter_slots())
                            {
                                if abi.borrow_result().is_some_and(|relation| {
                                    relation.projection != crate::BorrowProjection::Whole
                                }) && target.signature.results.get(*slot as usize)
                                    != Some(&VirType::Permission)
                                {
                                    continue;
                                }
                                abi_permission_restorations.insert(
                                    *slot as usize,
                                    *self
                                        .state
                                        .value(arguments[*input_slot as usize])
                                        .ok_or(TransferError::InvalidDerivedRange)?,
                                );
                                let input = arguments[*input_slot as usize];
                                if let Some(AbstractValue::U64(value)) = self.state.value(input)
                                    && let Some(expression) =
                                        word_expression(&self.state, input, *value)
                                {
                                    abi_word_restorations.insert(*slot as usize, expression);
                                }
                            }
                            permission_results.push(
                                *result_binding
                                    .result_slots()
                                    .last()
                                    .ok_or(TransferError::InvalidDerivedRange)?,
                            );
                        }
                        for slot in &permission_results {
                            abi_permission_restorations
                                .insert(*slot as usize, AbstractValue::Permission(permission));
                        }
                        borrowed_authority_results.push((loan_id, argument, permission_results));
                        continue;
                    }
                }
                if binding.interface().transfer == crate::VirInterfaceTransfer::Move {
                    moved_permission_slots.extend(
                        binding
                            .parameter_slots()
                            .iter()
                            .copied()
                            .filter(|slot| {
                                target.signature.parameters.get(*slot as usize)
                                    == Some(&VirType::Permission)
                            })
                            .map(|slot| slot as usize),
                    );
                }
                if binding.interface().transfer == crate::VirInterfaceTransfer::Move
                    && let crate::VirAbiValue::IndirectAggregate { access } = binding.value()
                {
                    let [pointer_slot, permission_slot] = binding.parameter_slots() else {
                        return Err(TransferError::InvalidValidatedCallShape {
                            arguments: arguments.len(),
                            parameters: target.signature.parameters.len(),
                            results: results.len(),
                            expected_results: target.signature.results.len(),
                        });
                    };
                    let pointer = *arguments.get(*pointer_slot as usize).ok_or(
                        TransferError::InvalidValidatedCallShape {
                            arguments: arguments.len(),
                            parameters: target.signature.parameters.len(),
                            results: results.len(),
                            expected_results: target.signature.results.len(),
                        },
                    )?;
                    let permission = *arguments.get(*permission_slot as usize).ok_or(
                        TransferError::InvalidValidatedCallShape {
                            arguments: arguments.len(),
                            parameters: target.signature.parameters.len(),
                            results: results.len(),
                            expected_results: target.signature.results.len(),
                        },
                    )?;
                    let object = self.object_access_facts(
                        pointer,
                        permission,
                        *access,
                        AccessPermission::Write,
                    )?;
                    let mask = active_object_mask(&object);
                    self.require(
                        ResourceObligationKind::ObjectMoveSupported { access: *access },
                        movable_object_status(self.memory, &object.shape),
                    );
                    self.require_active_variants(&object, &mask);
                    self.require_object_initialization(
                        &object,
                        &mask.possible_value_bytes,
                        InitializationRequirement::Initialized,
                    );
                    self.require_object_validity(&object, &mask.possible_value_bytes);
                    self.require_object_resource_payloads(&object, &mask);
                    for leaf in &mask.guaranteed_resource_leaves {
                        let payload = object
                            .allocation
                            .as_ref()
                            .zip(object.pointer.offset_bytes().exact_value())
                            .and_then(|(allocation, base)| {
                                base.checked_add(leaf.bytes().start_bytes()).map(|offset| {
                                    allocation.resource_payload(ResourcePayloadKey::new(
                                        offset,
                                        leaf.access(),
                                    ))
                                })
                            });
                        let offset = object
                            .pointer
                            .offset_bytes()
                            .exact_value()
                            .and_then(|base| base.checked_add(leaf.bytes().start_bytes()));
                        self.require(
                            ResourceObligationKind::AggregateAbiPayloadValid {
                                allocation: object.allocation_id,
                                offset_bytes: offset,
                                access: leaf.access(),
                            },
                            match payload.as_ref() {
                                Some(MovePathState::Available(payload)) => {
                                    aggregate_abi_payload_status(
                                        &self.state,
                                        self.memory,
                                        leaf.access(),
                                        payload,
                                    )
                                }
                                Some(MovePathState::Moved) => ObligationStatus::Refuted,
                                Some(MovePathState::Unknown) | None => ObligationStatus::Unknown,
                            },
                        );
                        if let Some(MovePathState::Available(payload)) = payload
                            && let AbstractProvenance::Known(allocation) =
                                payload.pointer().provenance()
                        {
                            aggregate_payload_allocations.insert(allocation);
                        }
                    }
                }
                if matches!(
                    binding.interface().transfer,
                    crate::VirInterfaceTransfer::BorrowShared
                        | crate::VirInterfaceTransfer::BorrowMutable
                ) && matches!(binding.value(), crate::VirAbiValue::Slice { .. })
                {
                    let [_pointer_slot, _length_slot, permission_slot] = binding.parameter_slots()
                    else {
                        return Err(TransferError::InvalidValidatedCallShape {
                            arguments: arguments.len(),
                            parameters: target.signature.parameters.len(),
                            results: results.len(),
                            expected_results: target.signature.results.len(),
                        });
                    };
                    let [result_slot] = binding.result_slots() else {
                        return Err(TransferError::InvalidValidatedCallShape {
                            arguments: arguments.len(),
                            parameters: target.signature.parameters.len(),
                            results: results.len(),
                            expected_results: target.signature.results.len(),
                        });
                    };
                    let argument = arguments.get(*permission_slot as usize).ok_or(
                        TransferError::InvalidValidatedCallShape {
                            arguments: arguments.len(),
                            parameters: target.signature.parameters.len(),
                            results: results.len(),
                            expected_results: target.signature.results.len(),
                        },
                    )?;
                    let value = AbstractValue::Permission(permission_fact(&self.state, *argument)?);
                    abi_permission_restorations.insert(*result_slot as usize, value);
                }
            }
        }

        let mut permission_arguments = Vec::new();
        let mut transferred_allocations = BTreeSet::new();
        for (index, (&argument, &expected)) in arguments
            .iter()
            .zip(&target.signature.parameters)
            .enumerate()
        {
            ensure_fact_type(&self.state, argument, expected)?;
            if matches!(expected, VirType::Permission) {
                let permission = permission_fact(&self.state, argument)?;
                self.require(
                    ResourceObligationKind::PermissionAvailable {
                        permission: argument,
                    },
                    permission_availability_status(permission.availability()),
                );
                self.require(
                    ResourceObligationKind::LoanCompatible {
                        loan: match permission.authority() {
                            PermissionAuthority::Loan(loan) => Some(loan),
                            PermissionAuthority::Owner | PermissionAuthority::Unknown => None,
                        },
                        permission: argument,
                        access: exact_abstract_range(permission.range()),
                        required: AccessPermission::Read,
                    },
                    if borrowed_permission_slots.contains(&index) {
                        ObligationStatus::Proven
                    } else {
                        owner_authority_status(permission.authority())
                    },
                );
                for &previous in &permission_arguments {
                    self.require(
                        ResourceObligationKind::PermissionOperandsDistinct {
                            left: previous,
                            right: argument,
                        },
                        if previous == argument {
                            ObligationStatus::Refuted
                        } else {
                            ObligationStatus::Proven
                        },
                    );
                }
                permission_arguments.push(argument);
                if moved_permission_slots.contains(&index)
                    && let AbstractProvenance::Known(allocation) = permission.provenance()
                {
                    transferred_allocations.insert(allocation);
                }
            }
        }

        for argument in permission_arguments.into_iter().collect::<BTreeSet<_>>() {
            mark_permission_consumed(&mut self.state, argument)?;
        }
        for (loan_id, argument, slots) in borrowed_authority_results {
            if let Some(loan) = self.state.loan_mut(loan_id) {
                loan.remove_authority(argument);
                for slot in slots {
                    loan.add_authority(results[slot as usize].id);
                }
            }
        }

        let preserved_instances = contract
            .zip(instantiation.as_ref())
            .map(|(contract, mapping)| contract.mapped_postcondition_instances(mapping))
            .unwrap_or_default();
        let mut body_failure = false;
        let mut body_outcomes = None;
        if let Some(context) = self.contract_context
            && let Some(summary_context) = context.summary
        {
            use crate::verifier::summary::CallSummaryOutcome as Outcome;
            use crate::verifier::summary::audit::{CallObservation, MappingLoss};
            let mapping_loss = std::cell::Cell::new(Some(MappingLoss::AbiOrResource));
            let closed = summary_context.registry.and_then(|r| r.get(target));
            let outcome = if let Some(closed) = closed {
                if self.obligations.iter().all(|o| o.is_proven()) {
                    match crate::verifier::summary::instantiate(
                        closed,
                        crate::verifier::summary::CallInstantiation {
                            loss: &mapping_loss,
                            before: &before,
                            consumed: &self.state,
                            arguments,
                            memory: self.memory,
                            site: context.call_site,
                            target,
                            queries: &self.relations.queries,
                            limits: self.relation_limits,
                        },
                    ) {
                        Ok(Some(applied)) => {
                            for outcome in &applied {
                                for event in &outcome.events {
                                    summary_context.record(event.clone());
                                }
                            }
                            body_outcomes = Some(applied);
                            if summary_context
                                .registry
                                .is_some_and(|r| r.is_inductive(&target.symbol))
                            {
                                Outcome::Inductive
                            } else {
                                Outcome::Applied
                            }
                        }
                        Ok(None) => Outcome::UnsupportedMapping,
                        Err(TransferError::StateDefinition(error)) => {
                            self.instance_failure(error)?;
                            body_failure = true;
                            Outcome::FreshInstanceFailure
                        }
                        Err(error) => return Err(error),
                    }
                } else {
                    Outcome::Preconditions
                }
            } else {
                Outcome::NotClosed
            };
            summary_context.call(
                &target.symbol,
                outcome,
                CallObservation {
                    finding: summary_context.site,
                    case_ordinal: summary_context.case_ordinal,
                    instance_site: context.call_site,
                    guard: before.path_condition().clone(),
                    dependency: closed.map(|s| s.binding.clone()),
                    arguments: arguments
                        .iter()
                        .map(|id| (*id, before.value(*id).copied()))
                        .collect(),
                    mapping_loss: if outcome == Outcome::UnsupportedMapping {
                        mapping_loss.get()
                    } else {
                        None
                    },
                    worlds: body_outcomes
                        .as_ref()
                        .map(|a| a.iter().map(|o| o.audit.clone()).collect())
                        .unwrap_or_default(),
                },
            );
        }
        if let Some(outcomes) = body_outcomes {
            let conditional = outcomes.len() > 1;
            let mut cases = Vec::new();
            for outcome in outcomes {
                self.state = outcome.state;
                for allocation in transferred_allocations
                    .iter()
                    .chain(&aggregate_payload_allocations)
                {
                    if !outcome.preserved.contains(allocation) {
                        self.state.transfer_opaque_instance(*allocation);
                    }
                }
                for (index, result) in results.iter().enumerate() {
                    // Closed body worlds have checked interface exports. Do not
                    // overwrite their pointer/length/domain with an identity
                    // skeleton; that skeleton belongs only to the fallback.
                    let value = outcome.values[index];
                    self.define(*result, value)?;
                    if let Some(expression) = outcome.expressions.get(&index) {
                        self.state.set_word_expression(result.id, *expression);
                    }
                    if conditional && let AbstractValue::Bool(value) = value {
                        match value {
                            super::AbstractBool::True => self
                                .state
                                .conjoin_path_fact(super::PathFact::boolean(result.id, true)),
                            super::AbstractBool::False => self
                                .state
                                .conjoin_path_fact(super::PathFact::boolean(result.id, false)),
                            super::AbstractBool::Unknown => {}
                        }
                    }
                }
                if let Some(abi) = target.abi.as_ref() {
                    self.refine_projected_result_length(abi, arguments, results)?;
                }
                for (index, result) in results.iter().enumerate() {
                    if let AbstractValue::Permission(permission) = outcome.values[index]
                        && let PermissionAuthority::Loan(loan) = permission.authority()
                        && let Some(loan) = self.state.loan_mut(loan)
                    {
                        loan.add_authority(result.id);
                    }
                }
                if let Some(abi) = target.abi.as_ref()
                    && ((!abi.borrow_result_alternatives().is_empty()
                        && abi.results()[0].interface().transfer
                            == crate::VirInterfaceTransfer::BorrowMutable)
                        || abi.borrow_result().is_some_and(|relation| {
                            relation.projection != crate::BorrowProjection::Whole
                        }))
                {
                    let slot = *abi.results()[0]
                        .result_slots()
                        .last()
                        .ok_or(TransferError::InvalidDerivedRange)?
                        as usize;
                    let result = results
                        .get(slot)
                        .ok_or(TransferError::InvalidDerivedRange)?;
                    let permission = permission_fact(&self.state, result.id)?;
                    let PermissionAuthority::Loan(parent_id) = permission.authority() else {
                        return Err(TransferError::InvalidDerivedRange);
                    };
                    let parent = self
                        .state
                        .loan(parent_id)
                        .cloned()
                        .ok_or(TransferError::InvalidDerivedRange)?;
                    let candidate = abi
                        .borrow_result_parameters()
                        .iter()
                        .position(|parameter| {
                            abi.parameters()[*parameter]
                                .parameter_slots()
                                .last()
                                .and_then(|slot| arguments.get(*slot as usize))
                                .and_then(|argument| self.state.value(*argument))
                                .is_some_and(|value| {
                                    matches!(
                                        value,
                                        AbstractValue::Permission(input)
                                            if input.authority()
                                                == PermissionAuthority::Loan(parent_id)
                                    )
                                })
                        })
                        .ok_or(TransferError::InvalidDerivedRange)?;
                    let candidate = u32::try_from(candidate)
                        .ok()
                        .filter(|candidate| *candidate < 4)
                        .ok_or(TransferError::InvalidDerivedRange)?;
                    // The upper half of the verifier-only loan namespace is
                    // reserved for call-return reborrows. Four bounded source
                    // alternatives receive distinct instances at one SSA call
                    // result, so worlds selecting different parents remain
                    // joinable without conflating their child metadata.
                    let child_site = result
                        .id
                        .get()
                        .checked_mul(4)
                        .and_then(|site| site.checked_add(candidate))
                        .filter(|site| *site < (1 << 31))
                        .ok_or(TransferError::InvalidDerivedRange)?;
                    let child_id = crate::VirLoanId::new((1 << 31) | child_site);
                    let child_kind = if abi.results()[0].interface().transfer
                        == crate::VirInterfaceTransfer::BorrowMutable
                    {
                        VirLoanKind::Mutable
                    } else {
                        VirLoanKind::Shared
                    };
                    if let Some(parent) = self.state.loan_mut(parent_id) {
                        parent.remove_authority(result.id);
                        if child_kind == VirLoanKind::Mutable {
                            parent.set_activity(LoanActivity::Suspended);
                        }
                    }
                    self.state.define_next_loan_instance(
                        child_id,
                        AbstractLoan::new(
                            parent.provenance(),
                            parent.range(),
                            child_kind,
                            parent.region(),
                            Some(parent_id),
                            LoanActivity::Active,
                        )
                        .with_footprint(parent.footprint())
                        .with_authority(result.id),
                    )?;
                    *self
                        .state
                        .value_mut(result.id)
                        .ok_or(TransferError::InvalidDerivedRange)? = AbstractValue::Permission(
                        permission.with_authority(PermissionAuthority::Loan(child_id)),
                    );
                }
                cases.push(self.state.clone());
            }
            let mut joined = ResourceState::unreachable();
            for case in &cases {
                joined = joined
                    .join(case)
                    .map_err(|_| TransferError::InvalidDerivedRange)?;
            }
            self.state = joined;
            self.cases = Some(cases);
            return Ok(());
        }
        self.invalidate_opaque_frame(&before, arguments, target)?;
        let summary_results = if body_failure {
            None
        } else if let (Some(contract), Some(mapping), Some(context)) =
            (contract, instantiation, self.contract_context)
        {
            match apply_postconditions(&self.state, contract, mapping, context.call_site) {
                Ok((state, values)) => {
                    self.state = state;
                    Some(values)
                }
                Err(ContractApplicationError::StateDefinition(error)) => {
                    self.instance_failure(error)?;
                    None
                }
                Err(error) => return Err(error.into()),
            }
        } else {
            None
        };
        for allocation in transferred_allocations {
            if summary_results.is_none() || !preserved_instances.contains(&allocation) {
                self.state.transfer_opaque_instance(allocation);
            }
        }
        for allocation in aggregate_payload_allocations {
            if summary_results.is_none() || !preserved_instances.contains(&allocation) {
                self.state.transfer_opaque_instance(allocation);
            }
        }

        if summary_results.is_some()
            && let Some(abi) = &target.abi
        {
            for (result_index, binding) in abi.results().iter().enumerate() {
                if binding.interface().transfer != crate::VirInterfaceTransfer::Move {
                    continue;
                }
                let crate::VirAbiValue::IndirectAggregate { access } = binding.value() else {
                    continue;
                };
                let [pointer_slot, _permission_slot] = binding.parameter_slots() else {
                    return Err(TransferError::InvalidValidatedCallShape {
                        arguments: arguments.len(),
                        parameters: target.signature.parameters.len(),
                        results: results.len(),
                        expected_results: target.signature.results.len(),
                    });
                };
                let pointer = *arguments.get(*pointer_slot as usize).ok_or(
                    TransferError::InvalidValidatedCallShape {
                        arguments: arguments.len(),
                        parameters: target.signature.parameters.len(),
                        results: results.len(),
                        expected_results: target.signature.results.len(),
                    },
                )?;
                let result_index =
                    u32::try_from(result_index).map_err(|_| TransferError::InvalidDerivedRange)?;
                let call_site = self
                    .contract_context
                    .expect("summary results require a contract context")
                    .call_site;
                let installation = install_aggregate_abi_payloads(
                    &mut self.state,
                    self.memory,
                    pointer,
                    *access,
                    |leaf| AbstractAllocationId::abi_call_payload(call_site, result_index, leaf),
                );
                match installation {
                    Ok(true) => {}
                    Ok(false) => self.require(
                        ResourceObligationKind::AggregateAbiPayloadValid {
                            allocation: None,
                            offset_bytes: None,
                            access: *access,
                        },
                        ObligationStatus::Unknown,
                    ),
                    Err(TransferError::StateDefinition(error)) => self.instance_failure(error)?,
                    Err(error) => return Err(error),
                }
            }
        }

        for (index, (result, &expected)) in
            results.iter().zip(&target.signature.results).enumerate()
        {
            if result.ty != expected {
                return Err(TransferError::InvalidValidatedCallResultType {
                    value: result.id,
                    declared: result.ty,
                    expected,
                });
            }
            let fact = abi_permission_restorations
                .get(&index)
                .copied()
                .or_else(|| {
                    summary_results
                        .as_ref()
                        .and_then(|values| values.get(index))
                        .copied()
                })
                .unwrap_or_else(|| unknown_value(result.ty));
            self.define(*result, fact)?;
            if let Some(expression) = abi_word_restorations.get(&index) {
                self.state.set_word_expression(result.id, *expression);
            }
        }
        Ok(())
    }

    fn require_borrow_projection_range(
        &mut self,
        abi: &crate::VirAbiSignature,
        arguments: &[VirValueId],
    ) -> Result<(), TransferError> {
        let Some(relation) = abi.borrow_result() else {
            return Ok(());
        };
        let crate::BorrowProjection::Slice { start, end, .. } = relation.projection else {
            return Ok(());
        };
        let source = abi
            .parameters()
            .get(relation.parameter as usize)
            .ok_or(TransferError::InvalidDerivedRange)?;
        let length_slot = *source
            .parameter_slots()
            .get(1)
            .ok_or(TransferError::InvalidDerivedRange)? as usize;
        let length = *arguments
            .get(length_slot)
            .ok_or(TransferError::InvalidDerivedRange)?;
        let term = |bound| -> Result<RelationTerm, TransferError> {
            match bound {
                crate::BorrowSliceBound::Constant(value) => Ok(RelationTerm::Constant(value)),
                crate::BorrowSliceBound::Parameter(parameter) => {
                    let binding = abi
                        .parameters()
                        .get(parameter as usize)
                        .ok_or(TransferError::InvalidDerivedRange)?;
                    let slot = *binding
                        .parameter_slots()
                        .first()
                        .ok_or(TransferError::InvalidDerivedRange)?
                        as usize;
                    Ok(word(
                        *arguments
                            .get(slot)
                            .ok_or(TransferError::InvalidDerivedRange)?,
                    ))
                }
                crate::BorrowSliceBound::SourceLength => Ok(word(length)),
            }
        };
        let start = term(start)?;
        let end = term(end)?;
        self.require(
            ResourceObligationKind::BorrowProjectionRangeOrdered {
                source_parameter: relation.parameter,
            },
            self.compare_words(RelationComparison::LessOrEqual, start, end),
        );
        self.require(
            ResourceObligationKind::BorrowProjectionRangeWithinSource {
                source_parameter: relation.parameter,
            },
            self.compare_words(RelationComparison::LessOrEqual, end, word(length)),
        );
        Ok(())
    }

    fn refine_projected_result_length(
        &mut self,
        abi: &crate::VirAbiSignature,
        arguments: &[VirValueId],
        results: &[VirValue],
    ) -> Result<(), TransferError> {
        let Some(relation) = abi.borrow_result() else {
            return Ok(());
        };
        let crate::BorrowProjection::Slice { start, end, .. } = relation.projection else {
            return Ok(());
        };
        let source = abi
            .parameters()
            .get(relation.parameter as usize)
            .ok_or(TransferError::InvalidDerivedRange)?;
        let interval = |bound| -> Result<U64Interval, TransferError> {
            let argument = match bound {
                crate::BorrowSliceBound::Constant(value) => {
                    return Ok(U64Interval::exact(value));
                }
                crate::BorrowSliceBound::Parameter(parameter) => {
                    let binding = abi
                        .parameters()
                        .get(parameter as usize)
                        .ok_or(TransferError::InvalidDerivedRange)?;
                    *arguments
                        .get(
                            *binding
                                .parameter_slots()
                                .first()
                                .ok_or(TransferError::InvalidDerivedRange)?
                                as usize,
                        )
                        .ok_or(TransferError::InvalidDerivedRange)?
                }
                crate::BorrowSliceBound::SourceLength => *arguments
                    .get(
                        *source
                            .parameter_slots()
                            .get(1)
                            .ok_or(TransferError::InvalidDerivedRange)?
                            as usize,
                    )
                    .ok_or(TransferError::InvalidDerivedRange)?,
            };
            match self.state.value(argument) {
                Some(AbstractValue::U64(value)) => Ok(*value),
                _ => Err(TransferError::InvalidDerivedRange),
            }
        };
        let start = interval(start)?;
        let end = interval(end)?;
        let length = start
            .exact_value()
            .zip(end.exact_value())
            .and_then(|(start, end)| end.checked_sub(start))
            .map_or_else(|| subtract_intervals(end, start), U64Interval::exact);
        let result = abi
            .results()
            .get(relation.result as usize)
            .and_then(|binding| binding.result_slots().get(1))
            .and_then(|slot| results.get(*slot as usize))
            .ok_or(TransferError::InvalidDerivedRange)?;
        *self
            .state
            .value_mut(result.id)
            .ok_or(TransferError::InvalidDerivedRange)? = AbstractValue::U64(length);
        Ok(())
    }

    /// Unknown effects are not a read-only frame. Forget all writable extents,
    /// then retain only the complete-value guarantee of an admitted borrowed
    /// ABI. Explicit ensures are installed separately by apply_postconditions.
    fn invalidate_opaque_frame(
        &mut self,
        before: &ResourceState,
        arguments: &[VirValueId],
        target: &VirCallTarget,
    ) -> Result<(), TransferError> {
        // Dense, pointer-free borrowed values have an independently checked
        // ABI restoration guarantee. Their initialized/valid bytes (including
        // symbolic prefixes) survive a call, but their contents/object facts do
        // not. This is a type guarantee, not an inferred empty write footprint.
        let mut restored_values = BTreeSet::new();
        if let Some(abi) = &target.abi {
            for binding in abi.parameters() {
                if !binding.interface().transfer.is_borrow() {
                    continue;
                }
                let access = match binding.value() {
                    crate::VirAbiValue::Pointer { pointee, .. } => *pointee,
                    crate::VirAbiValue::Slice { element, .. } => *element,
                    _ => continue,
                };
                let shape = self
                    .memory
                    .object_shape(access)
                    .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?;
                if shape.resource_leaves().is_empty()
                    && shape.variants().is_empty()
                    && shape.value_bytes().len() == 1
                    && shape.value_bytes()[0].start_bytes() == 0
                    && shape.value_bytes()[0].end_bytes() == shape.size_bytes()
                {
                    restored_values.extend(
                        binding
                            .parameter_slots()
                            .iter()
                            .map(|slot| arguments[*slot as usize]),
                    );
                }
            }
        }
        let mut writes = Vec::new();
        for argument in arguments {
            let Some(AbstractValue::Permission(permission)) = before.value(*argument) else {
                continue;
            };
            if permission.access() == AccessPermission::Read {
                continue;
            }
            let ids = match permission.provenance() {
                AbstractProvenance::Known(id) => vec![id],
                AbstractProvenance::Unknown => before.allocations().keys().copied().collect(),
            };
            for id in ids {
                let Some(allocation) = before.allocation(id) else {
                    continue;
                };
                let whole = ByteRange::new(0, allocation.size_bytes())
                    .map_err(|_| TransferError::InvalidDerivedRange)?;
                let range = exact_abstract_range(permission.range())
                    .and_then(|r| r.intersection(whole))
                    .unwrap_or(whole);
                writes.push((id, range, restored_values.contains(argument)));
            }
        }
        for (id, range, restored) in &writes {
            if let Some(allocation) = self.state.allocation_mut(*id) {
                if !restored {
                    allocation.forget_initialization(*range)?;
                    allocation.forget_validity(*range)?;
                }
                allocation.forget_object_state(*range)?;
            }
        }
        if let Some(abi) = &target.abi {
            for binding in abi.parameters() {
                if !binding.interface().transfer.is_borrow() {
                    continue;
                }
                let Some(&slot) = binding.parameter_slots().first() else {
                    continue;
                };
                if restored_values.contains(&arguments[slot as usize]) {
                    continue;
                }
                let Some(AbstractValue::Pointer(pointer)) = before.value(arguments[slot as usize])
                else {
                    continue;
                };
                let (AbstractProvenance::Known(id), Some(base)) =
                    (pointer.provenance(), pointer.offset_bytes().exact_value())
                else {
                    continue;
                };
                let Some(old) = before.allocation(id) else {
                    continue;
                };
                let mut guaranteed = Vec::new();
                match binding.value() {
                    crate::VirAbiValue::Pointer { pointee, .. } => {
                        let shape = self
                            .memory
                            .object_shape(*pointee)
                            .map_err(|_| TransferError::InvalidValidatedMemoryAccess(*pointee))?;
                        for bytes in shape.value_bytes() {
                            if let (Some(start), Some(end)) = (
                                base.checked_add(bytes.start_bytes()),
                                base.checked_add(bytes.end_bytes()),
                            ) {
                                if let Ok(range) = ByteRange::new(start, end) {
                                    guaranteed.push(range);
                                }
                            }
                        }
                    }
                    crate::VirAbiValue::Slice { element, .. } => {
                        let shape = self
                            .memory
                            .object_shape(*element)
                            .map_err(|_| TransferError::InvalidValidatedMemoryAccess(*element))?;
                        if shape.value_bytes().len() == 1
                            && shape.value_bytes()[0].start_bytes() == 0
                            && shape.value_bytes()[0].end_bytes() == shape.size_bytes()
                        {
                            guaranteed.extend(
                                writes.iter().filter_map(|(owner, range, _)| {
                                    (*owner == id).then_some(*range)
                                }),
                            );
                        }
                    }
                    _ => {}
                }
                if let Some(allocation) = self.state.allocation_mut(id) {
                    for range in guaranteed {
                        for old_range in old.initialization().initialized().ranges() {
                            if let Some(part) = range.intersection(*old_range) {
                                allocation.mark_initialized(part)?;
                            }
                        }
                        for old_range in old.valid_value_bytes().ranges() {
                            if let Some(part) = range.intersection(*old_range) {
                                allocation.mark_valid(part)?;
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

pub(in crate::verifier) fn aggregate_abi_payload_status(
    state: &ResourceState,
    memory: &VirMemorySchema,
    resource_access: VirMemoryAccess,
    payload: &TypedResourcePayload,
) -> ObligationStatus {
    let Ok(pointee) = owned_resource_pointee(memory, resource_access) else {
        return ObligationStatus::Refuted;
    };
    let Some(expected_layout) = memory
        .layout(pointee.layout)
        .filter(|layout| layout.ty == pointee.ty)
    else {
        return ObligationStatus::Refuted;
    };
    let AbstractProvenance::Known(allocation_id) = payload.pointer().provenance() else {
        return ObligationStatus::Unknown;
    };
    let Some(allocation) = state.allocation(allocation_id) else {
        return ObligationStatus::Unknown;
    };
    let Ok(whole) = ByteRange::new(0, allocation.size_bytes()) else {
        return ObligationStatus::Refuted;
    };
    combine_statuses([
        object_drop_payload_status(state, payload),
        memory_access_status(payload.pointer().memory_access(), pointee),
        if allocation.size_bytes() == expected_layout.size_bytes
            && allocation.alignment().bytes() >= expected_layout.alignment
        {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Refuted
        },
        match allocation.initialization().classify(whole) {
            InitializationClass::Initialized => ObligationStatus::Proven,
            InitializationClass::MaybeInitialized => ObligationStatus::Unknown,
            InitializationClass::Uninitialized => ObligationStatus::Refuted,
        },
        if allocation.valid_value_bytes().contains(whole) {
            ObligationStatus::Proven
        } else if allocation.valid_value_bytes().is_precise() {
            ObligationStatus::Refuted
        } else {
            ObligationStatus::Unknown
        },
    ])
}

/// Installs the existential owners guaranteed by one variant-free,
/// ownership-bearing aggregate ABI value into its caller-owned storage.
///
/// `false` means the storage pointer is not precise enough to attach the
/// payload. Callers retain an unknown/refuted obligation rather than gaining
/// ownership from an imprecise address.
pub(in crate::verifier) fn install_aggregate_abi_payloads(
    state: &mut ResourceState,
    memory: &VirMemorySchema,
    storage_pointer: VirValueId,
    access: VirMemoryAccess,
    mut payload_id: impl FnMut(u32) -> AbstractAllocationId,
) -> Result<bool, TransferError> {
    let shape = memory
        .object_shape(access)
        .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?;
    if !shape.variants().is_empty()
        || shape.resource_leaves().is_empty()
        || !shape
            .resource_leaves()
            .iter()
            .all(|leaf| leaf.kind() == VirPointerKind::Own)
    {
        return Err(TransferError::InvalidValidatedMemoryAccess(access));
    }
    let pointer = match state.value(storage_pointer).copied() {
        Some(AbstractValue::Pointer(pointer)) => pointer,
        Some(value) => {
            return Err(TransferError::AbstractValueTypeMismatch {
                value: storage_pointer,
                expected: VirType::Pointer { access },
                found: abstract_value_type(value),
            });
        }
        None => return Ok(false),
    };
    let (AbstractProvenance::Known(storage), Some(base)) =
        (pointer.provenance(), pointer.offset_bytes().exact_value())
    else {
        return Ok(false);
    };
    let mut payloads = Vec::with_capacity(shape.resource_leaves().len());
    for (index, leaf) in shape.resource_leaves().iter().enumerate() {
        let index = u32::try_from(index).map_err(|_| TransferError::InvalidDerivedRange)?;
        let pointee = owned_resource_pointee(memory, leaf.access())?;
        let layout = memory
            .layout(pointee.layout)
            .filter(|layout| layout.ty == pointee.ty && layout.size_bytes != 0)
            .ok_or(TransferError::InvalidValidatedMemoryAccess(pointee))?;
        let allocation_id = payload_id(index);
        let mut allocation =
            AbstractAllocation::new(VirRegionId::new(0), layout.size_bytes, layout.alignment)?;
        let whole =
            ByteRange::new(0, layout.size_bytes).map_err(|_| TransferError::InvalidDerivedRange)?;
        allocation.mark_initialized(whole)?;
        allocation.mark_valid(whole)?;
        state.introduce_allocation_instance(allocation_id, allocation)?;
        let provenance = AbstractProvenance::Known(allocation_id);
        let pointer = AbstractPointer::new(
            provenance,
            U64Interval::exact(0),
            GuaranteedAlignment::new(layout.alignment)
                .map_err(|_| TransferError::InvalidValidatedAlignment(layout.alignment))?,
        )
        .with_memory_access(Some(pointee));
        let permission = AbstractPermission::new(
            provenance,
            AbstractByteRange::Exact(whole),
            AccessPermission::Write,
            FreeCapability::Yes,
        );
        let offset = base
            .checked_add(leaf.bytes().start_bytes())
            .ok_or(TransferError::InvalidDerivedRange)?;
        payloads.push((
            ResourcePayloadKey::new(offset, leaf.access()),
            MovePathState::available(TypedResourcePayload::new(pointer, permission)),
        ));
    }
    let Some(storage) = state.allocation_mut(storage) else {
        return Ok(false);
    };
    for (key, payload) in payloads {
        if !storage.set_resource_payload(key, payload)? {
            return Ok(false);
        }
    }
    Ok(true)
}
