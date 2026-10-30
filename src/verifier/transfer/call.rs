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
        let prefixes = self.borrowed_call_prefix_frame(target, arguments);
        self.call_inner(results, target, arguments)?;
        if self.obligations.iter().all(|o| o.is_proven()) {
            Self::restore_borrowed_call_prefix_frame(&mut self.state, &prefixes);
            if let Some(cases) = &mut self.cases {
                for case in cases {
                    Self::restore_borrowed_call_prefix_frame(case, &prefixes);
                }
            }
        }
        Ok(())
    }

    fn call_inner(
        &mut self,
        results: &[VirValue],
        target: &VirCallTarget,
        arguments: &[VirValueId],
    ) -> Result<(), TransferError> {
        let original = self.state.clone();
        for (holder, instance) in original.predicate_instances() {
            self.require(
                ResourceObligationKind::PredicateBoundaryRestored {
                    holder: holder.0,
                    function_exit: false,
                },
                if instance.is_folded() {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Refuted
                },
            );
        }
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
        let mut predicate_arguments = BTreeSet::new();
        let mut predicate_payloads = BTreeSet::new();
        if let Some(contract) = contract {
            for interface in contract.predicates.iter().filter(|i| !i.metadata.ensures) {
                let status = if interface.export(&mut self.state, arguments, &[]).is_ok() {
                    predicate_payloads.extend(interface.projected_allocations(
                        &self.state,
                        arguments,
                        &[],
                    ));
                    for (_, slot) in &interface.metadata.bindings {
                        if let Some(argument) = arguments.get(*slot as usize) {
                            predicate_arguments.insert(*argument);
                        }
                    }
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                };
                self.require(
                    ResourceObligationKind::PredicateInterfaceValid {
                        predicate: interface.metadata.predicate,
                        ensures: false,
                    },
                    status,
                );
            }
        }
        let before = self.state.clone();
        let contract_matches =
            contract.is_some_and(|contract| contract.signature() == &target.signature);
        // Declarations are not callable certificates. Only the private registry
        // supplies either a closed dependency or a scoped SCC hypothesis. Every
        // candidate call still checks requires; final replay checks the body.
        let interface_available = !contract.is_some_and(|c| c.has_explicit_contract())
            || self
                .contract_context
                .and_then(|c| c.summary)
                .and_then(|s| s.registry)
                .and_then(|r| r.get(target))
                .is_some();
        self.require(
            ResourceObligationKind::CallContractAvailable {
                contract: target.contract,
            },
            if contract_matches && interface_available {
                ObligationStatus::Proven
            } else if contract_matches {
                ObligationStatus::Unknown
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
                crate::CfgAnalysisConfig {
                    relation_limits: self.relation_limits,
                    max_region_pairs_per_instruction: self.relations.limit,
                    ..Default::default()
                },
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
                // Pointer-to-container entries import the same finite payload
                // profile as predicates. Check the actual fields before any
                // summary or contract can use those entry guarantees.
                if (binding.interface().transfer.is_borrow()
                    || binding.interface().transfer == crate::VirInterfaceTransfer::Move)
                    && let crate::VirAbiValue::Pointer { pointee, .. } = binding.value()
                    && let Some(fields) =
                        crate::vir::predicate_resource_fields(self.memory, *pointee)
                    && !fields.is_empty()
                {
                    let pointer = pointer_fact(
                        &self.state,
                        arguments[binding.parameter_slots()[0] as usize],
                    )?;
                    for mut field in fields {
                        let at = pointer
                            .offset_bytes()
                            .exact_value()
                            .and_then(|base| base.checked_add(field.offset));
                        let allocation = match pointer.provenance() {
                            AbstractProvenance::Known(id) => Some(id),
                            _ => None,
                        };
                        let valid = allocation.zip(at).is_some_and(|(id, offset)| {
                            field.offset = offset;
                            self.state.bounded_field_payload(id, &field).is_ok()
                        });
                        self.require(
                            ResourceObligationKind::AggregateAbiPayloadValid {
                                allocation,
                                offset_bytes: at,
                                access: field.access,
                            },
                            if valid {
                                ObligationStatus::Proven
                            } else {
                                ObligationStatus::Unknown
                            },
                        );
                    }
                }
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
                            if !predicate_arguments.contains(&argument) {
                                self.require_object_initialization(
                                    &object,
                                    &mask.possible_value_bytes,
                                    InitializationRequirement::Initialized,
                                );
                                self.require_object_validity(&object, &mask.possible_value_bytes);
                            }
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
                        if leaf.kind() == VirPointerKind::Raw {
                            continue;
                        }
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
                                        object.allocation_id.zip(offset).map(|(storage, offset)|
                                            (storage, ResourcePayloadKey::new(offset, leaf.access()))),
                                        matches!(payload.pointer().provenance(),AbstractProvenance::Known(id) if predicate_payloads.contains(&id)),
                                    )
                                }
                                Some(MovePathState::Moved) => ObligationStatus::Refuted,
                                Some(MovePathState::Unknown) | None => ObligationStatus::Unknown,
                            },
                        );
                        if leaf.kind() == VirPointerKind::Own
                            && let Some(MovePathState::Available(payload)) = payload
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
                    // A returned view owns the output permission slot. If a prior
                    // failed borrow left no loan authority, keep the result unknown;
                    // this is an unproved call, not a malformed physical ABI.
                    if binding.result_slots().is_empty()
                        && abi.borrow_result_parameter() == Some(parameter_index)
                    {
                        continue;
                    }
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
                            results,
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
                        Ok(Some(applied))
                            if applied.iter().all(|outcome| {
                                outcome.state.loans().values().all(|loan| {
                                    loan.authorities().len()
                                        <= self.loan_context.map_or(usize::MAX, |context| {
                                            context.limits.max_aliases_per_loan
                                        })
                                })
                            }) =>
                        {
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
                        Ok(None) | Ok(Some(_)) => Outcome::UnsupportedMapping,
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
                    if let Some(origin) = outcome.origins.get(&index) {
                        self.state.set_word_origin(result.id, *origin);
                    }
                    if let Some(origin) = outcome.bool_origins.get(&index) {
                        self.state.set_bool_origin(result.id, *origin);
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
                    && abi.results().first().and_then(|b| b.result_slots().last())
                        .and_then(|slot| results.get(*slot as usize))
                        .and_then(|r| self.state.value(r.id)).is_some_and(|returned|
                            matches!(returned, AbstractValue::Permission(output) if abi.borrow_result_parameters().iter().any(|index|
                                abi.parameters()[*index].parameter_slots().last()
                                    .and_then(|slot| arguments.get(*slot as usize))
                                    .and_then(|id| before.value(*id)).is_some_and(|input|
                                        matches!(input, AbstractValue::Permission(input) if input.authority() == output.authority())))))
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
                    // Use the checked summary's actual permission range. A
                    // whole-parent footprint would hide the exported subview;
                    // an envelope alone must never become access authority.
                    let (start, end) = permission
                        .range()
                        .bounds()
                        .ok_or(TransferError::InvalidDerivedRange)?;
                    let envelope = ByteRange::new(start.interval().lower(), end.interval().upper())
                        .map_err(|_| TransferError::InvalidDerivedRange)?;
                    let pointer_slot = abi.results()[0].result_slots()[0] as usize;
                    let pointer = pointer_fact(&self.state, results[pointer_slot].id)?;
                    let access = pointer
                        .memory_access()
                        .ok_or(TransferError::InvalidDerivedRange)?;
                    let footprint = crate::verifier::MemoryFootprint {
                        provenance: permission.provenance(),
                        access,
                        stride_bytes: self
                            .memory
                            .layout(access.layout)
                            .ok_or(TransferError::InvalidDerivedRange)?
                            .size_bytes,
                        range: permission.range(),
                        envelope,
                    };
                    self.state.define_next_loan_instance(
                        child_id,
                        AbstractLoan::new(
                            parent.provenance(),
                            envelope,
                            child_kind,
                            parent.region(),
                            Some(parent_id),
                            LoanActivity::Active,
                        )
                        .with_footprint(Some(footprint))
                        .with_authority(result.id),
                    )?;
                    *self
                        .state
                        .value_mut(result.id)
                        .ok_or(TransferError::InvalidDerivedRange)? = AbstractValue::Permission(
                        permission.with_authority(PermissionAuthority::Loan(child_id)),
                    );
                }
                if let Some(contract) = contract {
                    self.import_predicate_postconditions(contract, results, arguments, &before);
                }
                cases.push(self.state.clone());
            }
            self.cases = Some(cases);
            return Ok(());
        }
        self.invalidate_opaque_frame(&before, arguments, target)?;
        let summary_results = if body_failure
            || (contract.is_some_and(|c| c.has_explicit_contract())
                && (!interface_available || !self.obligations.iter().all(|o| o.is_proven())))
        {
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
        // The checked interface is also used when a body summary cannot be
        // mapped into this caller world. Restore its predicates only after the
        // actual ABI results and permissions exist, just as in the body path.
        if summary_results.is_some()
            && let Some(contract) = contract
        {
            self.import_predicate_postconditions(contract, results, arguments, &before);
        }
        Ok(())
    }

    fn import_predicate_postconditions(
        &mut self,
        contract: &crate::verifier::contract::InstantiatedContract,
        results: &[VirValue],
        arguments: &[VirValueId],
        before: &ResourceState,
    ) {
        let ids = results.iter().map(|result| result.id).collect::<Vec<_>>();
        let mut next = self.state.clone();
        let mut valid = true;
        for interface in contract.predicates.iter().filter(|i| i.metadata.ensures) {
            let imported = interface
                .import_post(&mut next, &ids, arguments, before)
                .is_ok();
            valid &= imported;
            self.require(
                ResourceObligationKind::PredicateInterfaceValid {
                    predicate: interface.metadata.predicate,
                    ensures: true,
                },
                if imported {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
        }
        // A failed member must not publish a partial postcondition package.
        if valid {
            self.state = next;
        }
    }

    fn require_borrow_projection_range(
        &mut self,
        abi: &crate::VirAbiSignature,
        arguments: &[VirValueId],
    ) -> Result<(), TransferError> {
        let Some(relation) = abi.borrow_result() else {
            return Ok(());
        };
        let Some((start, end)) = relation.projection.slice_bounds() else {
            return Ok(());
        };
        let source = abi
            .parameters()
            .get(relation.parameter as usize)
            .ok_or(TransferError::InvalidDerivedRange)?;
        let length = if let Some(length) = relation.projection.array_length() {
            RelationTerm::Constant(length)
        } else {
            let slot = *source
                .parameter_slots()
                .get(1)
                .ok_or(TransferError::InvalidDerivedRange)? as usize;
            word(
                *arguments
                    .get(slot)
                    .ok_or(TransferError::InvalidDerivedRange)?,
            )
        };
        let term = |bound| -> Result<RelationTerm, TransferError> {
            match bound {
                crate::BorrowSliceBound::ReturnedLength
                | crate::BorrowSliceBound::ReturnedOffset => {
                    Err(TransferError::InvalidDerivedRange)
                }
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
                crate::BorrowSliceBound::SourceLength => Ok(length),
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
            self.compare_words(RelationComparison::LessOrEqual, end, length),
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
        let Some((start, end)) = relation.projection.slice_bounds() else {
            return Ok(());
        };
        let source = abi
            .parameters()
            .get(relation.parameter as usize)
            .ok_or(TransferError::InvalidDerivedRange)?;
        let interval = |bound| -> Result<U64Interval, TransferError> {
            if bound == crate::BorrowSliceBound::SourceLength
                && let Some(length) = relation.projection.array_length()
            {
                return Ok(U64Interval::exact(length));
            }
            let argument = match bound {
                crate::BorrowSliceBound::ReturnedLength
                | crate::BorrowSliceBound::ReturnedOffset => {
                    return Err(TransferError::InvalidDerivedRange);
                }
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
        let Some(AbstractValue::U64(actual)) = self.state.value(result.id) else {
            return Err(TransferError::InvalidDerivedRange);
        };
        // A closed body already supplied this value and its historical ABI
        // source. The projection checks the same result; it is not a new
        // assignment and must neither widen it nor discard its identity.
        let length = actual
            .intersection(length)
            .ok_or(TransferError::InvalidDerivedRange)?;
        self.state.narrow_word_interval(result.id, length);
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
                let range = Self::call_effect_envelope(permission.range())
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
                            ) && let Ok(range) = ByteRange::new(start, end)
                            {
                                guaranteed.push(range);
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
    storage: Option<(AbstractAllocationId, ResourcePayloadKey)>,
    predicate: bool,
) -> ObligationStatus {
    if matches!(
        memory.kind(resource_access.ty),
        Some(crate::VirMemoryTypeKind::Pointer {
            kind: VirPointerKind::Reference,
            ..
        })
    ) {
        return aggregate_reference_payload_status(
            state,
            memory,
            resource_access,
            payload,
            storage.map(|(allocation, payload)| {
                crate::verifier::resource::AbstractLoanAuthority::stored(allocation, payload)
            }),
            predicate,
        );
    }
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
        if predicate {
            ObligationStatus::Proven
        } else {
            match allocation.initialization().classify(whole) {
                InitializationClass::Initialized => ObligationStatus::Proven,
                InitializationClass::MaybeInitialized => ObligationStatus::Unknown,
                InitializationClass::Uninitialized => ObligationStatus::Refuted,
            }
        },
        if predicate || allocation.valid_value_bytes().contains(whole) {
            ObligationStatus::Proven
        } else if allocation.valid_value_bytes().is_precise() {
            ObligationStatus::Refuted
        } else {
            ObligationStatus::Unknown
        },
    ])
}

/// The same typed value guarantee applies when a field loan leaves in SSA.
pub(in crate::verifier) fn reference_ssa_export_status(
    state: &ResourceState,
    memory: &VirMemorySchema,
    reference: VirMemoryAccess,
    pointer: VirValueId,
    permission: VirValueId,
) -> ObligationStatus {
    let (Some(AbstractValue::Pointer(pointer)), Some(AbstractValue::Permission(value))) =
        (state.value(pointer), state.value(permission))
    else {
        return ObligationStatus::Refuted;
    };
    aggregate_reference_payload_status(
        state,
        memory,
        reference,
        &TypedResourcePayload::new(*pointer, *value),
        Some(crate::verifier::resource::AbstractLoanAuthority::value(
            permission,
        )),
        false,
    )
}

/// A reference crossing an aggregate interface retains its actual stored loan.
/// No address equality, owner fallback, or predicate initialization guarantee
/// can manufacture the missing authority.
fn aggregate_reference_payload_status(
    state: &ResourceState,
    memory: &VirMemorySchema,
    reference: VirMemoryAccess,
    payload: &TypedResourcePayload,
    carrier: Option<crate::verifier::resource::AbstractLoanAuthority>,
    predicate: bool,
) -> ObligationStatus {
    use crate::verifier::LivenessState;
    use crate::verifier::resource::AbstractLoanAuthority;
    let Some(crate::VirMemoryTypeKind::Pointer {
        kind: VirPointerKind::Reference,
        pointee,
        mutability,
    }) = memory.kind(reference.ty)
    else {
        return ObligationStatus::Refuted;
    };
    let Some(pointee) = memory.access(*pointee) else {
        return ObligationStatus::Refuted;
    };
    let Ok(shape) = memory.object_shape(pointee) else {
        return ObligationStatus::Refuted;
    };
    // Nested resource guarantees need their own interface transfer.
    if !memory.resolves_access(reference)
        || !shape.variants().is_empty()
        || shape
            .resource_leaves()
            .iter()
            .any(|leaf| leaf.kind() != VirPointerKind::Raw)
    {
        return ObligationStatus::Refuted;
    }
    let Some(carrier) = carrier else {
        return ObligationStatus::Unknown;
    };
    let carrier_valid = match carrier {
        AbstractLoanAuthority::Stored {
            allocation: storage,
            payload: key,
        } => {
            key.access() == reference
                && state.allocation(storage).is_some_and(|container| {
                    container.liveness() == LivenessState::Live
                        && container.resource_payload(key)
                            == MovePathState::Available(Box::new(*payload))
                        && memory.layout(reference.layout).is_some_and(|layout| {
                            key.offset_bytes()
                                .checked_add(layout.size_bytes)
                                .is_some_and(|end| end <= container.size_bytes())
                        })
                })
        }
        AbstractLoanAuthority::Value(value) => {
            matches!(state.value(value), Some(AbstractValue::Permission(p)) if *p == payload.permission())
        }
    };
    let permission = payload.permission();
    let pointer = payload.pointer();
    let PermissionAuthority::Loan(id) = permission.authority() else {
        return ObligationStatus::Refuted;
    };
    let Some(loan) = state.loan(id) else {
        return ObligationStatus::Refuted;
    };
    let (kind, access) = if *mutability == crate::VirMutability::Const {
        (VirLoanKind::Shared, AccessPermission::Read)
    } else {
        (VirLoanKind::Mutable, AccessPermission::Write)
    };
    if !carrier_valid
        || loan.activity() != LoanActivity::Active
        || loan.kind() != kind
        || !loan.authorities().contains(&carrier)
        || (kind == VirLoanKind::Mutable && loan.authorities().len() != 1)
        || !loan.authorities().iter().all(|authority| match *authority {
            AbstractLoanAuthority::Value(value) => {
                state.value(value) == Some(&AbstractValue::Permission(permission))
            }
            AbstractLoanAuthority::Stored {
                allocation,
                payload,
            } => state.allocation(allocation).is_some_and(|object| {
                object.liveness() == LivenessState::Live
                    && matches!(object.resource_payload(payload), MovePathState::Available(value)
                            if value.permission() == permission)
            }),
        })
        || permission.availability() != super::PermissionAvailability::Available
        || permission.free_capability() != FreeCapability::No
        || permission.access() != access
        || permission.provenance() != loan.provenance()
        || pointer.provenance() != loan.provenance()
        || permission.range() != loan.actual_range()
        || state
            .loans()
            .values()
            .any(|child| child.parent() == Some(id) && child.activity() != LoanActivity::Ended)
    {
        return ObligationStatus::Refuted;
    }
    let AbstractProvenance::Known(referent) = pointer.provenance() else {
        return ObligationStatus::Unknown;
    };
    let Some(allocation) = state.allocation(referent) else {
        return ObligationStatus::Unknown;
    };
    let (Some(offset), Some(range)) = (
        pointer.offset_bytes().exact_value(),
        exact_abstract_range(permission.range()),
    ) else {
        return ObligationStatus::Unknown;
    };
    let Some(end) = offset.checked_add(shape.size_bytes()) else {
        return ObligationStatus::Refuted;
    };
    let Ok(object) = ByteRange::new(offset, end) else {
        return ObligationStatus::Refuted;
    };
    if allocation.liveness() != LivenessState::Live
        || end > allocation.size_bytes()
        || range.end() > allocation.size_bytes()
        || !range.contains(object)
        || offset % shape.alignment() != 0
        || allocation.alignment().bytes() < shape.alignment()
    {
        return ObligationStatus::Refuted;
    }
    let domain = match pointer.domain() {
        crate::VirPointerDomain::Allocation => ObligationStatus::Proven,
        crate::VirPointerDomain::Restricted(domain) => match exact_abstract_range(domain) {
            Some(domain) if domain.contains(object) => ObligationStatus::Proven,
            Some(_) => ObligationStatus::Refuted,
            None => ObligationStatus::Unknown,
        },
        crate::VirPointerDomain::Unknown => ObligationStatus::Unknown,
    };
    let mut statuses = vec![
        memory_access_status(pointer.memory_access(), pointee),
        domain,
    ];
    if !predicate {
        for bytes in shape.value_bytes() {
            let (Some(start), Some(end)) = (
                offset.checked_add(bytes.start_bytes()),
                offset.checked_add(bytes.end_bytes()),
            ) else {
                return ObligationStatus::Refuted;
            };
            let Ok(bytes) = ByteRange::new(start, end) else {
                return ObligationStatus::Refuted;
            };
            statuses.push(match allocation.initialization().classify(bytes) {
                InitializationClass::Initialized => ObligationStatus::Proven,
                InitializationClass::MaybeInitialized => ObligationStatus::Unknown,
                InitializationClass::Uninitialized => ObligationStatus::Refuted,
            });
            statuses.push(if allocation.valid_value_bytes().contains(bytes) {
                ObligationStatus::Proven
            } else if allocation.valid_value_bytes().is_precise() {
                ObligationStatus::Refuted
            } else {
                ObligationStatus::Unknown
            });
        }
    }
    statuses
        .into_iter()
        .fold(ObligationStatus::Proven, |combined, status| {
            combine_statuses([combined, status])
        })
}

/// Installs the existential owners guaranteed by one variant-free,
/// ownership-bearing aggregate ABI value into its caller-owned storage.
///
/// `false` means the storage pointer is not precise enough to attach the
/// payload. Callers retain an unknown/refuted obligation rather than gaining
/// ownership from an imprecise address.
#[derive(Clone, Copy)]
pub(in crate::verifier) struct AggregateEntryLoan {
    pub region: crate::VirBorrowRegionId,
    pub loan: crate::VirLoanId,
    pub initialized: bool,
}

pub(in crate::verifier) fn install_aggregate_parameter_payloads(
    state: &mut ResourceState,
    memory: &VirMemorySchema,
    storage_pointer: VirValueId,
    access: VirMemoryAccess,
    loans: &BTreeMap<ResourcePayloadKey, AggregateEntryLoan>,
    payload_id: impl FnMut(u32) -> AbstractAllocationId,
) -> Result<bool, TransferError> {
    let mut next = state.clone();
    if !install_aggregate_abi_payloads_inner(
        &mut next,
        memory,
        storage_pointer,
        access,
        loans,
        payload_id,
    )? {
        return Ok(false);
    }
    *state = next;
    Ok(true)
}

pub(in crate::verifier) fn install_aggregate_abi_payloads(
    state: &mut ResourceState,
    memory: &VirMemorySchema,
    storage_pointer: VirValueId,
    access: VirMemoryAccess,
    payload_id: impl FnMut(u32) -> AbstractAllocationId,
) -> Result<bool, TransferError> {
    // A type-only fallback can introduce existential owners, but cannot
    // invent a returned loan. Reference results need a checked body summary
    // mapping the actual input authority to its output carrier.
    if memory
        .object_shape(access)
        .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?
        .resource_leaves()
        .iter()
        .any(|leaf| leaf.kind() == VirPointerKind::Reference)
    {
        return Ok(false);
    }
    let mut next = state.clone();
    if !install_aggregate_abi_payloads_inner(
        &mut next,
        memory,
        storage_pointer,
        access,
        &BTreeMap::new(),
        payload_id,
    )? {
        return Ok(false);
    }
    *state = next;
    Ok(true)
}

fn install_aggregate_abi_payloads_inner(
    state: &mut ResourceState,
    memory: &VirMemorySchema,
    storage_pointer: VirValueId,
    access: VirMemoryAccess,
    loans: &BTreeMap<ResourcePayloadKey, AggregateEntryLoan>,
    mut payload_id: impl FnMut(u32) -> AbstractAllocationId,
) -> Result<bool, TransferError> {
    let shape = memory
        .object_shape(access)
        .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?;
    if !shape.variants().is_empty()
        || shape.resource_leaves().is_empty()
        || !shape.resource_leaves().iter().all(|leaf| {
            matches!(leaf.kind(), VirPointerKind::Own | VirPointerKind::Raw)
                || (leaf.kind() == VirPointerKind::Reference
                    && loans.contains_key(&ResourcePayloadKey::new(
                        leaf.bytes().start_bytes(),
                        leaf.access(),
                    )))
        })
        || shape
            .resource_leaves()
            .iter()
            .filter(|leaf| leaf.kind() == VirPointerKind::Reference)
            .count()
            != loans.len()
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
    let Some(object) = state.allocation(storage) else {
        return Ok(false);
    };
    if object.liveness() != crate::verifier::LivenessState::Live
        || base
            .checked_add(shape.size_bytes())
            .is_none_or(|end| end > object.size_bytes())
    {
        return Ok(false);
    }
    // Entry/fallback facts may fill an unknown or moved leaf, never overwrite
    // a live payload and discard the resource it still owns.
    for leaf in shape.resource_leaves() {
        let offset = base
            .checked_add(leaf.bytes().start_bytes())
            .ok_or(TransferError::InvalidDerivedRange)?;
        if matches!(
            object.resource_payload(ResourcePayloadKey::new(offset, leaf.access())),
            MovePathState::Available(_)
        ) {
            return Ok(false);
        }
    }
    let mut payloads = Vec::with_capacity(shape.resource_leaves().len());
    for (index, leaf) in shape.resource_leaves().iter().enumerate() {
        // Raw links are initialized address bytes, never owned/borrowed
        // capabilities. Keep canonical ordinals for the actual resources.
        if leaf.kind() == VirPointerKind::Raw {
            continue;
        }
        let index = u32::try_from(index).map_err(|_| TransferError::InvalidDerivedRange)?;
        let borrowed = loans.get(&ResourcePayloadKey::new(
            leaf.bytes().start_bytes(),
            leaf.access(),
        ));
        let pointee = if borrowed.is_some() {
            leaf.pointee_access()
        } else {
            owned_resource_pointee(memory, leaf.access())?
        };

        let layout = memory
            .layout(pointee.layout)
            .filter(|layout| layout.ty == pointee.ty && layout.size_bytes != 0)
            .ok_or(TransferError::InvalidValidatedMemoryAccess(pointee))?;
        let allocation_id = payload_id(index);
        let mut allocation = if borrowed.is_some() {
            AbstractAllocation::new_local(layout.size_bytes, layout.alignment)?
        } else {
            AbstractAllocation::new(VirRegionId::new(0), layout.size_bytes, layout.alignment)?
        };
        let whole =
            ByteRange::new(0, layout.size_bytes).map_err(|_| TransferError::InvalidDerivedRange)?;
        if let Some(binding) = borrowed {
            let referent = memory
                .object_shape(pointee)
                .map_err(|_| TransferError::InvalidValidatedMemoryAccess(pointee))?;
            if !referent.variants().is_empty()
                || referent
                    .resource_leaves()
                    .iter()
                    .any(|leaf| leaf.kind() != VirPointerKind::Raw)
            {
                return Err(TransferError::InvalidValidatedMemoryAccess(pointee));
            }
            if binding.initialized {
                for bytes in referent.value_bytes() {
                    let bytes = ByteRange::new(bytes.start_bytes(), bytes.end_bytes())
                        .map_err(|_| TransferError::InvalidDerivedRange)?;
                    allocation.mark_initialized(bytes)?;
                    allocation.mark_valid(bytes)?;
                }
            } else {
                allocation.forget_initialization(whole)?;
            }
        } else {
            allocation.mark_initialized(whole)?;
            allocation.mark_valid(whole)?;
        }
        state.introduce_allocation_instance(allocation_id, allocation)?;
        let provenance = AbstractProvenance::Known(allocation_id);
        let mut pointer = AbstractPointer::new(
            provenance,
            U64Interval::exact(0),
            GuaranteedAlignment::new(layout.alignment)
                .map_err(|_| TransferError::InvalidValidatedAlignment(layout.alignment))?,
        )
        .with_memory_access(Some(pointee));
        let mut permission = AbstractPermission::new(
            provenance,
            AbstractByteRange::Exact(whole),
            AccessPermission::Write,
            FreeCapability::Yes,
        );
        let offset = base
            .checked_add(leaf.bytes().start_bytes())
            .ok_or(TransferError::InvalidDerivedRange)?;
        if let Some(binding) = borrowed {
            let kind = if leaf.mutability() == crate::VirMutability::Const {
                VirLoanKind::Shared
            } else {
                VirLoanKind::Mutable
            };
            permission = AbstractPermission::new(
                provenance,
                AbstractByteRange::Exact(whole),
                if kind == VirLoanKind::Shared {
                    AccessPermission::Read
                } else {
                    AccessPermission::Write
                },
                FreeCapability::No,
            )
            .with_authority(PermissionAuthority::Loan(binding.loan));
            pointer = pointer
                .with_paths(crate::VirPointerPaths::root(pointee))
                .with_domain(crate::VirPointerDomain::Restricted(
                    AbstractByteRange::Exact(whole),
                ));
            let mut loan = AbstractLoan::new(
                provenance,
                whole,
                kind,
                binding.region,
                None,
                LoanActivity::Active,
            )
            .with_footprint(Some(crate::verifier::MemoryFootprint {
                provenance,
                access: pointee,
                stride_bytes: layout.size_bytes,
                range: AbstractByteRange::Exact(whole),
                envelope: whole,
            }));
            loan.add_stored_authority(storage, ResourcePayloadKey::new(offset, leaf.access()));
            state.define_loan(binding.loan, loan)?;
        }
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

#[cfg(test)]
mod aggregate_entry_tests {
    use super::*;

    #[test]
    fn reference_entry_payloads_own_stored_loans_without_free_or_implicit_initialization() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "reference-entry.nera",
            include_str!("../../../spec/cases/aggregate/owning-abi.nera"),
        ));
        let unit = output.vir().unwrap().as_unit();
        let access = unit
            .runtime
            .abis
            .functions
            .iter()
            .flat_map(|f| f.signature.parameters())
            .find_map(|b| match b.value() {
                crate::VirAbiValue::IndirectAggregate { access } => Some(*access),
                _ => None,
            })
            .unwrap();
        for mutability in [crate::VirMutability::Const, crate::VirMutability::Mutable] {
            // A memory-only schema fixture: no callable reference-field ABI is
            // admitted by changing these pointer kinds.
            let mut memory = unit.memory.clone();
            for ty in &mut memory.types {
                if let crate::VirMemoryTypeKind::Pointer {
                    kind,
                    mutability: mode,
                    ..
                } = &mut ty.kind
                    && *kind == VirPointerKind::Own
                {
                    *kind = VirPointerKind::Reference;
                    *mode = mutability;
                }
            }
            memory.assign_canonical_type_capabilities().unwrap();
            memory.validate().unwrap();
            let shape = memory.object_shape(access).unwrap();
            let storage = AbstractAllocationId::new(0);
            let pointer_id = VirValueId::new(0);
            let mut before = ResourceState::new();
            before
                .define_allocation(
                    storage,
                    AbstractAllocation::new_local(shape.size_bytes() + 8, shape.alignment())
                        .unwrap(),
                )
                .unwrap();
            before
                .define_value(
                    pointer_id,
                    AbstractValue::Pointer(
                        AbstractPointer::new(
                            AbstractProvenance::Known(storage),
                            U64Interval::exact(8),
                            GuaranteedAlignment::new(shape.alignment()).unwrap(),
                        )
                        .with_memory_access(Some(access)),
                    ),
                )
                .unwrap();
            let fields: BTreeMap<_, _> = shape
                .resource_leaves()
                .iter()
                .enumerate()
                .map(|(index, leaf)| {
                    (
                        ResourcePayloadKey::new(leaf.bytes().start_bytes(), leaf.access()),
                        AggregateEntryLoan {
                            region: crate::VirBorrowRegionId::new(index as u32),
                            loan: crate::vir::interface_loan_id(3 + index as u32),
                            initialized: index == 0,
                        },
                    )
                })
                .collect();
            assert_eq!(fields.len(), 2);
            let mut supplied = before.clone();
            assert!(
                install_aggregate_parameter_payloads(
                    &mut supplied,
                    &memory,
                    pointer_id,
                    access,
                    &fields,
                    |leaf| AbstractAllocationId::new(100 + leaf)
                )
                .unwrap()
            );
            for (index, (key, binding)) in fields.iter().enumerate() {
                let actual = ResourcePayloadKey::new(8 + key.offset_bytes(), key.access());
                let MovePathState::Available(payload) = supplied
                    .allocation(storage)
                    .unwrap()
                    .resource_payload(actual)
                else {
                    panic!("stored reference");
                };
                assert_eq!(
                    aggregate_abi_payload_status(
                        &supplied,
                        &memory,
                        actual.access(),
                        &payload,
                        Some((storage, actual)),
                        true
                    ),
                    ObligationStatus::Proven
                );
                assert_eq!(
                    aggregate_abi_payload_status(
                        &supplied,
                        &memory,
                        actual.access(),
                        &payload,
                        Some((storage, actual)),
                        false
                    )
                    .is_proven(),
                    index == 0
                );
                assert_eq!(
                    aggregate_abi_payload_status(
                        &supplied,
                        &memory,
                        actual.access(),
                        &payload,
                        None,
                        true
                    ),
                    ObligationStatus::Unknown
                );
                for mutation in 0..9 {
                    let mut corrupt = supplied.clone();
                    let mut bad = *payload;
                    let permission = payload.permission();
                    match mutation {
                        0 => corrupt
                            .loan_mut(binding.loan)
                            .unwrap()
                            .set_activity(LoanActivity::Ended),
                        1 => corrupt
                            .loan_mut(binding.loan)
                            .unwrap()
                            .add_authority(VirValueId::new(999)),
                        2 => {
                            bad = TypedResourcePayload::new(
                                payload.pointer(),
                                permission.with_authority(PermissionAuthority::Owner),
                            )
                        }
                        3 => {
                            bad = TypedResourcePayload::new(
                                payload.pointer(),
                                AbstractPermission::new(
                                    permission.provenance(),
                                    permission.range(),
                                    permission.access(),
                                    FreeCapability::Yes,
                                )
                                .with_authority(permission.authority()),
                            )
                        }
                        4 => {
                            bad = TypedResourcePayload::new(
                                payload.pointer(),
                                permission.with_availability(
                                    super::super::PermissionAvailability::Consumed,
                                ),
                            )
                        }
                        5 => {
                            bad = TypedResourcePayload::new(
                                payload.pointer(),
                                AbstractPermission::new(
                                    permission.provenance(),
                                    permission.range(),
                                    if permission.access() == AccessPermission::Read {
                                        AccessPermission::Write
                                    } else {
                                        AccessPermission::Read
                                    },
                                    FreeCapability::No,
                                )
                                .with_authority(permission.authority()),
                            )
                        }
                        6 => {
                            bad = TypedResourcePayload::new(
                                AbstractPointer::new(
                                    payload.pointer().provenance(),
                                    U64Interval::exact(1),
                                    GuaranteedAlignment::one(),
                                )
                                .with_memory_access(payload.pointer().memory_access()),
                                permission,
                            )
                        }
                        7 => {
                            corrupt
                                .loan_mut(binding.loan)
                                .unwrap()
                                .move_stored_authority(
                                    storage,
                                    actual,
                                    storage,
                                    ResourcePayloadKey::new(
                                        actual.offset_bytes() + 1,
                                        actual.access(),
                                    ),
                                );
                        }
                        8 => {
                            bad = TypedResourcePayload::new(
                                payload
                                    .pointer()
                                    .with_domain(crate::VirPointerDomain::Restricted(
                                        AbstractByteRange::Exact(ByteRange::new(0, 0).unwrap()),
                                    )),
                                permission,
                            )
                        }
                        _ => unreachable!(),
                    }
                    corrupt
                        .allocation_mut(storage)
                        .unwrap()
                        .set_resource_payload(actual, MovePathState::available(bad))
                        .unwrap();
                    assert_eq!(
                        aggregate_abi_payload_status(
                            &corrupt,
                            &memory,
                            actual.access(),
                            &bad,
                            Some((storage, actual)),
                            true
                        ),
                        ObligationStatus::Refuted,
                        "mutation {mutation}"
                    );
                }
                let pointee = payload.pointer().memory_access().unwrap();
                let allowed = BTreeSet::from([(storage, actual)]);
                let predicates = BTreeSet::from([AbstractAllocationId::new(100 + index as u32)]);
                let export_status = |state: &ResourceState, allowed: &BTreeSet<_>| {
                    crate::verifier::borrow_interface::stored::stored_export_status(
                        state,
                        &memory,
                        binding.loan,
                        pointee,
                        allowed,
                        &predicates,
                    )
                };
                assert_eq!(export_status(&supplied, &allowed), ObligationStatus::Proven);
                assert_eq!(
                    export_status(&supplied, &BTreeSet::new()),
                    ObligationStatus::Refuted
                );
                let wrong_leaf = BTreeSet::from([(
                    storage,
                    ResourcePayloadKey::new(actual.offset_bytes() + 1, actual.access()),
                )]);
                assert_eq!(
                    export_status(&supplied, &wrong_leaf),
                    ObligationStatus::Refuted
                );
                let mut duplicate = supplied.clone();
                let duplicate_storage = AbstractAllocationId::new(900);
                duplicate
                    .define_allocation(
                        duplicate_storage,
                        AbstractAllocation::new_local(shape.size_bytes() + 8, shape.alignment())
                            .unwrap(),
                    )
                    .unwrap();
                duplicate
                    .allocation_mut(duplicate_storage)
                    .unwrap()
                    .set_resource_payload(actual, MovePathState::available(*payload))
                    .unwrap();
                assert_eq!(
                    export_status(&duplicate, &allowed),
                    ObligationStatus::Refuted
                );
                let mut ended = supplied.clone();
                ended
                    .loan_mut(binding.loan)
                    .unwrap()
                    .set_activity(LoanActivity::Ended);
                assert_eq!(export_status(&ended, &allowed), ObligationStatus::Refuted);
                ended
                    .loan_mut(binding.loan)
                    .unwrap()
                    .remove_stored_authority(storage, actual);
                assert_eq!(export_status(&ended, &allowed), ObligationStatus::Refuted);
                ended
                    .allocation_mut(storage)
                    .unwrap()
                    .set_resource_payload(actual, MovePathState::Moved)
                    .unwrap();
                assert_eq!(
                    export_status(&ended, &BTreeSet::new()),
                    ObligationStatus::Proven
                );
                // A stale SSA carrier is still a leak even after the loan says Ended.
                ended
                    .define_value(
                        VirValueId::new(999),
                        AbstractValue::Permission(payload.permission()),
                    )
                    .unwrap();
                assert_eq!(
                    export_status(&ended, &BTreeSet::new()),
                    ObligationStatus::Refuted
                );
                assert_eq!(
                    payload.permission().authority(),
                    PermissionAuthority::Loan(binding.loan)
                );
                assert_eq!(payload.permission().free_capability(), FreeCapability::No);
                assert_eq!(
                    payload.permission().access(),
                    if mutability == crate::VirMutability::Const {
                        AccessPermission::Read
                    } else {
                        AccessPermission::Write
                    }
                );
                let loan = supplied.loan(binding.loan).unwrap();
                assert!(loan.authorities().contains(
                    &crate::verifier::resource::AbstractLoanAuthority::stored(storage, actual)
                ));
                let allocation = supplied
                    .allocation(AbstractAllocationId::new(100 + index as u32))
                    .unwrap();
                assert_eq!(
                    allocation.ownership(),
                    crate::verifier::OwnershipState::Unowned
                );
                assert_eq!(
                    allocation.initialization().initialized().is_empty(),
                    index != 0
                );
                if index != 0 {
                    assert!(allocation.initialization().uninitialized().is_empty());
                }
            }
            // Raw ABI fixture: canonical field IDs and actual hidden result
            // slots are checked without admitting this ABI to a validated unit.
            let function = unit
                .runtime
                .functions
                .iter()
                .find(|function| {
                    unit.runtime
                        .abis
                        .function(function.id)
                        .unwrap()
                        .signature
                        .parameters()
                        .len()
                        == 3
                })
                .unwrap();
            let abi = &unit.runtime.abis.function(function.id).unwrap().signature;
            let accesses = abi
                .parameters()
                .iter()
                .map(|b| b.value().access().unwrap())
                .collect::<Vec<_>>();
            let planned = crate::vir::plan_parameter_reference_entries(&memory, &accesses).unwrap();
            let regions = crate::VirBorrowEnvironment::from_tables(
                planned
                    .iter()
                    .enumerate()
                    .map(|(i, field)| crate::VirBorrowRegion {
                        id: crate::VirBorrowRegionId::new(i as u32),
                        owner: function.id,
                        origin: crate::VirBorrowRegionOrigin::ParameterField {
                            index: field.parameter,
                            slot: field.slot,
                        },
                        scope: crate::VirBorrowRegionScope::Function,
                        source_origin: crate::VirOriginId::new(0),
                    })
                    .collect(),
                vec![],
            );
            let mut inputs = vec![VirValueId::new(9998); abi.physical().parameters.len()];
            inputs[abi.results()[0].parameter_slots()[0] as usize] = pointer_id;
            let result = VirValueId::new(9997);
            let mut exported = supplied.clone();
            exported
                .define_value(
                    result,
                    AbstractValue::Permission(AbstractPermission::new(
                        AbstractProvenance::Known(storage),
                        AbstractByteRange::Exact(
                            ByteRange::new(8, 8 + shape.size_bytes()).unwrap(),
                        ),
                        AccessPermission::Write,
                        FreeCapability::No,
                    )),
                )
                .unwrap();
            let predicates = BTreeSet::from([
                AbstractAllocationId::new(100),
                AbstractAllocationId::new(101),
            ]);
            let check = |state: &ResourceState| {
                crate::verifier::borrow_interface::stored::field_export_statuses(
                    state,
                    function.id,
                    &regions,
                    abi,
                    &memory,
                    &inputs,
                    &[result],
                    &predicates,
                )
                .unwrap()
            };
            let exported_statuses = check(&exported);
            for binding in fields.values() {
                assert_eq!(exported_statuses[&binding.loan], ObligationStatus::Proven);
            }
            if let Some(AbstractValue::Permission(permission)) = exported.value_mut(result) {
                permission.mark_consumed();
            }
            let rejected = check(&exported);
            for binding in fields.values() {
                assert_eq!(rejected[&binding.loan], ObligationStatus::Refuted);
            }
            // Restore through the parameter's own ABI return slot, with no
            // hidden result destination available. This is not an address alias.
            let parameter = &abi.parameters()[1];
            let mut parameter_inputs = vec![VirValueId::new(9998); abi.physical().parameters.len()];
            parameter_inputs[parameter.parameter_slots()[0] as usize] = pointer_id;
            let mut parameter_results = vec![VirValueId::new(9998); abi.physical().results.len()];
            parameter_results[parameter.result_slots()[0] as usize] = result;
            let root_permission = AbstractPermission::new(
                AbstractProvenance::Known(storage),
                AbstractByteRange::Exact(ByteRange::new(8, 8 + shape.size_bytes()).unwrap()),
                AccessPermission::Write,
                FreeCapability::No,
            );
            let mut in_place = supplied.clone();
            in_place
                .define_value(result, AbstractValue::Permission(root_permission))
                .unwrap();
            let check_in_place = |state: &ResourceState| {
                crate::verifier::borrow_interface::stored::field_export_statuses(
                    state,
                    function.id,
                    &regions,
                    abi,
                    &memory,
                    &parameter_inputs,
                    &parameter_results,
                    &predicates,
                )
                .unwrap()
            };
            for binding in fields.values() {
                assert_eq!(
                    check_in_place(&in_place)[&binding.loan],
                    ObligationStatus::Proven
                );
            }
            for mutation in 0..5 {
                let bad_permission = match mutation {
                    0 => root_permission
                        .with_availability(super::super::PermissionAvailability::Consumed),
                    1 => AbstractPermission::new(
                        root_permission.provenance(),
                        AbstractByteRange::Exact(ByteRange::new(8, 9).unwrap()),
                        AccessPermission::Write,
                        FreeCapability::No,
                    ),
                    2 => AbstractPermission::new(
                        AbstractProvenance::Known(AbstractAllocationId::new(900)),
                        root_permission.range(),
                        AccessPermission::Write,
                        FreeCapability::No,
                    ),
                    3 => AbstractPermission::new(
                        root_permission.provenance(),
                        root_permission.range(),
                        AccessPermission::Read,
                        FreeCapability::No,
                    ),
                    4 => root_permission.with_authority(PermissionAuthority::Loan(
                        fields.values().next().unwrap().loan,
                    )),
                    _ => unreachable!(),
                };
                let mut bad = in_place.clone();
                *bad.value_mut(result).unwrap() = AbstractValue::Permission(bad_permission);
                for binding in fields.values() {
                    assert_eq!(
                        check_in_place(&bad)[&binding.loan],
                        ObligationStatus::Refuted
                    );
                }
            }
            let existing = supplied.clone();
            assert!(
                !install_aggregate_parameter_payloads(
                    &mut supplied,
                    &memory,
                    pointer_id,
                    access,
                    &fields,
                    |leaf| AbstractAllocationId::new(200 + leaf)
                )
                .unwrap()
            );
            assert_eq!(supplied, existing);
            for collision in [false, true] {
                let mut broken_fields = fields.clone();
                if !collision {
                    let first = broken_fields.values().next().unwrap().loan;
                    broken_fields.values_mut().last().unwrap().loan = first;
                }
                let mut broken = before.clone();
                assert!(
                    install_aggregate_parameter_payloads(
                        &mut broken,
                        &memory,
                        pointer_id,
                        access,
                        &broken_fields,
                        |leaf| if collision && leaf == 1 {
                            storage
                        } else {
                            AbstractAllocationId::new(100 + leaf)
                        }
                    )
                    .is_err()
                );
                assert_eq!(broken, before);
            }
        }
    }

    #[test]
    fn aggregate_payload_installation_is_atomic_and_preserves_existing_owners() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "aggregate-entry.nera",
            include_str!("../../../spec/cases/aggregate/owning-abi.nera"),
        ));
        let unit = output.vir().unwrap().as_unit();
        let access = unit
            .runtime
            .abis
            .functions
            .iter()
            .flat_map(|f| f.signature.parameters())
            .find_map(|b| match b.value() {
                crate::VirAbiValue::IndirectAggregate { access } => Some(*access),
                _ => None,
            })
            .unwrap();
        let layout = unit.memory.layout(access.layout).unwrap();
        let storage = AbstractAllocationId::new(0);
        let pointer = VirValueId::new(0);
        let make = |size| {
            let mut state = ResourceState::new();
            if let Some(size) = size {
                state
                    .define_allocation(
                        storage,
                        AbstractAllocation::new_local(size, layout.alignment).unwrap(),
                    )
                    .unwrap();
            }
            state
                .define_value(
                    pointer,
                    AbstractValue::Pointer(
                        AbstractPointer::new(
                            AbstractProvenance::Known(storage),
                            U64Interval::exact(0),
                            GuaranteedAlignment::new(layout.alignment).unwrap(),
                        )
                        .with_memory_access(Some(access)),
                    ),
                )
                .unwrap();
            state
        };
        for size in [None, Some(8)] {
            let mut state = make(size);
            let before = state.clone();
            assert!(
                !install_aggregate_abi_payloads(
                    &mut state,
                    &unit.memory,
                    pointer,
                    access,
                    |index| AbstractAllocationId::new(index + 1)
                )
                .unwrap()
            );
            assert_eq!(state, before);
        }
        let mut state = make(Some(layout.size_bytes));
        let before = state.clone();
        // The second allocation collides after the first was introduced.
        assert!(
            install_aggregate_abi_payloads(&mut state, &unit.memory, pointer, access, |_| {
                AbstractAllocationId::new(1)
            })
            .is_err()
        );
        assert_eq!(state, before);
        assert!(
            install_aggregate_abi_payloads(&mut state, &unit.memory, pointer, access, |index| {
                AbstractAllocationId::new(index + 1)
            })
            .unwrap()
        );
        let initialized = state.clone();
        assert!(
            !install_aggregate_abi_payloads(&mut state, &unit.memory, pointer, access, |index| {
                AbstractAllocationId::new(index + 10)
            })
            .unwrap()
        );
        assert_eq!(state, initialized);
    }
}

#[cfg(test)]
mod projected_length_snapshot_tests {
    use super::*;
    use crate::{AffineExpression, ByteSpan};

    #[test]
    fn closed_slice_length_refinement_preserves_body_identity_and_precision() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "projected-length-snapshot.nera",
            "fn main()->u64 {return 0;}
             fn cut(values:&[u64],end:usize)->&[u64] {return &values[0usize..end];}",
        ));
        let unit = output.vir().expect("slice projection source").as_unit();
        let abi = &unit
            .runtime
            .abis
            .functions
            .iter()
            .find(|f| f.signature.borrow_result().is_some())
            .unwrap()
            .signature;
        let arguments = (0..abi.physical().parameters.len())
            .map(|index| VirValueId::new(index as u32))
            .collect::<Vec<_>>();
        let results = abi
            .physical()
            .results
            .iter()
            .enumerate()
            .map(|(index, ty)| VirValue {
                id: VirValueId::new(100 + index as u32),
                ty: *ty,
            })
            .collect::<Vec<_>>();
        let end = arguments[abi.parameters()[1].parameter_slots()[0] as usize];
        let length = results[abi.results()[0].result_slots()[1] as usize].id;
        let mut state = ResourceState::new();
        state
            .define_value(end, AbstractValue::U64(U64Interval::new(2, 6).unwrap()))
            .unwrap();
        state.seed_parameter_origins(crate::VirFunctionId::new(1), &[end]);
        let origin = state.word_origin(end).unwrap();
        state
            .define_value(length, AbstractValue::U64(U64Interval::new(3, 5).unwrap()))
            .unwrap();
        state.set_word_origin(length, origin);
        state.set_word_expression(length, AffineExpression::identity(end));
        let mut transfer = TransferBuilder::new(
            state,
            ByteSpan::new(0, 1).unwrap(),
            &unit.memory,
            None,
            None,
        );
        let before = transfer.state.clone();
        transfer
            .refine_projected_result_length(abi, &arguments, &results)
            .unwrap();
        assert_eq!(transfer.state.value(length), before.value(length));
        assert_eq!(
            transfer.state.word_origin(length),
            before.word_origin(length)
        );
        assert_eq!(
            transfer.state.word_expression(length),
            before.word_expression(length)
        );
        // A narrower result also refines the actual equal entry coordinate;
        // this is a fact about the same immutable value, not a reassignment.
        assert_eq!(transfer.state.value(end), before.value(length));
        assert_eq!(transfer.state.word_origin(end), before.word_origin(end));

        let mut narrower = before.clone();
        *narrower.value_mut(length).unwrap() = AbstractValue::U64(U64Interval::new(0, 9).unwrap());
        narrower.set_word_origin(length, origin);
        narrower.set_word_expression(length, AffineExpression::identity(end));
        transfer.state = narrower;
        transfer
            .refine_projected_result_length(abi, &arguments, &results)
            .unwrap();
        assert_eq!(
            transfer.state.value(length),
            Some(&AbstractValue::U64(U64Interval::new(2, 6).unwrap()))
        );
        assert_eq!(transfer.state.word_origin(length), Some(origin));
        assert_eq!(
            transfer.state.word_expression(length),
            Some(AffineExpression::identity(end))
        );

        for value in [
            AbstractValue::U64(U64Interval::new(8, 9).unwrap()),
            AbstractValue::Bool(super::super::AbstractBool::Unknown),
        ] {
            transfer.state = before.clone();
            *transfer.state.value_mut(length).unwrap() = value;
            let inconsistent = transfer.state.clone();
            assert!(matches!(
                transfer.refine_projected_result_length(abi, &arguments, &results),
                Err(TransferError::InvalidDerivedRange)
            ));
            assert_eq!(
                transfer.state, inconsistent,
                "failed refinement must not repair a contradictory summary"
            );
        }
    }
}
