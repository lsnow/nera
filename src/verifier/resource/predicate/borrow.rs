//! Loans remain live when their owner is sealed. No predicate operation ends a
//! loan or recreates its authority. Writes/call effects must preserve the closed
//! representation; opening the owner still waits for all loans to end.
use super::*;

impl ResourceState {
    pub(super) fn predicate_loans_compatible(
        &self,
        definition: &PredicateDefinition,
        resource: usize,
        provenance: AbstractProvenance,
        owned_loan: Option<crate::VirLoanId>,
    ) -> Result<(), PredicateError> {
        if !self.loan_precision_losses.is_empty() {
            return Err(PredicateError::Borrowed);
        }
        let whole = ByteRange::new(0, definition.resources[resource].size_bytes)
            .map_err(|_| PredicateError::InvalidDefinition)?;
        for (id, loan) in &self.loans {
            if loan.activity() == LoanActivity::Ended {
                continue;
            }
            if loan.provenance() == AbstractProvenance::Unknown {
                return Err(PredicateError::Borrowed);
            }
            if loan.provenance() != provenance {
                continue;
            }
            let range = match loan.actual_range() {
                AbstractByteRange::Exact(range) => range,
                AbstractByteRange::Symbolic { .. } if owned_loan != Some(*id) => {
                    // The envelope is only a conservative exclusion check for
                    // invariant cells. It never replaces actual loan authority.
                    let footprint = loan.footprint().ok_or(PredicateError::Borrowed)?;
                    if footprint.provenance != provenance {
                        return Err(PredicateError::Borrowed);
                    }
                    footprint.envelope
                }
                _ => return Err(PredicateError::Borrowed),
            };
            if !whole.contains(range) {
                return Err(PredicateError::Borrowed);
            }
            if owned_loan == Some(*id) {
                continue;
            }
            if let (Some(descendant), AbstractProvenance::Known(allocation)) =
                (owned_loan, provenance)
                && self.predicate_suspended_ancestor(
                    *id,
                    PermissionAuthority::Loan(descendant),
                    definition,
                    allocation,
                )
            {
                continue;
            }
            // A suspended view still reserves its full range. Check it and
            // every descendant against invariant cells below; retaining the
            // predicate does not reactivate the parent or grant an access.
            if !matches!(
                loan.activity(),
                LoanActivity::Active | LoanActivity::Suspended
            ) {
                return Err(PredicateError::Borrowed);
            }
            // A writable view cannot expose a constrained scalar or a canonical
            // projected witness cell. Read-only views cannot invalidate either
            // the scalar or initialized bytes.
            if loan.kind() != crate::VirLoanKind::Shared
                && (definition.scalar_constraints.iter().any(|bound| {
                    bound.resource == resource
                        && ByteRange::from_start_and_length(bound.offset_bytes, 8)
                            .is_ok_and(|cell| cell.overlaps(range))
                }) || definition
                    .logic
                    .constraints
                    .iter()
                    .chain(definition.projected_witnesses.iter().filter_map(|index| {
                        definition
                            .logic
                            .existentials
                            .get(*index as usize)?
                            .default
                            .as_ref()
                    }))
                    .chain(definition.logical_prefixes.iter().filter_map(|prefix| {
                        match &prefix.count {
                            crate::PredicatePrefixCount::Logical(expression) => Some(expression),
                            _ => None,
                        }
                    }))
                    .any(|constraint| {
                        constraint.nodes.iter().any(|node| {
                            let crate::predicate_logic::LogicNodeKind::Observe {
                                resource: index,
                                offset,
                                ..
                            } = node.kind
                            else {
                                return false;
                            };
                            let width = if node.ty == crate::predicate_logic::LogicType::Bool {
                                1
                            } else {
                                8
                            };
                            index as usize == resource
                                && ByteRange::from_start_and_length(offset, width)
                                    .is_ok_and(|cell| cell.overlaps(range))
                        })
                    }))
            {
                return Err(PredicateError::Borrowed);
            }
        }
        Ok(())
    }

    // Sealing a suspended parent retains its capability, not memory access.
    // The caller also checks every live loan against the representation.
    pub(super) fn predicate_loan_alias(
        &self,
        value: VirValueId,
        permission: AbstractPermission,
    ) -> bool {
        let PermissionAuthority::Loan(id) = permission.authority() else {
            return false;
        };
        permission.availability() == PermissionAvailability::Available
            && permission.free_capability() == FreeCapability::No
            && self.loan(id).is_some_and(|loan| {
                matches!(
                    loan.activity(),
                    LoanActivity::Active | LoanActivity::Suspended
                ) && permission.access()
                    == if loan.kind() == crate::VirLoanKind::Shared {
                        AccessPermission::Read
                    } else {
                        AccessPermission::Write
                    }
                    && loan.provenance() == permission.provenance()
                    && loan.has_value_authority(value)
                    && loan.actual_range() == permission.range()
            })
    }

    /// Observations only. Never import facts from the predicate declaration.
    pub(in crate::verifier) fn closed_predicate_checks(&self) -> Vec<(PredicateHolder, bool)> {
        self.predicates
            .iter()
            .filter(|(_, p)| p.folded && p.borrowed_by.is_empty())
            .map(|(holder, p)| (*holder, self.predicate_representation_valid(p)))
            .collect()
    }

    pub(super) fn predicate_representation_valid(&self, instance: &PredicateInstance) -> bool {
        if !instance.borrowed_by.is_empty() {
            return false;
        }
        self.predicate_representation_valid_for_release(instance, false)
    }

    // Releasing a borrowed logical wrapper neither ends its loan nor creates
    // owner authority. A local loan may already have ended through normal NLL.
    pub(super) fn predicate_representation_valid_for_release(
        &self,
        instance: &PredicateInstance,
        releasing: bool,
    ) -> bool {
        if instance.dropping {
            return false;
        }
        for (index, (resource, shape)) in instance
            .resources
            .iter()
            .zip(&instance.definition.resources)
            .enumerate()
        {
            if let Some((storage, key)) = resource.storage
                && (resource.carrier.is_some() || !instance.folded
                    || self.allocation(storage).is_none_or(|a| a.liveness() != LivenessState::Live
                        || !matches!(a.resource_payload(key), MovePathState::Available(payload)
                            if payload.pointer() == resource.pointer && payload.permission() == resource.permission.with_availability(PermissionAvailability::Consumed))))
            { return false; }
            let Some(allocation) = self.allocation(resource.allocation) else {
                return false;
            };
            if let PermissionAuthority::Loan(id) = resource.permission.authority()
                && self.loan(id).is_none_or(|loan| {
                    (!matches!(
                        loan.activity(),
                        LoanActivity::Active | LoanActivity::Suspended
                    ) && !(releasing && loan.activity() == LoanActivity::Ended))
                        || loan.provenance() != resource.pointer.provenance()
                        || loan.kind() != crate::VirLoanKind::Mutable
                        || loan.actual_range() != resource.permission.range()
                        || if releasing && loan.activity() == LoanActivity::Ended {
                            !loan.authorities().is_empty()
                        } else if instance.folded {
                            match (resource.carrier, resource.storage) {
                                (Some(carrier), None) => !loan.has_value_authority(carrier),
                                (None, Some((storage, key))) => !loan.authorities().contains(
                                    &crate::verifier::resource::AbstractLoanAuthority::stored(
                                        storage, key,
                                    ),
                                ),
                                _ => true,
                            }
                        } else {
                            false
                        }
                })
            {
                return false;
            }

            if self
                .predicate_fields_valid(&instance.definition, index, resource.allocation)
                .is_err()
                || allocation.liveness() != LivenessState::Live
                || (resource.permission.authority() == PermissionAuthority::Owner
                    && allocation.ownership() != OwnershipState::Owned)
                || allocation.size_bytes() != shape.size_bytes
                || shape.initialized.iter().any(|range| {
                    allocation.initialization().classify(*range) != InitializationClass::Initialized
                        || !allocation.valid_value_bytes().contains(*range)
                })
                || self
                    .predicate_loans_compatible(
                        &instance.definition,
                        index,
                        resource.pointer.provenance(),
                        match resource.permission.authority() {
                            PermissionAuthority::Loan(id) => Some(id),
                            _ => None,
                        },
                    )
                    .is_err()
            {
                return false;
            }
        }
        for bound in &instance.definition.scalar_constraints {
            let Ok(range) = ByteRange::from_start_and_length(bound.offset_bytes, 8) else {
                return false;
            };
            let scalar = self
                .allocation(instance.resources[bound.resource].allocation)
                .and_then(|allocation| allocation.scalar_content(range, bound.access));
            if !matches!(scalar, Some(AbstractValue::U64(value)) if value.lower() >= bound.lower && value.upper() <= bound.upper)
            {
                return false;
            }
        }
        self.predicate_logic_valid(instance)
            && instance
                .definition
                .initialized_prefixes
                .iter()
                .all(|(index, prefix)| {
                    self.allocation(instance.resources[*index].allocation)
                        .is_some_and(|a| a.heap_prefix_valid(*prefix))
                })
    }
}

impl ResourceState {
    /// A disposable logical observation view. Export only actual closed tokens;
    /// this state must never replace the execution state or grant runtime access.
    pub(in crate::verifier) fn predicate_observation_view(&self) -> Self {
        let mut view = self.clone();
        for holder in self.predicates.keys() {
            // This adapter checks the actual closed representation and exact
            // consumed carriers. It neither opens logical binders nor ends a
            // child loan; each observation must separately prove disjointness.
            let _ = view.expose_closed_predicate_carriers(*holder);
        }
        view
    }
}
