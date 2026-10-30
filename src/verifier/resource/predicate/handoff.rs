//! Scoped whole-allocation handoff. Each suspended lender remains in the state
//! across calls and CFG edges; only a matching closed loan token can restore it.
use super::*;
use crate::{VirLoanEffect, VirLoanId, VirLoanKind};

impl ResourceState {
    /// Every ancestry edge must retain its exact sealed restoration token.
    /// The loan count bounds malformed cycles as well as legitimate depth.
    pub(super) fn predicate_handoff_ancestor(
        &self,
        lender: &PredicateInstance,
        mut child: VirLoanId,
        definition: &PredicateDefinition,
        allocation: AbstractAllocationId,
    ) -> bool {
        for _ in 0..=self.loans.len() {
            let Some(loan) = self.loan(child) else {
                return false;
            };
            let frames = self
                .predicates
                .values()
                .filter(|p| {
                    p.folded
                        && p.borrowed_by.values().any(|loan| *loan == child)
                        && p.definition == *definition
                        && p.resources.iter().enumerate().any(|(index, r)| {
                            r.allocation == allocation && p.borrowed_by.get(&index) == Some(&child)
                        })
                })
                .collect::<Vec<_>>();
            let [frame] = frames.as_slice() else {
                return false;
            };
            let Some(r) = frame.resources.iter().find(|r| r.allocation == allocation) else {
                return false;
            };
            if loan.kind() != VirLoanKind::Mutable
                || !matches!(
                    loan.activity(),
                    LoanActivity::Active | LoanActivity::Suspended
                )
                || loan.provenance() != r.pointer.provenance()
                || loan.actual_range() != r.permission.range()
                || r.carrier.is_none_or(|c| {
                    self.value(c)
                        != Some(&AbstractValue::Permission(
                            r.permission
                                .with_availability(PermissionAvailability::Consumed),
                        ))
                })
            {
                return false;
            }
            let parent = match r.permission.authority() {
                PermissionAuthority::Owner if loan.parent().is_none() => None,
                PermissionAuthority::Loan(parent)
                    if loan.parent() == Some(parent)
                        && self.loan(parent).is_some_and(|p| {
                            p.activity() == LoanActivity::Suspended
                                && p.kind() == VirLoanKind::Mutable
                                && r.carrier.is_some_and(|c| p.has_value_authority(c))
                        }) =>
                {
                    Some(parent)
                }
                _ => return false,
            };
            if *frame == lender {
                return true;
            }
            let Some(parent) = parent else {
                return false;
            };
            child = parent;
        }
        false
    }

    pub(super) fn predicate_suspended_ancestor(
        &self,
        ancestor: VirLoanId,
        descendant: PermissionAuthority,
        definition: &PredicateDefinition,
        allocation: AbstractAllocationId,
    ) -> bool {
        let PermissionAuthority::Loan(descendant) = descendant else {
            return false;
        };
        self.predicates.values().any(|p| {
            p.resources.iter().any(|r| {
                r.allocation == allocation
                    && r.permission.authority() == PermissionAuthority::Loan(ancestor)
            }) && self.predicate_handoff_ancestor(p, descendant, definition, allocation)
        })
    }

    /// Find bindings only through actual SSA carriers. Equal addresses never
    /// stand in for a missing linear permission.
    fn predicate_instance_bindings(
        &self,
        instance: &PredicateInstance,
    ) -> Result<Vec<PredicateBinding>, PredicateError> {
        instance
            .resources
            .iter()
            .map(|r| {
                let permission = r.carrier.ok_or(PredicateError::MissingAuthority)?;
                let pointer = self
                    .values
                    .iter()
                    .find_map(|(id, v)| (*v == AbstractValue::Pointer(r.pointer)).then_some(*id))
                    .ok_or(PredicateError::MissingAuthority)?;
                Ok(PredicateBinding {
                    pointer,
                    permission,
                })
            })
            .collect()
    }

    /// Check the suspended group's actual representation under its current
    /// child authorities. This view neither exposes nor manufactures access.
    fn predicate_lender_valid(&self, instance: &PredicateInstance) -> bool {
        let mut view = instance.clone();
        view.borrowed_by.clear();
        for (&index, &id) in &instance.borrowed_by {
            let Some(loan) = self.loan(id) else {
                return false;
            };
            if loan.activity() == LoanActivity::Ended {
                if !loan.authorities().is_empty() {
                    return false;
                }
                continue;
            }
            if loan.activity() != LoanActivity::Active || loan.authorities().len() != 1 {
                return false;
            }
            let Some(resource) = view.resources.get_mut(index) else {
                return false;
            };
            let Some((&carrier, permission)) =
                self.values.iter().find_map(|(carrier, value)| match value {
                    AbstractValue::Permission(p)
                        if loan.has_value_authority(*carrier)
                            && p.authority() == PermissionAuthority::Loan(id) =>
                    {
                        Some((carrier, *p))
                    }
                    _ => None,
                })
            else {
                return false;
            };
            if permission.provenance() != resource.permission.provenance()
                || permission.range() != resource.permission.range()
            {
                return false;
            }
            resource.carrier = Some(carrier);
            resource.permission = permission.with_availability(PermissionAvailability::Available);
        }
        self.predicate_representation_valid(&view)
    }

    /// Open only the selected member in a formation view. Other members stay
    /// sealed, and already formed loans remain attached to the lender.
    pub(in crate::verifier) fn prepare_predicate_borrow(
        &mut self,
        effect: VirLoanEffect,
        size: u64,
    ) -> Option<PredicateHolder> {
        if effect.kind != VirLoanKind::Mutable
            || effect.range.start_bytes != 0
            || effect.range.end_bytes != size
        {
            return None;
        }
        let (holder, instance, index) = self.predicates.iter().find_map(|(holder, p)| {
            if !p.folded {
                return None;
            }
            p.resources.iter().enumerate().find_map(|(index, r)| {
                (r.carrier == Some(effect.source_permission)
                    && !p.borrowed_by.contains_key(&index)
                    && p.definition.resources[index].size_bytes == size
                    && match (r.permission.authority(), effect.parent) {
                        (PermissionAuthority::Owner, None) => true,
                        (PermissionAuthority::Loan(parent), Some(expected))
                            if parent == expected =>
                        {
                            self.loan(parent).is_some_and(|l| {
                                l.activity() == LoanActivity::Active
                                    && l.kind() == VirLoanKind::Mutable
                                    && l.has_value_authority(effect.source_permission)
                            })
                        }
                        _ => false,
                    })
                .then_some((*holder, p, index))
            })
        })?;
        if self.predicates.len() >= MAX_PREDICATE_INSTANCES
            || !self.predicate_lender_valid(instance)
            || instance.resources.iter().any(|r| {
                r.carrier.is_none_or(|c| {
                    self.value(c)
                        != Some(&AbstractValue::Permission(
                            r.permission
                                .with_availability(PermissionAvailability::Consumed),
                        ))
                })
            })
        {
            return None;
        }
        let resource = &instance.resources[index];
        if self.value(effect.source_pointer) != Some(&AbstractValue::Pointer(resource.pointer))
            || self.value(effect.source_permission)
                != Some(&AbstractValue::Permission(
                    resource
                        .permission
                        .with_availability(PermissionAvailability::Consumed),
                ))
        {
            return None;
        }
        self.values.insert(
            effect.source_permission,
            AbstractValue::Permission(resource.permission),
        );
        self.predicates.get_mut(&holder)?.folded = false;
        Some(holder)
    }

    /// Forming a group is incremental, but a child predicate is published only
    /// once every member has its real, distinct loan authority.
    pub(in crate::verifier) fn seal_predicate_borrow(
        &mut self,
        holder: PredicateHolder,
        loan: VirLoanId,
        binding: PredicateBinding,
    ) -> Result<(), PredicateError> {
        let mut next = self.clone();
        let owner = next
            .predicates
            .get(&holder)
            .ok_or(PredicateError::MissingHolder)?;
        if owner.folded || owner.borrowed_by.values().any(|id| *id == loan) {
            return Err(PredicateError::InvalidBinding);
        }
        let actual = next.loan(loan).ok_or(PredicateError::MissingAuthority)?;
        let index = owner
            .resources
            .iter()
            .position(|r| r.pointer.provenance() == actual.provenance())
            .ok_or(PredicateError::InvalidBinding)?;
        if owner.borrowed_by.contains_key(&index) {
            return Err(PredicateError::Borrowed);
        }
        let resource = &owner.resources[index];
        let carrier = resource.carrier.ok_or(PredicateError::MissingAuthority)?;
        let parent = match resource.permission.authority() {
            PermissionAuthority::Owner => None,
            PermissionAuthority::Loan(parent)
                if next.loan(parent).is_some_and(|l| {
                    l.activity() == LoanActivity::Suspended && l.has_value_authority(carrier)
                }) =>
            {
                Some(parent)
            }
            _ => return Err(PredicateError::MissingAuthority),
        };
        if next.value(carrier) != Some(&AbstractValue::Permission(resource.permission))
            || actual.activity() != LoanActivity::Active
            || actual.kind() != VirLoanKind::Mutable
            || actual.parent() != parent
            || actual.actual_range() != resource.permission.range()
            || !actual.has_value_authority(binding.permission)
            || next.value(binding.pointer) != Some(&AbstractValue::Pointer(resource.pointer))
            || next.value(binding.permission)
                != Some(&AbstractValue::Permission(
                    AbstractPermission::new(
                        resource.pointer.provenance(),
                        resource.permission.range(),
                        AccessPermission::Write,
                        FreeCapability::No,
                    )
                    .with_authority(PermissionAuthority::Loan(loan)),
                ))
        {
            return Err(PredicateError::MissingAuthority);
        }
        let consumed = resource
            .permission
            .with_availability(PermissionAvailability::Consumed);
        next.values
            .insert(carrier, AbstractValue::Permission(consumed));
        let owner = next.predicates.get_mut(&holder).unwrap();
        owner.folded = true;
        owner.borrowed_by.insert(index, loan);
        if owner.borrowed_by.len() == owner.resources.len() {
            let mut child_view = owner.clone();
            let definition = owner.definition.clone();
            for (index, r) in child_view.resources.iter_mut().enumerate() {
                let id = child_view.borrowed_by[&index];
                let l = next.loan(id).ok_or(PredicateError::MissingAuthority)?;
                if l.activity() != LoanActivity::Active || l.authorities().len() != 1 {
                    return Err(PredicateError::Borrowed);
                }
                let (carrier, permission) = next
                    .values
                    .iter()
                    .find_map(|(c, v)| match v {
                        AbstractValue::Permission(p)
                            if l.has_value_authority(*c)
                                && p.authority() == PermissionAuthority::Loan(id) =>
                        {
                            Some((*c, *p))
                        }
                        _ => None,
                    })
                    .ok_or(PredicateError::MissingAuthority)?;
                r.carrier = Some(carrier);
                r.permission = permission;
            }
            let bindings = next.predicate_instance_bindings(&child_view)?;
            let child = next.available_predicate_holder()?;
            child_view.borrowed_by.clear();
            next.predicate_fold_impl(
                &definition,
                definition.module,
                child,
                &bindings,
                &Default::default(),
                false,
                Some(&child_view),
            )?;
        }
        *self = next;
        Ok(())
    }

    /// A closed child is opened once for the group's first return. Later
    /// members remain real loans, checked again at each return boundary.
    pub(in crate::verifier) fn prepare_predicate_restore(
        &mut self,
        loan: VirLoanId,
        binding: PredicateBinding,
    ) -> Result<Option<PredicateHolder>, PredicateError> {
        let parents = self
            .predicates
            .iter()
            .filter(|(_, p)| p.borrowed_by.values().any(|id| *id == loan))
            .map(|(h, _)| *h)
            .collect::<Vec<_>>();
        let [holder] = parents.as_slice() else {
            return if parents.is_empty() {
                Ok(None)
            } else {
                Err(PredicateError::AliasedAuthority)
            };
        };
        if !matches!(self.value(binding.permission), Some(AbstractValue::Permission(p)) if p.authority() == PermissionAuthority::Loan(loan))
            || self.loan(loan).is_none_or(|l| {
                l.activity() != LoanActivity::Active
                    || l.authorities().len() != 1
                    || !l.has_value_authority(binding.permission)
            })
        {
            return Err(PredicateError::MissingAuthority);
        }
        let mut next = self.clone();
        let children = next
            .predicates
            .iter()
            .filter(|(h, p)| {
                **h != *holder
                    && p.resources
                        .iter()
                        .any(|r| r.permission.authority() == PermissionAuthority::Loan(loan))
            })
            .map(|(_, p)| p.clone())
            .collect::<Vec<_>>();
        if let [child] = children.as_slice() {
            if !child.folded || !child.borrowed_by.is_empty() {
                return Err(PredicateError::OpenBoundary);
            }
            let bindings = next.predicate_instance_bindings(child)?;
            let parent = &next.predicates[holder];
            if child.definition != parent.definition
                || child.resources.len() != parent.resources.len()
                || child
                    .resources
                    .iter()
                    .zip(&parent.resources)
                    .any(|(a, b)| a.allocation != b.allocation || a.pointer != b.pointer)
            {
                return Err(PredicateError::InvalidBinding);
            }
            next.export_predicate_interface(&child.definition, &bindings)?;
            // The checked child owns the current existential package. Transfer
            // that logical state while the parent's real carriers stay consumed
            // until every restoration edge has ended.
            let parent = next.predicates.get_mut(holder).unwrap();
            parent.logic_scope = child.logic_scope;
            parent.logical_parameters = child.logical_parameters.clone();
            parent.logical_witnesses = child.logical_witnesses.clone();
            parent.logical_facts = child.logical_facts.clone();
            parent.logical_initialization = child.logical_initialization.clone();
            parent.logical_local_aliases = child.logical_local_aliases.clone();
            parent.opening_action = None;
        } else if !children.is_empty() {
            return Err(PredicateError::AliasedAuthority);
        }
        if !matches!(next.value(binding.permission), Some(AbstractValue::Permission(p)) if p.availability() == PermissionAvailability::Available)
        {
            return Err(PredicateError::MissingAuthority);
        }
        if !next.predicate_lender_valid(&next.predicates[holder]) {
            return Err(PredicateError::UnprovedRepresentation);
        }
        *self = next;
        Ok(Some(*holder))
    }

    /// The original carriers stay consumed throughout the group. Ending a
    /// member retires only that restoration edge, never another member's loan.
    pub(in crate::verifier) fn restore_predicate_lender(
        &mut self,
        holder: PredicateHolder,
        loan: VirLoanId,
    ) -> Result<(), PredicateError> {
        let mut next = self.clone();
        if next
            .loan(loan)
            .is_none_or(|l| l.activity() != LoanActivity::Ended || !l.authorities().is_empty())
        {
            return Err(PredicateError::Borrowed);
        }
        let parent = next
            .predicates
            .get_mut(&holder)
            .ok_or(PredicateError::MissingHolder)?;
        let index = parent
            .borrowed_by
            .iter()
            .find_map(|(index, id)| (*id == loan).then_some(*index))
            .ok_or(PredicateError::InvalidBinding)?;
        if !parent.folded {
            return Err(PredicateError::InvalidBinding);
        }
        parent.borrowed_by.remove(&index);
        let parent = &next.predicates[&holder];
        if !next.predicate_lender_valid(parent)
            || parent.resources.iter().any(|r| {
                r.carrier.is_none_or(|carrier| {
                    next.value(carrier)
                        != Some(&AbstractValue::Permission(
                            r.permission
                                .with_availability(PermissionAvailability::Consumed),
                        ))
                })
            })
        {
            return Err(PredicateError::UnprovedRepresentation);
        }
        *self = next;
        Ok(())
    }

    /// Restore only existing lender edges after checked, actual loan ends.
    /// A child predicate must already have been exported or retired: ending a
    /// loan cannot silently discard its sealed instance or cleanup obligation.
    pub(in crate::verifier) fn restore_ended_predicate_lenders(
        &mut self,
        ended: &BTreeSet<VirLoanId>,
    ) -> Result<(), PredicateError> {
        if ended.is_empty() {
            return Ok(());
        }
        let mut next = self.clone();
        for loan in ended {
            if next
                .loan(*loan)
                .is_none_or(|l| l.activity() != LoanActivity::Ended || !l.authorities().is_empty())
                || next.predicates.values().any(|p| {
                    p.resources
                        .iter()
                        .any(|r| r.permission.authority() == PermissionAuthority::Loan(*loan))
                })
            {
                return Err(PredicateError::Borrowed);
            }
            let parents = next
                .predicates
                .iter()
                .filter(|(_, p)| p.borrowed_by.values().any(|id| id == loan))
                .map(|(h, _)| *h)
                .collect::<Vec<_>>();
            if parents.len() > 1 {
                return Err(PredicateError::AliasedAuthority);
            }
            for parent in parents {
                next.restore_predicate_lender(parent, *loan)?;
            }
        }
        *self = next;
        Ok(())
    }
}
