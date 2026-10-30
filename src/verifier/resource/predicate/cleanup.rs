//! Destruction tracks actual stored obligations, separately from logical facts.
use super::*;

impl ResourceState {
    pub(in crate::verifier) fn predicate_cleanup_checks(&self) -> Vec<(PredicateHolder, bool)> {
        self.predicates
            .iter()
            .filter(|(_, p)| p.dropping)
            .map(|(h, p)| (*h, self.predicate_cleanup_valid(p)))
            .collect()
    }

    pub(super) fn predicate_drop_ready(&self, p: &PredicateInstance) -> bool {
        p.borrowed_by.is_empty()
            && if p.dropping {
                self.predicate_cleanup_valid(p)
            } else {
                p.folded && self.predicate_representation_valid(p)
            }
    }

    pub(super) fn predicate_resource_retired(&self, r: &SealedResource) -> bool {
        let location_released = match (r.carrier, r.storage) {
            (Some(carrier), None) => {
                self.value(carrier)
                    == Some(&AbstractValue::Permission(
                        r.permission
                            .with_availability(PermissionAvailability::Consumed),
                    ))
            }
            (None, Some((storage, key))) => {
                self.allocation(storage)
                    .is_some_and(|a| match a.resource_payload(key) {
                        MovePathState::Moved => true,
                        // Reusing a retired field does not make the new resource a
                        // member of the old group. Unknown cannot establish retirement.
                        MovePathState::Available(payload) => {
                            payload.permission().authority() != r.permission.authority()
                                || payload.permission().provenance() != r.permission.provenance()
                        }
                        MovePathState::Unknown => false,
                    })
            }
            _ => false,
        };
        if !location_released {
            return false;
        }
        match r.permission.authority() {
            PermissionAuthority::Owner => self
                .allocation(r.allocation)
                .is_some_and(|a| a.liveness() == LivenessState::Dead),
            PermissionAuthority::Loan(id) => self
                .loan(id)
                .is_some_and(|l| l.activity() == LoanActivity::Ended && l.authorities().is_empty()),
            PermissionAuthority::Unknown => false,
        }
    }

    /// This checks responsibility conservation only. A partially destroyed
    /// group is never a valid logical representation and supplies no facts.
    pub(super) fn predicate_cleanup_valid(&self, p: &PredicateInstance) -> bool {
        if !p.dropping || p.folded || !p.borrowed_by.is_empty() {
            return false;
        }
        let mut locations = BTreeSet::new();
        p.resources.iter().all(|r| {
            let (location, present) = match (r.carrier, r.storage) {
                (Some(carrier), None) => (AbstractLoanAuthority::value(carrier),
                    self.value(carrier) == Some(&AbstractValue::Permission(r.permission.with_availability(PermissionAvailability::Consumed)))),
                (None, Some((storage, key))) => (AbstractLoanAuthority::stored(storage, key),
                    self.allocation(storage).is_some_and(|a| a.liveness() == LivenessState::Live
                        && matches!(a.resource_payload(key), MovePathState::Available(payload)
                            if payload.pointer() == r.pointer && payload.permission() == r.permission.with_availability(PermissionAvailability::Consumed)))),
                _ => return false,
            };
            if !locations.insert(location) { return false; }
            if self.predicate_resource_retired(r) { return true; }
            if !present || self.allocation(r.allocation).is_none_or(|a| a.liveness() != LivenessState::Live) { return false; }
            match r.permission.authority() {
                PermissionAuthority::Owner => !self.loans.values().any(|l| {
                    l.activity() != LoanActivity::Ended
                        && (l.provenance() == r.pointer.provenance()
                            || l.provenance() == AbstractProvenance::Unknown)
                }),
                PermissionAuthority::Loan(id) => self.loan(id).is_some_and(|loan| {
                    loan.activity() == LoanActivity::Active
                        && loan.provenance() == r.pointer.provenance()
                        && loan.actual_range() == r.permission.range()
                        && loan.authorities() == &BTreeSet::from([location])
                        && !self.loans.values().any(|child| {
                            child.parent() == Some(id) && child.activity() != LoanActivity::Ended
                        })
                }),
                PermissionAuthority::Unknown => false,
            }
        })
    }

    /// Admit implicit destruction of an actual sealed SSA owner. Unlike free,
    /// this consumes a representation member without exposing it for use.
    pub(in crate::verifier) fn predicate_ssa_owner_to_drop(
        &self,
        carrier: VirValueId,
        pointer: AbstractPointer,
        permission: AbstractPermission,
    ) -> Option<(PredicateHolder, AbstractPermission)> {
        let mut matches = self
            .predicates
            .iter()
            .filter(|(_, p)| p.resources.iter().any(|r| r.carrier == Some(carrier)));
        let (holder, group) = matches.next()?;
        if matches.next().is_some()
            || !self.predicate_drop_ready(group)
            || group.resources.iter().any(|r| {
                r.permission.authority() != PermissionAuthority::Owner
                    || self.loans.values().any(|loan| {
                        loan.activity() != LoanActivity::Ended
                            && (loan.provenance() == r.pointer.provenance()
                                || loan.provenance() == AbstractProvenance::Unknown)
                    })
            })
        {
            return None;
        }
        let resource = group
            .resources
            .iter()
            .find(|r| r.carrier == Some(carrier))?;
        (resource.storage.is_none()
            && resource.pointer == pointer
            && permission
                == resource
                    .permission
                    .with_availability(PermissionAvailability::Consumed))
        .then_some((*holder, resource.permission))
    }

    /// A loan moved out of one field can end while sibling responsibilities
    /// remain stored. Ordinary all-SSA restoration keeps its existing protocol.
    pub(in crate::verifier) fn predicate_ssa_borrow_to_drop(
        &self,
        carrier: VirValueId,
        pointer: AbstractPointer,
        permission: AbstractPermission,
    ) -> Option<PredicateHolder> {
        let mut matches = self
            .predicates
            .iter()
            .filter(|(_, p)| p.resources.iter().any(|r| r.carrier == Some(carrier)));
        let (holder, group) = matches.next()?;
        if matches.next().is_some()
            || !self.predicate_drop_ready(group)
            || (!group.dropping && group.resources.iter().all(|r| r.storage.is_none()))
        {
            return None;
        }
        if !self.predicate_borrow_carriers_valid(group) {
            return None;
        }
        let resource = group
            .resources
            .iter()
            .find(|r| r.carrier == Some(carrier))?;
        (resource.storage.is_none()
            && resource.pointer == pointer
            && permission
                == resource
                    .permission
                    .with_availability(PermissionAvailability::Consumed))
        .then_some(*holder)
    }

    pub(super) fn predicate_borrow_carriers_valid(&self, group: &PredicateInstance) -> bool {
        let mut seen = BTreeSet::new();
        group.resources.iter().all(|resource| {
            if group.dropping && self.predicate_resource_retired(resource) {
                return true;
            }
            let PermissionAuthority::Loan(id) = resource.permission.authority() else {
                return false;
            };
            let location = match (resource.carrier, resource.storage) {
                (Some(value), None) => AbstractLoanAuthority::value(value),
                (None, Some((storage, key))) => AbstractLoanAuthority::stored(storage, key),
                _ => return false,
            };
            seen.insert(location)
                && self.loan(id).is_some_and(|loan| {
                    loan.activity() == LoanActivity::Active
                        && loan.authorities() == &BTreeSet::from([location])
                        && !self.loans.values().any(|child| {
                            child.parent() == Some(id) && child.activity() != LoanActivity::Ended
                        })
                })
        })
    }

    /// Commit one actual drop without forgetting remaining members. The
    /// final member retires the group and restores lenders as one transaction.
    pub(in crate::verifier) fn advance_dropped_predicate(
        &mut self,
        holder: PredicateHolder,
    ) -> bool {
        let mut next = self.clone();
        let Some(p) = next.predicates.get_mut(&holder) else {
            return false;
        };
        if (!p.folded && !p.dropping) || !p.borrowed_by.is_empty() {
            return false;
        }
        p.dropping = true;
        p.folded = false;
        p.logic_scope = None;
        p.opening_action = None;
        p.logical_witnesses.clear();
        p.logical_parameters.clear();
        p.logical_facts.clear();
        p.logical_initialization.clear();
        p.logical_local_aliases.clear();
        if !next.predicate_cleanup_valid(&next.predicates[&holder]) {
            return false;
        }
        if next.predicates[&holder]
            .resources
            .iter()
            .all(|r| next.predicate_resource_retired(r))
            && !next.finish_dropped_predicate(holder)
        {
            return false;
        }
        *self = next;
        true
    }

    pub(in crate::verifier) fn finish_dropped_predicate(
        &mut self,
        holder: PredicateHolder,
    ) -> bool {
        let mut next = self.clone();
        let Some(p) = next.predicates.get(&holder) else {
            return false;
        };
        if (!p.folded && !p.dropping)
            || !p.borrowed_by.is_empty()
            || !p
                .resources
                .iter()
                .all(|r| next.predicate_resource_retired(r))
        {
            return false;
        }
        let ended = p
            .resources
            .iter()
            .filter_map(|r| match r.permission.authority() {
                PermissionAuthority::Loan(id) => Some(id),
                _ => None,
            })
            .collect();
        next.predicates.remove(&holder);
        if next.restore_ended_predicate_lenders(&ended).is_err() {
            return false;
        }
        *self = next;
        true
    }
}
