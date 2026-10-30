//! Closed-package compatibility at CFG joins. Pure bound-name normalization
//! lives in logic/identity, existential weakening in logic/abstraction. This
//! adapter checks both inputs and rechecks after the ordinary memory join.
use super::*;

pub(in crate::verifier::resource) struct PredicateJoin {
    pub instances: BTreeMap<PredicateHolder, PredicateInstance>,
    pub recheck: BTreeSet<PredicateHolder>,
}

impl ResourceState {
    pub(in crate::verifier::resource) fn join_predicates(
        &self,
        other: &Self,
    ) -> Result<PredicateJoin, ResourceJoinError> {
        self.merge_predicates(other, false)
    }

    pub(in crate::verifier::resource) fn widen_predicates(
        &self,
        other: &Self,
    ) -> Result<PredicateJoin, ResourceJoinError> {
        self.merge_predicates(other, true)
    }

    fn merge_predicates(
        &self,
        other: &Self,
        widen: bool,
    ) -> Result<PredicateJoin, ResourceJoinError> {
        let mismatch = || ResourceJoinError::PredicateStateMismatch;
        if self.predicates.len() > MAX_PREDICATE_INSTANCES
            || self.predicates.len() != other.predicates.len()
        {
            return Err(mismatch());
        }
        let flexible = self
            .predicates
            .iter()
            .filter_map(|(holder, instance)| {
                self.closed_join_package_valid(instance).then_some(*holder)
            })
            .collect();
        let matching = self
            .match_predicate_groups(other, &flexible)
            .map_err(|_| mismatch())?;
        let prefer_left = self.prefer_predicate_labels(other);
        let mut result = PredicateJoin {
            instances: BTreeMap::new(),
            recheck: BTreeSet::new(),
        };
        let mut budget = crate::predicate_logic::LogicBudget::default();
        for (holder, left) in &self.predicates {
            let right_holder = matching[holder];
            let right = &other.predicates[&right_holder];
            let output_holder = if prefer_left { *holder } else { right_holder };
            let relabeled = *holder != right_holder;
            // Renaming a ghost holder still requires a closed, valid package
            // on both paths; pending/open restoration obligations stay pinned.
            if relabeled
                && (!self.closed_join_package_valid(left)
                    || !other.closed_join_package_valid(right))
            {
                return Err(mismatch());
            }
            let mut joined = left.clone();
            joined.logical_local_aliases = right.logical_local_aliases.clone();
            if &joined == right {
                // Existing exact-identity path, including open packages and
                // outstanding restoration duties. Aliases may only be lost.
                joined
                    .logical_local_aliases
                    .retain(|id, snapshot| left.logical_local_aliases.get(id) == Some(snapshot));
                // Numeric widening can lose a valid representation even when
                // the binders already use the same namespace. Pending cleanup
                // states retain the previous exact-identity behavior.
                if self.closed_join_package_valid(left) && other.closed_join_package_valid(right) {
                    result.recheck.insert(output_holder);
                }
            } else {
                if left.definition != right.definition
                    || left.resources != right.resources
                    || !self.closed_join_package_valid(left)
                    || !other.closed_join_package_valid(right)
                {
                    return Err(mismatch());
                }
                let scopes = [
                    left.logic_scope.ok_or_else(mismatch)?,
                    right.logic_scope.ok_or_else(mismatch)?,
                ];
                // A scope referenced by another live package cannot be renamed
                // locally: that would silently identify independent binders.
                for (state, selected, scope) in
                    [(self, *holder, scopes[0]), (other, right_holder, scopes[1])]
                {
                    for (h, instance) in &state.predicates {
                        if *h != selected
                            && logic::mentions_scopes(instance, &[scope], &mut budget)
                                .map_err(|_| mismatch())?
                        {
                            return Err(mismatch());
                        }
                    }
                }
                // Keep one complete input namespace. Per-package minima can
                // merge independent binders when call order swaps their scopes.
                let target = if prefer_left { scopes[0] } else { scopes[1] };
                joined = self
                    .join_closed_logic(other, left, right, target, &mut budget, widen)
                    .map_err(|_| mismatch())?;
                result.recheck.insert(output_holder);
            }
            if result.instances.insert(output_holder, joined).is_some() {
                return Err(mismatch());
            }
        }
        Ok(result)
    }

    /// Identity-preserving normalization and existential weakening have
    /// different premises. In particular, a private foreign/SSA capture need
    /// not be identified with any current value in order to forget it.
    fn join_closed_logic(
        &self,
        other: &Self,
        left: &PredicateInstance,
        right: &PredicateInstance,
        target: crate::predicate_logic::InstanceScope,
        budget: &mut crate::predicate_logic::LogicBudget,
        widen: bool,
    ) -> Result<PredicateInstance, PredicateError> {
        let a = logic::normalize_closed_scope(left, target, budget);
        let b = logic::normalize_closed_scope(right, target, budget);
        if let (Ok(a), Ok(b)) = (&a, &b)
            && a == b
        {
            return Ok(a.clone());
        }
        // Budget/malformed arithmetic failures cannot turn into a proof by
        // retrying under a new budget. Only unavailable identity may be lost.
        for result in [&a, &b] {
            if let Err(error) = result
                && *error != PredicateError::InvalidBinding
            {
                return Err(error.clone());
            }
        }
        let mut a = left.clone();
        let mut b = right.clone();
        let parameters = if widen {
            self.widen_predicate_parameters(other, left, right, target, budget)?
        } else {
            self.join_predicate_parameters(other, left, right, target, budget)?
        };
        a.logical_parameters = parameters.values.clone();
        b.logical_parameters = parameters.values;
        // Admission of each original package happened before this adapter.
        // Drop private captures and extra facts, never reinterpret their names.
        a.logical_local_aliases = parameters.aliases.clone();
        b.logical_local_aliases = parameters.aliases;
        let mut a = self.abstract_predicate_logic_at_scope(&a, target, budget)?;
        let mut b = other.abstract_predicate_logic_at_scope(&b, target, budget)?;
        // Declaration capture may remember distinct immutable memory origins
        // on the two paths. Such extra facts are not a reason to identify the
        // origins or reject an otherwise representable package join. Keep only
        // common premises, then re-prove the representation in both inputs and
        // in the joined storage below. If a discarded fact was essential, the
        // checks fail and complete guarded cases remain necessary.
        let mut common = Vec::new();
        for fact in &a.logical_facts {
            for other in &b.logical_facts {
                budget.charge(1).map_err(logic::map_error)?;
                if fact == other {
                    common.push(fact.clone());
                    break;
                }
            }
        }
        a.logical_facts = common;
        b.logical_facts = a.logical_facts.clone();
        if a != b || !self.closed_join_package_valid(&a) || !other.closed_join_package_valid(&b) {
            // Preserve guarded cases if weakening loses a prefix certificate.
            return Err(PredicateError::UnprovedRepresentation);
        }
        Ok(a)
    }

    fn closed_join_package_valid(&self, instance: &PredicateInstance) -> bool {
        instance.folded
            && instance.opening_action.is_none()
            && instance.borrowed_by.is_empty()
            && instance
                .resources
                .iter()
                .all(|r| match (r.carrier, r.storage) {
                    (Some(carrier), None) => {
                        self.value(carrier)
                            == Some(&AbstractValue::Permission(
                                r.permission
                                    .with_availability(PermissionAvailability::Consumed),
                            ))
                    }
                    // Typed storage and actual loan authority are checked by the
                    // representation adapter below, never by a pointer comparison.
                    (None, Some(_)) => true,
                    _ => false,
                })
            && self.predicate_representation_valid(instance)
    }

    pub(in crate::verifier::resource) fn check_joined_predicates(
        &self,
        recheck: &BTreeSet<PredicateHolder>,
    ) -> Result<(), ResourceJoinError> {
        if recheck.iter().all(|holder| {
            self.predicates
                .get(holder)
                .is_some_and(|p| self.closed_join_package_valid(p))
        }) {
            Ok(())
        } else {
            Err(ResourceJoinError::PredicateStateMismatch)
        }
    }
}
