//! Predicate packages in induction frames. Existential forgetting is separate
//! from actual resource preservation and from the pure consequence service.
use super::*;

impl ResourceState {
    /// Admit the entry before havoc. A written sealed package must be refolded
    /// by this loop; every backedge will recheck the same declaration, public
    /// parameters and real resource carriers. Open packages retain their epoch.
    pub(in crate::verifier::resource) fn inherit_loop_predicate_frame(
        &mut self,
        entry: &Self,
        modified: &BTreeSet<AbstractAllocationId>,
        repacked: &BTreeSet<PredicateHolder>,
    ) -> bool {
        if !self.predicates.is_empty()
            || repacked.len() > MAX_PREDICATE_INSTANCES
            || entry.predicates.iter().any(|(holder, p)| {
                !p.borrowed_by.is_empty()
                    || p.folded
                        && (!entry.sealed_loop_predicate_valid(p)
                            || p.resources.iter().any(|r| modified.contains(&r.allocation))
                                && !repacked.contains(holder))
            })
        {
            return false;
        }
        self.predicates = entry.predicates.clone();
        self.next_predicate_scope = self.next_predicate_scope.max(entry.next_predicate_scope);
        for instance in self.predicates.values_mut() {
            instance.logical_local_aliases.clear();
        }
        true
    }

    /// Restore only declared representation guarantees after scalar havoc.
    /// This is a provisional induction premise, justified by actual entry and
    /// backedge checks. The enclosing frame constructor commits atomically.
    pub(in crate::verifier::resource) fn assume_loop_predicate_representation(
        &mut self,
        entry: &Self,
        modified: &BTreeSet<AbstractAllocationId>,
        repacked: &BTreeSet<PredicateHolder>,
    ) -> Result<(), PredicateError> {
        for (holder, instance) in &entry.predicates {
            if !instance.folded
                || !instance
                    .resources
                    .iter()
                    .any(|r| modified.contains(&r.allocation))
            {
                continue;
            }
            if !repacked.contains(holder) || !entry.sealed_loop_predicate_valid(instance) {
                return Err(PredicateError::UnprovedRepresentation);
            }
            let allocations: Vec<_> = instance.resources.iter().map(|r| r.allocation).collect();
            self.assume_predicate_scalar_bounds(&instance.definition, &allocations)?;
            // Keep the relation to the stored count, never initialize its upper
            // envelope. Writes to the count/elements still invalidate this
            // certificate through the ordinary transfer semantics.
            for (index, prefix) in &instance.definition.initialized_prefixes {
                self.allocations
                    .get_mut(
                        allocations
                            .get(*index)
                            .ok_or(PredicateError::InvalidDefinition)?,
                    )
                    .ok_or(PredicateError::MissingAuthority)?
                    .certify_heap_prefix(*prefix);
            }
        }
        Ok(())
    }

    fn sealed_loop_predicate_carriers_valid(&self, instance: &PredicateInstance) -> bool {
        instance.folded
            && instance.borrowed_by.is_empty()
            && instance.resources.iter().all(|resource| {
                resource.storage.is_none()
                    && resource.carrier.is_some_and(|carrier| {
                        self.value(carrier)
                            == Some(&AbstractValue::Permission(
                                resource
                                    .permission
                                    .with_availability(PermissionAvailability::Consumed),
                            ))
                    })
            })
    }

    pub(super) fn sealed_loop_predicate_valid(&self, instance: &PredicateInstance) -> bool {
        self.sealed_loop_predicate_carriers_valid(instance)
            && self.predicate_representation_valid(instance)
    }

    /// Only packages refolded by this loop are abstracted. Untouched packages
    /// keep their existing precision; open packages keep their exact epoch.
    #[cfg(test)]
    pub(in crate::verifier) fn abstract_loop_predicates(
        &mut self,
        repacked: &BTreeSet<PredicateHolder>,
    ) -> Result<(), PredicateError> {
        self.abstract_loop_predicates_from_frame(
            None,
            &BTreeSet::new(),
            repacked,
            &Default::default(),
        )
    }

    #[cfg(test)]
    pub(in crate::verifier) fn abstract_loop_predicates_after_havoc(
        &mut self,
        entry: &Self,
        modified: &BTreeSet<AbstractAllocationId>,
        repacked: &BTreeSet<PredicateHolder>,
    ) -> Result<(), PredicateError> {
        self.abstract_loop_predicates_after_havoc_with_parameters(
            entry,
            modified,
            repacked,
            &Default::default(),
        )
    }

    pub(in crate::verifier) fn abstract_loop_predicates_after_havoc_with_parameters(
        &mut self,
        entry: &Self,
        modified: &BTreeSet<AbstractAllocationId>,
        repacked: &BTreeSet<PredicateHolder>,
        parameters: &LoopPredicateParameters,
    ) -> Result<(), PredicateError> {
        self.abstract_loop_predicates_from_frame(Some(entry), modified, repacked, parameters)
    }

    fn abstract_loop_predicates_from_frame(
        &mut self,
        entry: Option<&Self>,
        modified: &BTreeSet<AbstractAllocationId>,
        repacked: &BTreeSet<PredicateHolder>,
        parameters: &LoopPredicateParameters,
    ) -> Result<(), PredicateError> {
        if repacked.len() > MAX_PREDICATE_INSTANCES {
            return Err(PredicateError::Budget);
        }
        let mut instances = self.predicates.clone();
        // Observation origins and logical abstraction commit together. A later
        // representation/budget failure cannot leave fresh cell identities.
        let mut candidate = self.clone();
        let mut next = self.next_predicate_scope;
        for (holder, instance) in &mut instances {
            if !repacked.contains(holder) || !instance.folded {
                continue;
            }
            let written = instance
                .resources
                .iter()
                .any(|r| modified.contains(&r.allocation));
            let admitted = if written {
                entry.is_some_and(|entry| {
                    entry.predicates.get(holder).is_some_and(|before| {
                        let mut comparable = instance.clone();
                        comparable.logical_local_aliases = before.logical_local_aliases.clone();
                        comparable == *before
                            && entry.sealed_loop_predicate_valid(before)
                            && self.sealed_loop_predicate_carriers_valid(instance)
                    })
                })
            } else {
                self.sealed_loop_predicate_valid(instance)
            };
            if !admitted {
                return Err(PredicateError::UnprovedRepresentation);
            }
            let mut budget = crate::predicate_logic::LogicBudget::default();
            if instance.logic_scope.is_some() {
                candidate.seed_loop_predicate_observations(instance, next, &mut budget)?;
                candidate.bind_loop_predicate_parameters(
                    *holder,
                    instance,
                    parameters,
                    crate::predicate_logic::InstanceScope {
                        declaration: instance.definition.id.get(),
                        instance: next,
                        opening: 0,
                    },
                    &mut budget,
                )?;
            }
            candidate.abstract_loop_predicate_logic(instance, &mut next, &mut budget)?;
            // Hidden initialization counts still need actual byte/prefix
            // evidence. Existential abstraction must not initialize an envelope.
            if !candidate.sealed_loop_predicate_valid(instance) {
                return Err(PredicateError::UnprovedRepresentation);
            }
        }
        candidate.predicates = instances;
        candidate.next_predicate_scope = next;
        *self = candidate;
        Ok(())
    }

    pub(in crate::verifier::resource) fn loop_predicates_match_with_parameters(
        &self,
        expected: &Self,
        repacked: &BTreeSet<PredicateHolder>,
        parameters: &LoopPredicateParameters,
    ) -> bool {
        if repacked.len() > MAX_PREDICATE_INSTANCES
            || expected.predicates.len() > MAX_PREDICATE_INSTANCES
            || self.predicates.len() != expected.predicates.len()
        {
            return false;
        }
        let flexible = expected
            .predicates
            .iter()
            .filter_map(|(holder, instance)| {
                (repacked.contains(holder) && instance.folded).then_some(*holder)
            })
            .collect();
        let Ok(matching) = expected.match_predicate_groups(self, &flexible) else {
            return false;
        };
        expected.predicates.iter().all(|(holder, before)| {
            if !repacked.contains(holder) || !before.folded {
                let Some(after) = self.predicates.get(holder) else {
                    return false;
                };
                // Alias loss is precision loss, not a new resource phase.
                let mut comparable = after.clone();
                comparable.logical_local_aliases = before.logical_local_aliases.clone();
                return comparable == *before;
            }
            // The common resource adapter establishes a full, unique group
            // mapping. Loop entailment of the parameters remains separate.
            let after = &self.predicates[&matching[holder]];
            if !after.borrowed_by.is_empty()
                || !before.borrowed_by.is_empty()
                || after.logical_parameters.len() != before.logical_parameters.len()
                || !self.sealed_loop_predicate_valid(after)
                || !expected.sealed_loop_predicate_valid(before)
            {
                return false;
            }
            let mut budget = crate::predicate_logic::LogicBudget::default();
            after
                .logical_parameters
                .iter()
                .zip(&before.logical_parameters)
                .enumerate()
                .all(|(position, (a, b))| {
                    let actual;
                    let b = if let Some(expression) = parameters.expression(*holder, position) {
                        let Ok(value) = self.loop_parameter_actual(after, expression, &mut budget)
                        else {
                            return false;
                        };
                        actual = value;
                        &actual
                    } else {
                        b
                    };
                    a.ty == b.ty
                        && self.predicate_argument_equality(
                            after,
                            a.clone(),
                            b.clone(),
                            &mut budget,
                        ) == Ok(true)
                })
        })
    }
}
