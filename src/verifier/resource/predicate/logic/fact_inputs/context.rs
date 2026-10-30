//! A query-local source catalog. The immutable state borrow prevents facts
//! surviving a store, CFG transition, call, or opening change. This adapter
//! qualifies identities; arithmetic and propositions remain in pure Facts.
use super::*;

pub(in crate::verifier::resource::predicate::logic) struct QualifiedFacts<'a> {
    state: &'a ResourceState,
    scope: Option<InstanceScope>,
    saved: &'a [PredicateConstraintFact],
    raw: Vec<PredicateLogicValue>,
    prepared: Vec<Option<PredicateLogicValue>>,
    initialized: bool,
    failed: Option<PredicateError>,
    pub(in crate::verifier::resource::predicate::logic) facts: Facts,
}

impl<'a> QualifiedFacts<'a> {
    pub(in crate::verifier::resource::predicate::logic) fn is_initialized(&self) -> bool {
        self.initialized
    }
    pub(in crate::verifier::resource::predicate::logic) fn new(
        state: &'a ResourceState,
        scope: Option<InstanceScope>,
        saved: &'a [PredicateConstraintFact],
    ) -> Self {
        Self {
            state,
            scope,
            saved,
            raw: vec![],
            prepared: vec![],
            initialized: false,
            failed: None,
            facts: Facts::new(),
        }
    }

    pub(in crate::verifier::resource::predicate::logic) fn matches(
        &self,
        state: &ResourceState,
        scope: InstanceScope,
        saved: &[PredicateConstraintFact],
    ) -> bool {
        std::ptr::eq(self.state, state)
            && self.scope == Some(scope)
            && std::ptr::eq(self.saved, saved)
    }

    fn intern(
        &mut self,
        value: &PredicateLogicValue,
        observations: &mut Vec<(PredicateLogicValue, bool)>,
        budget: &mut LogicBudget,
    ) -> Result<usize, PredicateError> {
        // Equality includes nominal type, complete origin, scope and bounds.
        // Equal ranges alone never intern independent observations.
        for (id, previous) in self.raw.iter().enumerate() {
            budget.charge(1).map_err(map_error)?;
            if previous == value {
                return Ok(id);
            }
        }
        budget.charge(1).map_err(map_error)?;
        if self.raw.len() >= MAX_SUBSTITUTION_NODES {
            return Err(PredicateError::Budget);
        }
        let prepared =
            self.state
                .qualify_logic_fact_value(value.clone(), self.scope, observations, budget)?;
        let id = self.raw.len();
        self.raw.push(value.clone());
        self.prepared.push(prepared);
        Ok(id)
    }

    pub(in crate::verifier::resource::predicate::logic) fn queries(
        &mut self,
        queries: &[PredicateLogicValue],
        budget: &mut LogicBudget,
    ) -> Result<Vec<Option<PredicateLogicValue>>, PredicateError> {
        budget.charge(1).map_err(map_error)?;
        if let Some(error) = &self.failed {
            return Err(error.clone());
        }
        let result = self.prepare(queries, budget);
        if let Err(error) = &result {
            self.failed = Some(error.clone());
        }
        result
    }

    fn prepare(
        &mut self,
        queries: &[PredicateLogicValue],
        budget: &mut LogicBudget,
    ) -> Result<Vec<Option<PredicateLogicValue>>, PredicateError> {
        if self.saved.len() > MAX_CONSTRAINTS {
            return Err(PredicateError::Budget);
        }
        let before = self.raw.len();
        let mut observations = Vec::new();
        let mut snapshots = Vec::new();
        if !self.initialized {
            for fact in self.saved {
                let mut leaves = Vec::new();
                for (node, value) in &fact.leaves {
                    let id = self.intern(value, &mut observations, budget)?;
                    leaves.push((*node, self.prepared[id].clone()));
                }
                snapshots.push((&fact.expression, leaves));
            }
        }
        let mut indices = Vec::new();
        for value in queries {
            indices.push(self.intern(value, &mut observations, budget)?);
        }
        let mut differences = Vec::new();
        if self.raw.len() != before {
            // New operands can expose relations to earlier operands. Project
            // the complete unique catalog, never only the newly added suffix.
            let numeric = self
                .state
                .predicate_numeric_inputs(self.prepared.iter().flatten(), budget)?;
            observations.extend(numeric.booleans);
            differences = numeric.differences;
        }
        if !self.initialized {
            let batch = snapshots
                .iter()
                .map(|(expression, leaves)| (*expression, leaves.as_slice()))
                .collect::<Vec<_>>();
            self.facts
                .extend_inputs(&observations, &differences, &batch, budget)
                .map_err(map_error)?;
            self.initialized = true;
        } else {
            self.facts
                .extend_observations(&observations, &differences, budget)
                .map_err(map_error)?;
        }
        Ok(indices
            .into_iter()
            .map(|id| self.prepared[id].clone())
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scope() -> InstanceScope {
        InstanceScope {
            declaration: 0,
            instance: 0,
            opening: 0,
        }
    }
    fn word(binder: u32) -> PredicateLogicValue {
        TypedLogicValue {
            ty: LogicType::Usize,
            value: LogicValue::Word(
                AffineValue::variable(
                    ObservationAtom::Existential {
                        scope: scope(),
                        binder,
                    },
                    0,
                    10,
                )
                .unwrap(),
            ),
        }
    }

    #[test]
    fn source_catalog_reuses_only_complete_identities_in_one_immutable_state() {
        let state = ResourceState::new();
        let before = state.clone();
        let mut context = QualifiedFacts::new(&state, Some(scope()), &[]);
        let inputs = [word(0), word(1)];
        let prepared = context
            .queries(&inputs, &mut LogicBudget::default())
            .unwrap();
        assert_ne!(prepared[0], prepared[1]);
        assert_eq!(
            context.facts.entails(
                crate::predicate_logic::facts::Comparison::Equal,
                prepared[0].as_ref().unwrap(),
                prepared[1].as_ref().unwrap(),
                &mut LogicBudget::default()
            ),
            Ok(false)
        );
        // A warm lookup does not repeat source qualification or solve facts.
        let mut budget = LogicBudget::default();
        budget.charge(MAX_SUBSTITUTION_NODES - 4).unwrap();
        assert_eq!(context.queries(&inputs, &mut budget).unwrap(), prepared);
        assert!(context.matches(&state, scope(), &[]));
        assert!(!context.matches(&before, scope(), &[]));
        assert!(!context.matches(
            &state,
            InstanceScope {
                opening: 1,
                ..scope()
            },
            &[]
        ));
        assert_eq!(state, before);
    }

    #[test]
    fn failed_preparation_cannot_resume_a_partial_catalog_with_a_fresh_budget() {
        let state = ResourceState::new();
        let mut context = QualifiedFacts::new(&state, Some(scope()), &[]);
        let mut budget = LogicBudget::default();
        budget.charge(MAX_SUBSTITUTION_NODES - 1).unwrap();
        assert_eq!(
            context.queries(&[word(0)], &mut budget),
            Err(PredicateError::Budget)
        );
        assert_eq!(
            context.queries(&[word(0)], &mut LogicBudget::default()),
            Err(PredicateError::Budget)
        );
        // A separate invocation still performs its own complete preparation.
        let mut fresh = QualifiedFacts::new(&state, Some(scope()), &[]);
        assert!(
            fresh
                .queries(&[word(0)], &mut LogicBudget::default())
                .is_ok()
        );
    }
}
