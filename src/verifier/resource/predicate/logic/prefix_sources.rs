//! Qualify actual cursor sources for logical initialization counts. The pure
//! facts service decides numeric relations; this adapter cannot initialize
//! storage. Its caller must supply existing bytes or a checked contract import.
use super::*;
use crate::predicate_logic::facts::Comparison;

impl ResourceState {
    pub(super) fn predicate_prefix_relation(
        &self,
        captured: &CapturedPredicateLogic,
        comparison: Comparison,
        left: &AffineValue<ObservationAtom>,
        right: &AffineValue<ObservationAtom>,
        budget: &mut LogicBudget,
    ) -> Result<bool, PredicateError> {
        let queries = [left, right].map(|word| TypedLogicValue {
            ty: LogicType::Usize,
            value: LogicValue::Word(word.clone()),
        });
        let (facts, inputs) = self.established_constraint_facts_with_inputs(
            &captured.facts,
            &queries,
            captured.scope,
            budget,
        )?;
        let [Some(left), Some(right)] = inputs.as_slice() else {
            return Ok(false);
        };
        facts
            .entails(comparison, left, right, budget)
            .map_err(map_error)
    }

    /// Return an expression over actual scalar coordinates only after proving
    /// equality, never from a common range or a one-sided bound. No SSA is created.
    pub(super) fn predicate_prefix_source(
        &self,
        count: &AffineValue<ObservationAtom>,
        captured: &CapturedPredicateLogic,
        budget: &mut LogicBudget,
    ) -> Result<Option<AffineExpression>, PredicateError> {
        if count.lower == count.upper {
            return Ok(Some(AffineExpression::constant(count.lower)));
        }
        let scope = captured.scope.ok_or(PredicateError::InvalidBinding)?;
        let mut coordinates = Vec::new();
        // Preserve the old direct-coordinate path before spending the shared
        // relation budget on other equally bounded runtime scalars.
        for (id, value) in &self.values {
            budget.charge(1).map_err(map_error)?;
            if !matches!(value, AbstractValue::U64(_)) {
                continue;
            }
            let expression = AffineExpression::identity(*id);
            let actual = self.prefix_expression_value(expression, scope)?;
            coordinates.push((*id, actual.clone()));
            if let Some(true) = count.equal(&actual) {
                // Even direct matches must reconcile all retained copies.
                if self.predicate_prefix_relation(
                    captured,
                    Comparison::Equal,
                    count,
                    &actual,
                    budget,
                )? {
                    return Ok(Some(expression));
                }
            }
        }
        if let Some(expression) =
            self.composite_prefix_source(count, captured, &coordinates, budget)?
        {
            return Ok(Some(expression));
        }
        self.offset_prefix_source(count, captured, &coordinates, budget)
    }

    /// A saved relation may identify a hidden count as an actual cursor plus
    /// a fixed offset. All coordinates, including disjoint intervals, are
    /// eligible for the query; ranges alone never establish a fixed offset.
    fn offset_prefix_source(
        &self,
        count: &AffineValue<ObservationAtom>,
        captured: &CapturedPredicateLogic,
        coordinates: &[(VirValueId, AffineValue<ObservationAtom>)],
        budget: &mut LogicBudget,
    ) -> Result<Option<AffineExpression>, PredicateError> {
        for (id, actual) in coordinates {
            budget.charge(1).map_err(map_error)?;
            let queries = [count, actual].map(|word| TypedLogicValue {
                ty: LogicType::Usize,
                value: LogicValue::Word(word.clone()),
            });
            let (facts, inputs) = self.established_constraint_facts_with_inputs(
                &captured.facts,
                &queries,
                captured.scope,
                budget,
            )?;
            let [Some(count), Some(actual)] = inputs.as_slice() else {
                continue;
            };
            let offset = facts
                .exact_word_difference(count, actual, budget)
                .map_err(map_error)?;
            // Negative offsets need a signed initialization endpoint, which
            // this consumer does not support. Never drop or wrap the offset.
            let Some(offset) = offset.and_then(|n| u64::try_from(n).ok()) else {
                continue;
            };
            let expression = AffineExpression::identity(*id)
                .checked_add_constant(offset)
                .ok_or(PredicateError::UnprovedRepresentation)?;
            // This is a mathematical identity. The checked import adapter
            // derives actual input bounds before admitting machine arithmetic.
            return Ok(Some(expression));
        }
        Ok(None)
    }

    /// Immutable runtime coordinates are alternative descriptions, not
    /// independent induction variables. Algebra may select a bounded integral
    /// combination, but every residual atom must have an actual reader.
    fn composite_prefix_source(
        &self,
        count: &AffineValue<ObservationAtom>,
        captured: &CapturedPredicateLogic,
        coordinates: &[(VirValueId, AffineValue<ObservationAtom>)],
        budget: &mut LogicBudget,
    ) -> Result<Option<AffineExpression>, PredicateError> {
        let queries = std::iter::once(count)
            .chain(coordinates.iter().map(|(_, word)| word))
            .map(|word| TypedLogicValue {
                ty: LogicType::Usize,
                value: LogicValue::Word(word.clone()),
            })
            .collect::<Vec<_>>();
        let (facts, inputs) = self.established_constraint_facts_with_inputs(
            &captured.facts,
            &queries,
            captured.scope,
            budget,
        )?;
        let Some(Some(count)) = inputs.first() else {
            return Ok(None);
        };
        let sources = coordinates
            .iter()
            .zip(&inputs[1..])
            .filter_map(|((id, _), value)| match value {
                Some(TypedLogicValue {
                    value: LogicValue::Word(word),
                    ..
                }) => Some((*id, word.clone())),
                _ => None,
            })
            .collect::<Vec<_>>();
        if let Some(expression) =
            Self::prefix_coordinate_expression(&count.value, &sources, budget)?
        {
            return Ok(Some(expression));
        }
        // A hidden binder may equal a complete public expression rather than
        // one scalar or a scalar plus a fixed offset. Premise forms are merely
        // candidates: both real-coordinate mapping and equality are required.
        for candidate in facts
            .symbolic_word_candidates(LogicType::Usize, budget)
            .map_err(map_error)?
        {
            let Some(expression) =
                Self::prefix_coordinate_expression(&candidate.value, &sources, budget)?
            else {
                continue;
            };
            if facts
                .entails(Comparison::Equal, count, &candidate, budget)
                .map_err(map_error)?
            {
                return Ok(Some(expression));
            }
        }
        Ok(None)
    }

    fn prefix_coordinate_expression(
        value: &LogicValue<ObservationAtom, ResourceWitness>,
        sources: &[(VirValueId, AffineValue<ObservationAtom>)],
        budget: &mut LogicBudget,
    ) -> Result<Option<AffineExpression>, PredicateError> {
        use crate::predicate_logic::scalar_template::ScalarTemplate;
        let result = ScalarTemplate::capture_rebased(
            value,
            &[],
            sources,
            &mut |_, _, _| Err(LogicError::Unbound),
            budget,
        );
        let template = match result {
            Ok(template) => template,
            Err(LogicError::Unbound | LogicError::Overflow) => return Ok(None),
            Err(error) => return Err(map_error(error)),
        };
        let Some((constant, terms)) = template.word_shape() else {
            return Err(PredicateError::InvalidBinding);
        };
        // The initialization consumer has a smaller term language than pure
        // logic: at most two roots, nonnegative coefficients and addend. Do
        // not approximate a signed expression or an unrepresentable endpoint.
        let Ok(constant) = u64::try_from(constant) else {
            return Ok(None);
        };
        let mut expression = AffineExpression::constant(constant);
        for (id, coefficient) in terms {
            budget.charge(1).map_err(map_error)?;
            let Some(next) = u64::try_from(*coefficient)
                .ok()
                .and_then(|scale| AffineExpression::identity(*id).checked_scale(scale))
                .and_then(|term| expression.checked_add(term))
            else {
                return Ok(None);
            };
            expression = next;
        }
        Ok(Some(expression))
    }

    pub(super) fn prefix_expression_value(
        &self,
        expression: AffineExpression,
        scope: InstanceScope,
    ) -> Result<AffineValue<ObservationAtom>, PredicateError> {
        let mut word = AffineValue::exact(expression.addend());
        for (id, coefficient) in expression.terms().into_iter().flatten() {
            let Some(AbstractValue::U64(value)) = self.value(id) else {
                return Err(PredicateError::InvalidBinding);
            };
            // These are actual scalar coordinates, including singleton-valued
            // operands. Keep their identity so the source map and invalidation
            // protocol agree with captured logical parameters.
            let term = observations::observed_scalar_word(
                scope,
                *value,
                self.word_origin(id),
                ObservationAtom::Local { scope, value: id },
            )
            .and_then(|word| word.scale(coefficient))
            .map_err(map_error)?;
            word = word.add(&term).map_err(map_error)?;
        }
        Ok(word)
    }
}
