//! Project current scalar facts into the exact historical coordinates occurring
//! in the complete capture context. No pending package guarantee, address
//! identity or foreign frame is used to discover an endpoint. Pure affine
//! reasoning stays in facts.
use super::scalar_relations::ScalarDifference;
use super::*;
use crate::verifier::relation::state::RelationOperand;

#[derive(Default)]
pub(super) struct NumericInputs {
    pub differences: Vec<ScalarDifference>,
    pub booleans: Vec<(PredicateLogicValue, bool)>,
}

impl ResourceState {
    pub(super) fn predicate_numeric_inputs<'a>(
        &self,
        values: impl IntoIterator<Item = &'a PredicateLogicValue>,
        budget: &mut LogicBudget,
    ) -> Result<NumericInputs, PredicateError> {
        let mut groups = BTreeMap::<(WordType, InstanceScope), BTreeSet<ScalarOriginCell>>::new();
        for value in values {
            budget.charge(1).map_err(map_error)?;
            for leaf in value.value.capture_leaves(budget).map_err(map_error)? {
                let (ty, words) = match leaf {
                    LogicValue::Word(word) => (
                        match value.ty {
                            LogicType::U64 => WordType::U64,
                            LogicType::Usize => WordType::Usize,
                            _ => return Err(PredicateError::InvalidBinding),
                        },
                        vec![word],
                    ),
                    LogicValue::BoolComparison {
                        word_type,
                        left,
                        right,
                        ..
                    } => (*word_type, vec![left, right]),
                    _ => continue,
                };
                for word in words {
                    budget.charge(word.terms.len()).map_err(map_error)?;
                    for atom in word.terms.keys() {
                        if let ObservationAtom::Historical {
                            scope,
                            cell,
                            local: true,
                        } = atom
                        {
                            groups.entry((ty, *scope)).or_default().insert(*cell);
                        }
                    }
                }
            }
        }
        let mut result = NumericInputs::default();
        for ((word_type, scope), cells) in groups {
            let ty = word_type.logic_type();
            let mut inputs = BTreeMap::new();
            for (slot, origin) in &self.word_origins {
                budget.charge(1).map_err(map_error)?;
                if !origin
                    .terms()
                    .all(|(cell, coefficient)| coefficient == 0 || cells.contains(&cell))
                {
                    continue;
                }
                let Some(AbstractValue::U64(interval)) = self.value(*slot) else {
                    return Err(PredicateError::InvalidBinding);
                };
                let captured = observations::observed_scalar_word(
                    scope,
                    *interval,
                    Some(*origin),
                    ObservationAtom::Current {
                        scope,
                        value: *slot,
                    },
                )
                .map_err(map_error)?;
                if captured.terms.is_empty() {
                    continue;
                }
                let value = TypedLogicValue {
                    ty,
                    value: LogicValue::Word(captured),
                };
                // Import the actual range even without a difference-table edge.
                // All copies remain inputs, so conflicting copies cannot be
                // cherry-picked. This never names an unobserved root slot.
                let zero = TypedLogicValue {
                    ty,
                    value: LogicValue::Word(AffineValue::exact(0)),
                };
                result.differences.push((
                    value.clone(),
                    zero.clone(),
                    i128::from(interval.upper()),
                ));
                result
                    .differences
                    .push((zero, value.clone(), -i128::from(interval.lower())));
                inputs.insert(*slot, value);
                if result.differences.len() + result.booleans.len() > MAX_EXPRESSION_NODES {
                    return Err(PredicateError::Budget);
                }
            }
            result
                .differences
                .extend(self.predicate_scalar_differences(&inputs, budget)?);
            for (left, right) in self.relations.disequalities() {
                budget.charge(1).map_err(map_error)?;
                let resolve = |operand: RelationOperand| match operand {
                    RelationOperand::Constant(value) => Some(AffineValue::exact(value)),
                    RelationOperand::Value(slot) => match &inputs.get(&slot)?.value {
                        LogicValue::Word(word) => Some(word.clone()),
                        _ => None,
                    },
                };
                let (Some(a), Some(b)) = (resolve(*left), resolve(*right)) else {
                    continue;
                };
                result.booleans.push((
                    TypedLogicValue {
                        ty: LogicType::Bool,
                        value: LogicValue::BoolComparison {
                            word_type,
                            comparison: WordComparison::Equal,
                            left: a.clone(),
                            right: b.clone(),
                            negated: false,
                        },
                    },
                    false,
                ));
            }
            if result.differences.len() + result.booleans.len() > MAX_EXPRESSION_NODES {
                return Err(PredicateError::Budget);
            }
        }
        Ok(result)
    }
}
