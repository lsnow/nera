//! Bounded Boolean identities over already qualified capture leaves. This is
//! syntax normalization, not source alignment or a solver: it never substitutes
//! equal ranges/truths for named inputs, drops leaves, or chooses a branch.
use super::scalar_template::ScalarTemplate;
use super::*;

type Value<A, R> = LogicValue<A, R>;

impl<A: Ord + Clone, R: Clone> LogicValue<A, R> {
    pub(crate) fn canonical_boolean_capture(
        &self,
        budget: &mut LogicBudget,
    ) -> Result<Self, LogicError> {
        if !self.is_boolean() {
            return Err(LogicError::TypeMismatch);
        }
        // Validate the original complete tree before normalization can change
        // its depth. Even an annihilating constant cannot hide an invalid leaf.
        self.capture_leaves(budget)?;
        let value = normalize(self, false, budget)?;
        value.capture_leaves(budget)?;
        Ok(value)
    }
}

fn normalize<A: Ord + Clone, R: Clone>(
    value: &Value<A, R>,
    invert: bool,
    budget: &mut LogicBudget,
) -> Result<Value<A, R>, LogicError> {
    budget.charge(1)?;
    Ok(match value {
        Value::Bool(v) => Value::Bool(v.map(|b| b ^ invert)),
        Value::BoolAtom {
            atom,
            negated,
            known,
        } => Value::BoolAtom {
            atom: atom.clone(),
            negated: *negated ^ invert,
            known: *known,
        },
        Value::BoolComparison {
            word_type,
            comparison,
            left,
            right,
            negated,
        } => {
            for word in [left, right] {
                budget.charge(word.terms.len())?;
                if word.terms.len() > MAX_LINEAR_TERMS {
                    return Err(LogicError::Budget);
                }
                if word.lower > word.upper {
                    return Err(LogicError::InvalidNode);
                }
            }
            // Equality is symmetric. Ordering keys exclude interval precision.
            let swap = *comparison == WordComparison::Equal
                && (&left.constant, &left.terms) > (&right.constant, &right.terms);
            Value::BoolComparison {
                word_type: *word_type,
                comparison: *comparison,
                left: if swap { right.clone() } else { left.clone() },
                right: if swap { left.clone() } else { right.clone() },
                negated: *negated ^ invert,
            }
        }
        Value::BoolBinary {
            operation,
            left,
            right,
            negated,
        } => {
            let invert = invert ^ *negated;
            let (operation, child_invert, result_invert) = match (*operation, invert) {
                (BooleanOperation::And, true) => (BooleanOperation::Or, true, false),
                (BooleanOperation::Or, true) => (BooleanOperation::And, true, false),
                (op, inv) => (op, false, inv),
            };
            let left = normalize(left, child_invert, budget)?;
            let right = normalize(right, child_invert, budget)?;
            let mut terms = Vec::new();
            flatten(left, operation, &mut terms, budget)?;
            flatten(right, operation, &mut terms, budget)?;
            let mut keyed = terms
                .into_iter()
                .map(|term| {
                    let key = ScalarTemplate::capture(&term, &mut |a, _, _| Ok(a.clone()), budget)?;
                    Ok((key, term))
                })
                .collect::<Result<Vec<_>, LogicError>>()?;
            // Fallible insertion sort charges every comparison to the caller's
            // budget; there is no unmetered solver or fresh per-subtree budget.
            for i in 1..keyed.len() {
                let mut j = i;
                while j > 0 {
                    budget.charge(1)?;
                    if keyed[j - 1].0 <= keyed[j].0 {
                        break;
                    }
                    keyed.swap(j - 1, j);
                    j -= 1;
                }
            }
            let terms: Vec<_> = keyed.into_iter().map(|(_, value)| value).collect();
            let mut result = balanced(&terms, operation, budget)?;
            if result_invert {
                result = result.bool_not();
            }
            result
        }
        _ => return Err(LogicError::TypeMismatch),
    })
}

fn flatten<A: Ord, R>(
    value: Value<A, R>,
    operation: BooleanOperation,
    terms: &mut Vec<Value<A, R>>,
    budget: &mut LogicBudget,
) -> Result<(), LogicError> {
    budget.charge(1)?;
    match value {
        Value::BoolBinary {
            operation: op,
            left,
            right,
            negated: false,
        } if op == operation && operation != BooleanOperation::Equal => {
            flatten(*left, operation, terms, budget)?;
            flatten(*right, operation, terms, budget)?;
        }
        value => terms.push(value),
    }
    Ok(())
}

fn balanced<A: Ord + Clone, R: Clone>(
    terms: &[Value<A, R>],
    operation: BooleanOperation,
    budget: &mut LogicBudget,
) -> Result<Value<A, R>, LogicError> {
    budget.charge(1)?;
    if terms.len() == 1 {
        return Ok(terms[0].clone());
    }
    let middle = terms.len() / 2;
    Ok(Value::BoolBinary {
        operation,
        left: Box::new(balanced(&terms[..middle], operation, budget)?),
        right: Box::new(balanced(&terms[middle..], operation, budget)?),
        negated: false,
    })
}

#[cfg(test)]
mod tests;
