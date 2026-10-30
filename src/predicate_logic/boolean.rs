//! Bounded Boolean capture structure and leaf traversal. This module knows no
//! runtime identities, provenance, CFG or permissions; adapters admit leaves.
use super::*;

impl BooleanOperation {
    pub(crate) fn evaluate(self, left: Option<bool>, right: Option<bool>) -> Option<bool> {
        match self {
            Self::Equal => left.zip(right).map(|(a, b)| a == b),
            Self::And if left == Some(false) || right == Some(false) => Some(false),
            Self::Or if left == Some(true) || right == Some(true) => Some(true),
            Self::And => left.zip(right).map(|(a, b)| a && b),
            Self::Or => left.zip(right).map(|(a, b)| a || b),
        }
    }
}

impl<A: Ord, R> LogicValue<A, R> {
    pub(crate) fn is_boolean(&self) -> bool {
        matches!(
            self,
            Self::Bool(_)
                | Self::BoolAtom { .. }
                | Self::BoolComparison { .. }
                | Self::BoolBinary { .. }
        )
    }

    /// One traversal bound covers the complete expanded capture. Children of
    /// Boolean operators must themselves be Boolean, including at adapter APIs.
    pub(crate) fn capture_leaves(
        &self,
        budget: &mut LogicBudget,
    ) -> Result<Vec<&Self>, LogicError> {
        let mut pending = vec![(self, 0)];
        let mut leaves = Vec::new();
        let mut count = 0;
        while let Some((value, depth)) = pending.pop() {
            budget.charge(1)?;
            count += 1;
            if count > MAX_EXPRESSION_NODES || depth >= MAX_EXPRESSION_DEPTH {
                return Err(LogicError::Budget);
            }
            if let Self::BoolBinary { left, right, .. } = value {
                if !left.is_boolean() || !right.is_boolean() {
                    return Err(LogicError::TypeMismatch);
                }
                pending.push((right, depth + 1));
                pending.push((left, depth + 1));
            } else {
                leaves.push(value);
            }
        }
        Ok(leaves)
    }

    pub(crate) fn capture_leaves_mut(
        &mut self,
        budget: &mut LogicBudget,
    ) -> Result<Vec<&mut Self>, LogicError> {
        let mut pending = vec![(self, 0)];
        let mut leaves = Vec::new();
        let mut count = 0;
        while let Some((value, depth)) = pending.pop() {
            budget.charge(1)?;
            count += 1;
            if count > MAX_EXPRESSION_NODES || depth >= MAX_EXPRESSION_DEPTH {
                return Err(LogicError::Budget);
            }
            if let Self::BoolBinary { left, right, .. } = value {
                if !left.is_boolean() || !right.is_boolean() {
                    return Err(LogicError::TypeMismatch);
                }
                pending.push((right, depth + 1));
                pending.push((left, depth + 1));
            } else {
                leaves.push(value);
            }
        }
        Ok(leaves)
    }
}

impl<A: Ord, R> LogicValue<A, R> {
    pub(crate) fn boolean_binary(
        operation: BooleanOperation,
        left: Self,
        right: Self,
        negated: bool,
        budget: &mut LogicBudget,
    ) -> Result<Self, LogicError> {
        if !left.is_boolean() || !right.is_boolean() {
            return Err(LogicError::TypeMismatch);
        }
        let result = Self::BoolBinary {
            operation,
            left: Box::new(left),
            right: Box::new(right),
            negated,
        };
        if result
            .capture_leaves(budget)?
            .iter()
            .any(|v| matches!(v, Self::Bool(None)))
        {
            return Err(LogicError::Unbound);
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate_logic::scalar_template::{ScalarKind, ScalarTemplate};
    type Value = LogicValue<u32, ()>;
    fn atom(id: u32, known: Option<bool>) -> Value {
        Value::BoolAtom {
            atom: id,
            negated: false,
            known,
        }
    }
    fn binary(op: BooleanOperation, a: Value, b: Value) -> Value {
        Value::boolean_binary(op, a, b, false, &mut LogicBudget::default()).unwrap()
    }
    #[test]
    fn templates_keep_all_boolean_inputs_and_recompute_truth_after_substitution() {
        for op in [
            BooleanOperation::And,
            BooleanOperation::Or,
            BooleanOperation::Equal,
        ] {
            for old in [false, true] {
                let value = binary(op, atom(1, Some(old)), atom(2, Some(old)));
                let template = ScalarTemplate::capture(
                    &value,
                    &mut |id, _, _| Ok(*id),
                    &mut LogicBudget::default(),
                )
                .unwrap();
                assert_eq!(
                    template.inputs(&mut LogicBudget::default()).unwrap(),
                    BTreeMap::from([(1, ScalarKind::Bool), (2, ScalarKind::Bool)])
                );
                for a in [false, true] {
                    for b in [false, true] {
                        let rebuilt: Value = template
                            .instantiate(
                                &mut |id, _, _| {
                                    Ok(atom(*id + 10, Some(if *id == 1 { a } else { b })))
                                },
                                &mut LogicBudget::default(),
                            )
                            .unwrap();
                        assert_eq!(rebuilt.known_boolean(), op.evaluate(Some(a), Some(b)));
                        assert_eq!(
                            rebuilt.bool_not().known_boolean(),
                            op.evaluate(Some(a), Some(b)).map(|v| !v)
                        );
                    }
                }
            }
        }
    }
    #[test]
    fn nested_comparisons_rebase_and_join_without_losing_shape_or_leaf_bounds() {
        let source = AffineValue::identified(1, 0, 2)
            .unwrap()
            .add(&AffineValue::exact(1))
            .unwrap();
        let comparison = Value::BoolComparison {
            word_type: WordType::Usize,
            comparison: WordComparison::LessEqual,
            left: source.clone(),
            right: AffineValue::exact(2),
            negated: false,
        };
        let value = binary(
            BooleanOperation::Or,
            binary(BooleanOperation::And, atom(3, None), comparison),
            atom(4, Some(false)),
        );
        let rewritten: Value = ScalarTemplate::rebase_capture(
            &value,
            &[(20, source)],
            &mut |id, _, _| Ok(*id + 20),
            &mut LogicBudget::default(),
        )
        .unwrap();
        let template = ScalarTemplate::capture(
            &rewritten,
            &mut |id, _, _| Ok(*id),
            &mut LogicBudget::default(),
        )
        .unwrap();
        assert_eq!(
            template.inputs(&mut LogicBudget::default()).unwrap(),
            BTreeMap::from([
                (20, ScalarKind::Word),
                (23, ScalarKind::Bool),
                (24, ScalarKind::Bool)
            ])
        );
        let mut wider = rewritten.clone();
        for leaf in wider
            .capture_leaves_mut(&mut LogicBudget::default())
            .unwrap()
        {
            if let Value::BoolComparison { left, .. } = leaf {
                left.upper = 9;
            }
            if let Value::BoolAtom { known, .. } = leaf {
                *known = None;
            }
        }
        let typed = |value| TypedLogicValue::<(), _, _> {
            ty: LogicType::Bool,
            value,
        };
        let a = typed(rewritten);
        let b = typed(wider);
        let joined = a.join_capture(&b, &mut LogicBudget::default()).unwrap();
        assert_eq!(
            joined,
            b.join_capture(&a, &mut LogicBudget::default()).unwrap()
        );
        assert_eq!(
            joined,
            typed(
                b.value
                    .canonical_boolean_capture(&mut LogicBudget::default())
                    .unwrap()
            )
        );
        let wide = a.widen_capture(&b, &mut LogicBudget::default()).unwrap();
        assert_eq!(
            wide.widen_capture(&b, &mut LogicBudget::default()).unwrap(),
            wide
        );
        assert!(
            a.join_capture(&typed(value), &mut LogicBudget::default())
                .is_err()
        );
    }
    #[test]
    fn anonymous_operands_malformed_children_depth_and_shared_budget_fail_closed() {
        assert_eq!(
            Value::boolean_binary(
                BooleanOperation::And,
                atom(1, None),
                Value::Bool(None),
                false,
                &mut LogicBudget::default()
            ),
            Err(LogicError::Unbound)
        );
        assert_eq!(
            Value::boolean_binary(
                BooleanOperation::And,
                atom(1, None),
                Value::Word(AffineValue::exact(0)),
                false,
                &mut LogicBudget::default()
            ),
            Err(LogicError::TypeMismatch)
        );
        let mut value = atom(0, None);
        for id in 1..MAX_EXPRESSION_DEPTH {
            value = binary(BooleanOperation::And, value, atom(id as u32, None));
        }
        assert_eq!(
            Value::boolean_binary(
                BooleanOperation::Or,
                value,
                atom(99, None),
                false,
                &mut LogicBudget::default()
            ),
            Err(LogicError::Budget)
        );
        let mut balanced = atom(1, None);
        for _ in 0..7 {
            balanced = binary(BooleanOperation::Equal, balanced.clone(), balanced);
        }
        assert_eq!(
            Value::boolean_binary(
                BooleanOperation::And,
                balanced.clone(),
                balanced,
                false,
                &mut LogicBudget::default()
            ),
            Err(LogicError::Budget)
        );
        let mut budget = LogicBudget::default();
        budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
        assert_eq!(
            Value::boolean_binary(
                BooleanOperation::Equal,
                atom(1, None),
                atom(2, None),
                false,
                &mut budget
            ),
            Err(LogicError::Budget)
        );
    }
}
