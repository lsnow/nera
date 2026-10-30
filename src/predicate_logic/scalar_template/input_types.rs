//! Recover the logical types of template inputs without inspecting runtime slots.
//! Whole words inherit the declared result type; comparison operands retain
//! their own word type even when nested inside a Boolean result.
use super::*;

impl<A: Ord + Clone> ScalarTemplate<A> {
    pub(crate) fn typed_inputs<T: Copy + Eq>(
        &self,
        result_type: LogicType<T>,
        budget: &mut LogicBudget,
    ) -> Result<BTreeMap<A, LogicType<T>>, LogicError> {
        budget.charge(1)?;
        let mut result = BTreeMap::new();
        match (self, result_type) {
            (Self::Boolean { left, right, .. }, LogicType::Bool) => {
                for (atom, ty) in left
                    .typed_inputs(LogicType::Bool, budget)?
                    .into_iter()
                    .chain(right.typed_inputs(LogicType::Bool, budget)?)
                {
                    budget.charge(1)?;
                    if result.insert(atom, ty).is_some_and(|old| old != ty) {
                        return Err(LogicError::TypeMismatch);
                    }
                }
            }
            (Self::Bool(_), LogicType::Bool) => {}
            (Self::BoolAtom { atom, .. }, LogicType::Bool) => {
                result.insert(atom.clone(), LogicType::Bool);
            }
            (Self::Word(word), LogicType::U64 | LogicType::Usize) => {
                budget.charge(word.terms.len())?;
                result.extend(word.terms.keys().cloned().map(|a| (a, result_type)));
            }
            (
                Self::Comparison {
                    word_type,
                    left,
                    right,
                    ..
                },
                LogicType::Bool,
            ) => {
                budget.charge(left.terms.len() + right.terms.len())?;
                result.extend(
                    left.terms
                        .keys()
                        .chain(right.terms.keys())
                        .cloned()
                        .map(|a| (a, word_type.logic_type())),
                );
            }
            _ => return Err(LogicError::TypeMismatch),
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type Value = LogicValue<u32, ()>;
    fn comparison(word_type: WordType, atom: u32) -> Value {
        Value::BoolComparison {
            word_type,
            comparison: WordComparison::LessEqual,
            left: AffineValue::identified(atom, 0, 9).unwrap(),
            right: AffineValue::exact(4),
            negated: false,
        }
    }
    fn template(value: &Value) -> ScalarTemplate<u32> {
        ScalarTemplate::capture(value, &mut |id, _, _| Ok(*id), &mut LogicBudget::default())
            .unwrap()
    }

    #[test]
    fn nested_comparisons_select_their_own_input_and_domain_types() {
        let value = Value::boolean_binary(
            BooleanOperation::Or,
            comparison(WordType::U64, 1),
            comparison(WordType::Usize, 2),
            false,
            &mut LogicBudget::default(),
        )
        .unwrap();
        let template = template(&value);
        assert_eq!(
            template.typed_inputs::<()>(LogicType::Bool, &mut LogicBudget::default()),
            Ok(BTreeMap::from([(1, LogicType::U64), (2, LogicType::Usize)]))
        );
        let mut domains = Vec::new();
        let result = template
            .instantiate_with_domain(
                &mut |id, kind, _| {
                    assert_eq!(kind, ScalarKind::Word);
                    Ok(Value::Word(
                        AffineValue::identified(*id + 10, 0, 9).unwrap(),
                    ))
                },
                &mut |ty, word, _| {
                    domains.push(ty);
                    word.into_word()
                },
                &mut LogicBudget::default(),
            )
            .unwrap();
        assert_eq!(
            domains,
            vec![
                Some(WordType::U64),
                Some(WordType::U64),
                Some(WordType::Usize),
                Some(WordType::Usize)
            ]
        );
        let leaves = result.capture_leaves(&mut LogicBudget::default()).unwrap();
        assert!(matches!(
            leaves[0],
            Value::BoolComparison {
                word_type: WordType::U64,
                ..
            }
        ));
        assert!(matches!(
            leaves[1],
            Value::BoolComparison {
                word_type: WordType::Usize,
                ..
            }
        ));
    }

    #[test]
    fn conflicting_input_types_and_wrong_result_types_are_rejected() {
        let value = Value::boolean_binary(
            BooleanOperation::And,
            comparison(WordType::U64, 1),
            comparison(WordType::Usize, 1),
            false,
            &mut LogicBudget::default(),
        )
        .unwrap();
        assert_eq!(
            template(&value).typed_inputs::<()>(LogicType::Bool, &mut LogicBudget::default()),
            Err(LogicError::TypeMismatch)
        );
        assert_eq!(
            template(&comparison(WordType::Usize, 1))
                .typed_inputs::<()>(LogicType::Usize, &mut LogicBudget::default()),
            Err(LogicError::TypeMismatch)
        );
        assert_eq!(
            template(&comparison(WordType::Usize, 1))
                .typed_inputs::<()>(LogicType::Bool, &mut LogicBudget { remaining: 0 }),
            Err(LogicError::Budget)
        );
        let word = template(&Value::Word(AffineValue::identified(1, 0, 9).unwrap()));
        assert_eq!(
            word.typed_inputs::<()>(LogicType::Usize, &mut LogicBudget::default()),
            Ok(BTreeMap::from([(1, LogicType::Usize)]))
        );
    }

    #[test]
    fn coordinate_rebasing_preserves_comparison_operand_type() {
        for word_type in [WordType::U64, WordType::Usize] {
            let value = comparison(word_type, 1);
            let rewritten = ScalarTemplate::<u32>::rebase_capture(
                &value,
                &[(9, AffineValue::identified(1, 0, 9).unwrap())],
                &mut |id, _, _| Ok(*id),
                &mut LogicBudget::default(),
            )
            .unwrap();
            assert!(
                matches!(rewritten,Value::BoolComparison {word_type:actual,..} if actual==word_type)
            );
            assert_eq!(
                template(&rewritten)
                    .typed_inputs::<()>(LogicType::Bool, &mut LogicBudget::default()),
                Ok(BTreeMap::from([(9, word_type.logic_type())]))
            );
        }
    }
}
