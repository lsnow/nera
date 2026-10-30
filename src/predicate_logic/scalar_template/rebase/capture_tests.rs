use super::*;
type Value = LogicValue<u32, ()>;

fn word() -> AffineValue<u32> {
    AffineValue::identified(1, 1, 2)
        .unwrap()
        .add(&AffineValue::identified(2, 1, 2).unwrap())
        .unwrap()
        .add(&AffineValue::exact(1))
        .unwrap()
}

fn rewrite(value: &Value, sources: &[(u32, AffineValue<u32>)]) -> Result<Value, LogicError> {
    ScalarTemplate::rebase_capture(
        value,
        sources,
        &mut |a, _, _| Ok(*a),
        &mut LogicBudget::default(),
    )
}

#[test]
fn dependent_complete_coordinates_keep_each_direct_public_identity() {
    let a = word();
    let b = a.scale(2).unwrap();
    for sources in [
        vec![(90, a.clone()), (91, b.clone())],
        vec![(91, b.clone()), (90, a.clone())],
    ] {
        for (id, original) in [(90, &a), (91, &b)] {
            assert_eq!(
                rewrite(&Value::Word(original.clone()), &sources),
                Ok(Value::Word(
                    AffineValue::identified(id, original.lower, original.upper).unwrap()
                ))
            );
        }
        let compared = rewrite(
            &Value::BoolComparison {
                word_type: WordType::Usize,
                comparison: WordComparison::LessEqual,
                left: a.clone(),
                right: b.clone(),
                negated: true,
            },
            &sources,
        )
        .unwrap();
        assert_eq!(
            compared,
            Value::BoolComparison {
                word_type: WordType::Usize,
                comparison: WordComparison::LessEqual,
                left: AffineValue::identified(90, a.lower, a.upper).unwrap(),
                right: AffineValue::identified(91, b.lower, b.upper).unwrap(),
                negated: true,
            }
        );
        // Induction templates still require independent changing coordinates.
        assert_eq!(
            ScalarTemplate::<u32>::capture_rebased(
                &Value::Word(b.clone()),
                &sources,
                &[],
                &mut |a, _, _| Ok(*a),
                &mut LogicBudget::default(),
            ),
            Err(LogicError::Unbound)
        );
        // No arbitrary dependent-basis selection for an unmatched expression.
        assert_eq!(
            rewrite(&Value::Word(a.scale(3).unwrap()), &sources),
            Err(LogicError::Unbound)
        );
    }
}

#[test]
fn exact_capture_uses_polynomial_identity_and_validates_all_sources() {
    let source = word();
    let narrowed = AffineValue {
        lower: 4,
        upper: 4,
        ..source.clone()
    };
    assert_eq!(
        rewrite(&Value::Word(narrowed), &[(90, source.clone())]),
        Ok(Value::Word(AffineValue::identified(90, 4, 4).unwrap()))
    );
    // Repeated equivalent coordinates select by key, not input iteration order.
    for sources in [
        vec![(91, source.clone()), (90, source.clone())],
        vec![(90, source.clone()), (91, source.clone())],
    ] {
        assert_eq!(
            rewrite(&Value::Word(source.clone()), &sources),
            Ok(Value::Word(
                AffineValue::identified(90, source.lower, source.upper).unwrap()
            ))
        );
    }
    let shifted = source.add(&AffineValue::exact(1)).unwrap();
    let other = AffineValue {
        terms: BTreeMap::from([(3, 1), (4, 1)]),
        ..source.clone()
    };
    // Neither equal ranges nor equal coefficients with different constants
    // establish whole-coordinate identity in a dependent group.
    assert_eq!(
        rewrite(
            &Value::Word(source.clone()),
            &[(90, shifted.clone()), (91, shifted)]
        ),
        Err(LogicError::Unbound)
    );
    assert_eq!(
        rewrite(&Value::Word(other.clone()), &[(90, source.clone())]),
        Ok(Value::Word(other))
    );
    let bad = AffineValue {
        lower: 9,
        upper: 1,
        ..source.clone()
    };
    assert_eq!(
        rewrite(
            &Value::Word(source.clone()),
            &[(90, source.clone()), (91, bad)]
        ),
        Err(LogicError::InvalidNode)
    );
    assert_eq!(
        rewrite(
            &Value::Word(source.clone()),
            &[(90, source.clone()), (90, source.clone())]
        ),
        Err(LogicError::InvalidNode)
    );
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert_eq!(
        ScalarTemplate::<u32>::rebase_capture(
            &Value::Word(source.clone()),
            &[(90, source)],
            &mut |a, _, _| Ok(*a),
            &mut budget
        ),
        Err(LogicError::Budget)
    );
}
