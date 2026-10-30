use super::*;
type Value = TypedLogicValue<u32, u32, u32>;
fn join(a: &Value, b: &Value) -> Result<Value, LogicError> {
    a.join_capture(b, &mut LogicBudget::default())
}
fn boolean(atom: u32, known: Option<bool>, negated: bool) -> Value {
    Value {
        ty: LogicType::Bool,
        value: LogicValue::BoolAtom {
            atom,
            known,
            negated,
        },
    }
}
fn word(atom: u32, lower: u64, upper: u64) -> Value {
    Value {
        ty: LogicType::Usize,
        value: LogicValue::Word(AffineValue::identified(atom, lower, upper).unwrap()),
    }
}

#[test]
fn boolean_join_forgets_only_path_specific_truth_and_obeys_join_laws() {
    for negated in [false, true] {
        for a in [None, Some(false), Some(true)] {
            for b in [None, Some(false), Some(true)] {
                let left = boolean(10, a, negated);
                let right = boolean(10, b, negated);
                let merged = join(&left, &right).unwrap();
                assert_eq!(merged, boolean(10, if a == b { a } else { None }, negated));
                assert_eq!(join(&right, &left), Ok(merged.clone()));
                assert_eq!(join(&left, &left), Ok(left.clone()));
                assert_eq!(join(&merged, &left), Ok(merged.clone()));
                for c in [None, Some(false), Some(true)] {
                    let third = boolean(10, c, negated);
                    assert_eq!(
                        join(&merged, &third),
                        join(&left, &join(&right, &third).unwrap())
                    );
                }
            }
        }
    }
}

#[test]
fn same_affine_and_comparison_shapes_join_bounds_without_constantizing() {
    let a = word(10, 1, 2);
    let b = word(10, 6, 7);
    assert_eq!(join(&a, &b), Ok(word(10, 1, 7)));
    assert_eq!(join(&b, &a), join(&a, &b));
    let comparison = |value: Value| {
        let LogicValue::Word(left) = value.value else {
            panic!()
        };
        Value {
            ty: LogicType::Bool,
            value: LogicValue::BoolComparison {
                word_type: WordType::Usize,
                comparison: WordComparison::LessEqual,
                left,
                right: AffineValue::exact(3),
                negated: false,
            },
        }
    };
    let a = comparison(a);
    let b = comparison(b);
    assert_eq!(a.value.known_boolean(), Some(true));
    assert_eq!(b.value.known_boolean(), Some(false));
    let joined = join(&a, &b).unwrap();
    assert_eq!(joined, comparison(word(10, 1, 7)));
    assert_eq!(joined.value.known_boolean(), None);
    assert_eq!(join(&joined, &a), Ok(joined.clone()));
    assert_eq!(join(&a, &b), join(&b, &a));
    let mut wrong = b.clone();
    if let LogicValue::BoolComparison { negated, .. } = &mut wrong.value {
        *negated = true;
    }
    assert_eq!(join(&a, &wrong), Err(LogicError::Unbound));
    let mut wrong_type = b.clone();
    if let LogicValue::BoolComparison { word_type, .. } = &mut wrong_type.value {
        *word_type = WordType::U64;
    }
    assert_eq!(join(&a, &wrong_type), Err(LogicError::Unbound));
}

#[test]
fn matching_truth_or_ranges_never_establish_identity() {
    assert_eq!(
        join(
            &boolean(10, Some(true), false),
            &boolean(20, Some(true), false)
        ),
        Err(LogicError::Unbound)
    );
    assert_eq!(
        join(
            &boolean(10, Some(true), false),
            &boolean(10, Some(false), true)
        ),
        Err(LogicError::Unbound)
    );
    assert_eq!(
        join(&word(10, 1, 1), &word(20, 1, 1)),
        Err(LogicError::Unbound)
    );
    let literal = Value {
        ty: LogicType::Bool,
        value: LogicValue::Bool(Some(true)),
    };
    assert_eq!(
        join(&literal, &boolean(10, Some(true), false)),
        Err(LogicError::Unbound)
    );
    let unknown = Value {
        ty: LogicType::Bool,
        value: LogicValue::Bool(None),
    };
    assert_eq!(join(&unknown, &unknown), Err(LogicError::Unbound));
    let other_literal = Value {
        value: LogicValue::Bool(Some(false)),
        ..literal.clone()
    };
    assert_eq!(join(&literal, &other_literal), Err(LogicError::Unbound));
    assert_eq!(join(&literal, &literal), Ok(literal));
    let mut different_type = word(10, 1, 1);
    different_type.ty = LogicType::U64;
    assert_eq!(
        join(&word(10, 1, 1), &different_type),
        Err(LogicError::TypeMismatch)
    );
    let mut shifted = word(10, 1, 1);
    if let LogicValue::Word(word) = &mut shifted.value {
        word.constant = 1;
    }
    assert_eq!(join(&word(10, 1, 1), &shifted), Err(LogicError::Unbound));
}

#[test]
fn malformed_bounds_and_shared_budget_failure_cannot_be_join_evidence() {
    let value = word(10, 1, 7);
    let mut malformed = value.clone();
    if let LogicValue::Word(word) = &mut malformed.value {
        word.lower = 8;
    }
    assert_eq!(join(&value, &malformed), Err(LogicError::InvalidNode));
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES - 1).unwrap();
    assert_eq!(
        value.join_capture(&value, &mut budget),
        Err(LogicError::Budget)
    );
    assert_eq!(value, word(10, 1, 7));
    let resource = Value {
        ty: LogicType::Resource(1),
        value: LogicValue::Resource(10),
    };
    assert_eq!(join(&resource, &resource), Ok(resource.clone()));
    let different = Value {
        value: LogicValue::Resource(20),
        ..resource.clone()
    };
    assert_eq!(join(&resource, &different), Err(LogicError::Unbound));
}

#[test]
fn captured_numeric_widening_accelerates_growth_and_stabilizes() {
    let old = word(10, 2, 3);
    for (next, expected) in [
        (word(10, 1, 3), word(10, 0, 3)),
        (word(10, 2, 4), word(10, 2, u64::MAX)),
        (word(10, 1, 4), word(10, 0, u64::MAX)),
    ] {
        let wide = old
            .widen_capture(&next, &mut LogicBudget::default())
            .unwrap();
        assert_eq!(wide, expected);
        assert_eq!(
            wide.widen_capture(&next, &mut LogicBudget::default()),
            Ok(wide.clone())
        );
        assert_eq!(join(&wide, &old), Ok(wide.clone()));
        assert_eq!(join(&wide, &next), Ok(wide));
    }
    let old = boolean(10, Some(true), false);
    let next = boolean(10, Some(false), false);
    assert_eq!(
        old.widen_capture(&next, &mut LogicBudget::default()),
        Ok(boolean(10, None, false))
    );
}
