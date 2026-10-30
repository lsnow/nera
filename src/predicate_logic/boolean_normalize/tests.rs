use super::*;
type V = LogicValue<u32, u32>;
type Typed = TypedLogicValue<u32, u32, u32>;
fn atom(id: u32, known: Option<bool>) -> V {
    V::BoolAtom {
        atom: id,
        negated: false,
        known,
    }
}
fn gate(op: BooleanOperation, a: V, b: V) -> V {
    V::BoolBinary {
        operation: op,
        left: Box::new(a),
        right: Box::new(b),
        negated: false,
    }
}
fn canon(value: &V) -> V {
    value
        .canonical_boolean_capture(&mut LogicBudget::default())
        .unwrap()
}
fn typed(value: V) -> Typed {
    Typed {
        ty: LogicType::Bool,
        value,
    }
}

#[test]
fn associative_commutative_and_demorgan_forms_preserve_truth_and_named_structure() {
    for op in [BooleanOperation::And, BooleanOperation::Or] {
        let dual = if op == BooleanOperation::And {
            BooleanOperation::Or
        } else {
            BooleanOperation::And
        };
        for bits in 0..8 {
            let a = atom(1, Some(bits & 1 != 0));
            let b = atom(2, Some(bits & 2 != 0));
            let c = atom(3, Some(bits & 4 != 0));
            let first = gate(op, gate(op, a.clone(), b.clone()), c.clone());
            let forms = [
                first.clone(),
                gate(op, c.clone(), gate(op, b.clone(), a.clone())),
                gate(dual, c.bool_not(), gate(dual, a.bool_not(), b.bool_not())).bool_not(),
            ];
            for value in forms {
                let canonical = canon(&value);
                assert_eq!(canonical, canon(&first));
                assert_eq!(canonical.known_boolean(), value.known_boolean());
                assert_eq!(canon(&canonical), canonical);
                assert_eq!(
                    canonical
                        .capture_leaves(&mut LogicBudget::default())
                        .unwrap()
                        .len(),
                    3
                );
            }
        }
    }
}

#[test]
fn equivalent_shapes_join_and_widen_without_preserving_one_predecessors_truth() {
    let left = typed(gate(
        BooleanOperation::And,
        atom(1, Some(true)),
        atom(2, Some(false)),
    ));
    let right = typed(
        gate(
            BooleanOperation::Or,
            atom(2, Some(true)).bool_not(),
            atom(1, Some(false)).bool_not(),
        )
        .bool_not(),
    );
    let expected = typed(gate(BooleanOperation::And, atom(1, None), atom(2, None)));
    let joined = left
        .join_capture(&right, &mut LogicBudget::default())
        .unwrap();
    assert_eq!(joined, expected);
    assert_eq!(
        right.join_capture(&left, &mut LogicBudget::default()),
        Ok(joined.clone())
    );
    assert_eq!(
        joined.join_capture(&left, &mut LogicBudget::default()),
        Ok(joined.clone())
    );
    assert_eq!(
        left.widen_capture(&right, &mut LogicBudget::default()),
        Ok(joined)
    );
}

fn equal(a: AffineValue<u32>, b: AffineValue<u32>, ty: WordType) -> V {
    V::BoolComparison {
        word_type: ty,
        comparison: WordComparison::Equal,
        left: a,
        right: b,
        negated: false,
    }
}

#[test]
fn symmetric_numeric_equality_hulls_the_corresponding_operands_and_keeps_type() {
    for ty in [WordType::U64, WordType::Usize] {
        let left = typed(equal(
            AffineValue::identified(1, 1, 3).unwrap(),
            AffineValue::identified(2, 4, 8).unwrap(),
            ty,
        ));
        let right = typed(equal(
            AffineValue::identified(2, 2, 6).unwrap(),
            AffineValue::identified(1, 0, 4).unwrap(),
            ty,
        ));
        let joined = left
            .join_capture(&right, &mut LogicBudget::default())
            .unwrap();
        assert_eq!(
            joined,
            typed(equal(
                AffineValue::identified(1, 0, 4).unwrap(),
                AffineValue::identified(2, 2, 8).unwrap(),
                ty
            ))
        );
        assert_eq!(
            right.join_capture(&left, &mut LogicBudget::default()),
            Ok(joined)
        );
        let wrong = typed(equal(
            AffineValue::identified(1, 0, 4).unwrap(),
            AffineValue::identified(2, 2, 6).unwrap(),
            if ty == WordType::U64 {
                WordType::Usize
            } else {
                WordType::U64
            },
        ));
        assert_eq!(
            left.join_capture(&wrong, &mut LogicBudget::default()),
            Err(LogicError::Unbound)
        );
    }
}

#[test]
fn normalization_never_uses_equal_truths_as_identity_or_discards_a_hidden_bad_leaf() {
    let a = typed(gate(
        BooleanOperation::And,
        atom(1, Some(true)),
        atom(2, Some(true)),
    ));
    let b = typed(gate(
        BooleanOperation::And,
        atom(1, Some(true)),
        atom(3, Some(true)),
    ));
    assert_eq!(
        a.join_capture(&b, &mut LogicBudget::default()),
        Err(LogicError::Unbound)
    );
    assert_eq!(
        a.join_capture(&typed(V::Bool(Some(true))), &mut LogicBudget::default()),
        Err(LogicError::Unbound)
    );
    let mut invalid = AffineValue::identified(1, 0, 2).unwrap();
    invalid.lower = 3;
    let hidden = gate(
        BooleanOperation::Or,
        V::Bool(Some(true)),
        equal(invalid, AffineValue::exact(2), WordType::Usize),
    );
    assert_eq!(
        hidden.canonical_boolean_capture(&mut LogicBudget::default()),
        Err(LogicError::InvalidNode)
    );
    let anonymous = gate(BooleanOperation::Or, V::Bool(Some(true)), V::Bool(None));
    assert_eq!(
        anonymous.canonical_boolean_capture(&mut LogicBudget::default()),
        Err(LogicError::Unbound)
    );
}

#[test]
fn normalization_is_bounded_before_and_during_rewriting() {
    let mut value = atom(1, None);
    for _ in 0..MAX_EXPRESSION_DEPTH {
        value = gate(BooleanOperation::And, atom(2, None), value);
    }
    assert_eq!(
        value.canonical_boolean_capture(&mut LogicBudget::default()),
        Err(LogicError::Budget)
    );
    let original = gate(BooleanOperation::And, atom(2, None), atom(1, None));
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES - 4).unwrap();
    assert_eq!(
        original.canonical_boolean_capture(&mut budget),
        Err(LogicError::Budget)
    );
    assert_eq!(
        original,
        gate(BooleanOperation::And, atom(2, None), atom(1, None))
    );
}

#[test]
fn boolean_equality_is_commutative_but_ordered_numeric_comparison_is_not() {
    let first = gate(BooleanOperation::Equal, atom(1, None), atom(2, None)).bool_not();
    let swapped = gate(BooleanOperation::Equal, atom(2, None), atom(1, None)).bool_not();
    assert_eq!(canon(&first), canon(&swapped));
    assert_ne!(canon(&first), canon(&swapped.bool_not()));
    let mut forward = equal(
        AffineValue::identified(1, 0, 10).unwrap(),
        AffineValue::identified(2, 0, 10).unwrap(),
        WordType::Usize,
    );
    let mut backward = forward.clone();
    if let V::BoolComparison { comparison, .. } = &mut forward {
        *comparison = WordComparison::LessEqual;
    }
    if let V::BoolComparison {
        comparison,
        left,
        right,
        ..
    } = &mut backward
    {
        *comparison = WordComparison::LessEqual;
        std::mem::swap(left, right);
    }
    assert_eq!(
        typed(forward).join_capture(&typed(backward), &mut LogicBudget::default()),
        Err(LogicError::Unbound)
    );
    let malformed = gate(
        BooleanOperation::Or,
        V::Bool(Some(true)),
        V::Word(AffineValue::exact(0)),
    );
    assert_eq!(
        malformed.canonical_boolean_capture(&mut LogicBudget::default()),
        Err(LogicError::TypeMismatch)
    );
}
