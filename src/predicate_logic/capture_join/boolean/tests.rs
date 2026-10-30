use super::*;
type V = LogicValue<u32, ()>;
type Typed = TypedLogicValue<(), u32, ()>;

fn atom(id: u32, known: Option<bool>) -> V {
    V::BoolAtom {
        atom: id,
        known,
        negated: false,
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
fn forms(a: V, b: V, c: V) -> (V, V) {
    use BooleanOperation::*;
    (
        gate(And, a.clone(), gate(Or, b.clone(), c.clone())),
        gate(Or, gate(And, a.clone(), b), gate(And, a, c)),
    )
}
fn typed(value: V) -> Typed {
    Typed {
        ty: LogicType::Bool,
        value,
    }
}
fn join(a: &V, b: &V) -> Result<V, LogicError> {
    typed(a.clone())
        .join_capture(&typed(b.clone()), &mut LogicBudget::default())
        .map(|value| value.value)
}

#[test]
fn distributive_join_preserves_sources_and_forgets_branch_truth() {
    let (a, _) = forms(
        atom(1, Some(true)),
        atom(2, Some(false)),
        atom(3, Some(true)),
    );
    let (_, b) = forms(
        atom(1, Some(false)),
        atom(2, Some(true)),
        atom(3, Some(false)),
    );
    let joined = join(&a, &b).unwrap();
    assert_eq!(join(&b, &a), Ok(joined.clone()));
    assert_eq!(join(&joined, &a), Ok(joined.clone()));
    assert_eq!(join(&joined, &b), Ok(joined.clone()));
    let leaves = joined.capture_leaves(&mut LogicBudget::default()).unwrap();
    let mut sources = BTreeSet::new();
    for leaf in leaves {
        let V::BoolAtom {
            atom, known: None, ..
        } = leaf
        else {
            panic!("lost source or retained branch truth")
        };
        sources.insert(*atom);
    }
    assert_eq!(sources, BTreeSet::from([1, 2, 3]));
    assert_eq!(
        typed(a)
            .widen_capture(&typed(b), &mut LogicBudget::default())
            .unwrap()
            .value,
        joined
    );
}

fn comparison(lower: u64, upper: u64, word_type: WordType) -> V {
    V::BoolComparison {
        word_type,
        comparison: WordComparison::LessEqual,
        left: AffineValue::identified(7, lower, upper).unwrap(),
        right: AffineValue::exact(5),
        negated: false,
    }
}

#[test]
fn repeated_numeric_leaves_merge_precision_before_widening() {
    let (a, _) = forms(
        comparison(2, 3, WordType::Usize),
        atom(2, None),
        atom(3, None),
    );
    let (_, b) = forms(
        comparison(1, 8, WordType::Usize),
        atom(2, None),
        atom(3, None),
    );
    for (wide, lower, upper) in [(false, 1, 8), (true, 0, u64::MAX)] {
        let a = typed(a.clone());
        let b = typed(b.clone());
        let joined = if wide {
            a.widen_capture(&b, &mut LogicBudget::default())
        } else {
            a.join_capture(&b, &mut LogicBudget::default())
        }
        .unwrap();
        for leaf in joined
            .value
            .capture_leaves(&mut LogicBudget::default())
            .unwrap()
        {
            if let V::BoolComparison {
                left, word_type, ..
            } = leaf
            {
                assert_eq!(*word_type, WordType::Usize);
                assert_eq!((left.lower, left.upper), (lower, upper));
                assert_eq!(left.terms, BTreeMap::from([(7, 1)]));
            }
        }
        assert_eq!(
            joined
                .join_capture(&b, &mut LogicBudget::default())
                .unwrap(),
            joined
        );
    }
    let (_, wrong) = forms(
        comparison(1, 8, WordType::U64),
        atom(2, None),
        atom(3, None),
    );
    assert_eq!(join(&a, &wrong), Err(LogicError::Unbound));
}

#[test]
fn equivalence_cannot_align_missing_sources_or_rely_on_current_truth() {
    use BooleanOperation::*;
    let (a, _) = forms(
        atom(1, Some(true)),
        atom(2, Some(true)),
        atom(3, Some(true)),
    );
    let (_, wrong_source) = forms(
        atom(4, Some(true)),
        atom(2, Some(true)),
        atom(3, Some(true)),
    );
    assert_eq!(join(&a, &wrong_source), Err(LogicError::Unbound));
    let wrong_shape = gate(
        Or,
        atom(1, Some(true)),
        gate(And, atom(2, Some(true)), atom(3, Some(true))),
    );
    assert_eq!(join(&a, &wrong_shape), Err(LogicError::Unbound));
    let tautology = gate(Or, atom(1, None), atom(1, None).bool_not());
    assert_eq!(
        join(&tautology, &V::Bool(Some(true))),
        Err(LogicError::Unbound)
    );
    let mut malformed = comparison(0, 8, WordType::Usize);
    if let V::BoolComparison { left, .. } = &mut malformed {
        left.lower = 9;
    }
    let invalid = gate(Or, V::Bool(Some(true)), malformed);
    // Construct invalid bounds explicitly: they cannot be erased by a true branch.
    assert_eq!(join(&invalid, &invalid), Err(LogicError::InvalidNode));
}

#[test]
fn equivalence_handles_negated_equality_and_exhausts_one_shared_budget() {
    use BooleanOperation::*;
    let (a, b) = forms(atom(1, None), atom(2, None), atom(3, None));
    assert!(
        crate::predicate_logic::boolean_equivalence::equivalent_values(
            &gate(Equal, a, V::Bool(Some(false))),
            &b.bool_not(),
            &mut LogicBudget::default()
        )
        .unwrap()
    );
    let mut left = atom(0, None);
    for id in 1..9 {
        left = gate(Or, left, atom(id, None));
    }
    let mut budget = LogicBudget::default();
    assert_eq!(
        crate::predicate_logic::boolean_equivalence::equivalent_values(&left, &left, &mut budget),
        Err(LogicError::Budget)
    );
}
