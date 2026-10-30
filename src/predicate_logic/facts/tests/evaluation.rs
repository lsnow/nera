use super::*;
use LogicNodeKind::*;

fn difference() -> LogicExpression<u32> {
    expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
        (LogicType::Usize, Sub(1, 0)),
    ])
}

#[test]
fn signed_counts_use_correlations_without_losing_identity() {
    let low = word(10, 0, u64::MAX);
    let high = word(20, 0, u64::MAX);
    let mut facts = Facts::new();
    add_relation(&mut facts, low.clone(), high.clone(), Comparison::LessEqual);
    let constraint = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(0, 1)),
        (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
        (LogicType::Bool, LessEqual(3, 2)),
    ]);
    facts
        .extend(
            &constraint,
            &[(0, Some(low.clone())), (3, Some(high.clone()))],
            &mut LogicBudget::default(),
        )
        .unwrap();
    let leaves = [(0, Some(low.clone())), (1, Some(high.clone()))];
    let value = facts
        .evaluate_word(&difference(), &leaves, &mut LogicBudget::default())
        .unwrap()
        .unwrap();
    let LogicValue::Word(count) = value.value else {
        panic!()
    };
    assert_eq!((count.lower, count.upper), (0, 1));
    assert_eq!(count.terms, BTreeMap::from([(10, -1), (20, 1)]));
    assert_eq!(count.constant, 0);
    let mut reversed = difference();
    reversed.nodes[2].kind = Sub(0, 1);
    assert_eq!(
        facts.evaluate_word(&reversed, &leaves, &mut LogicBudget::default()),
        Ok(None)
    );
    let unrelated = [(0, Some(word(11, 0, u64::MAX))), (1, Some(high))];
    assert_eq!(
        facts.evaluate_word(&difference(), &unrelated, &mut LogicBudget::default()),
        Ok(None)
    );
    let mut other_type = difference();
    for node in &mut other_type.nodes {
        node.ty = LogicType::U64;
    }
    let other_leaves = leaves.map(|(id, value)| {
        (
            id,
            value.map(|mut value| {
                value.ty = LogicType::U64;
                value
            }),
        )
    });
    assert_eq!(
        facts.evaluate_word(&other_type, &other_leaves, &mut LogicBudget::default()),
        Ok(None)
    );
    assert_eq!(low, word(10, 0, u64::MAX));
}

#[test]
fn transitive_correlations_bound_composite_differences() {
    let x = word(10, 0, u64::MAX);
    let y = word(20, 0, u64::MAX);
    let z = word(30, 0, u64::MAX);
    let mut facts = Facts::new();
    add_relation(&mut facts, x.clone(), y.clone(), Comparison::Less);
    add_relation(&mut facts, y, z.clone(), Comparison::Less);
    let count = facts
        .evaluate_word(
            &difference(),
            &[(0, Some(x)), (1, Some(z))],
            &mut LogicBudget::default(),
        )
        .unwrap()
        .unwrap();
    let LogicValue::Word(count) = count.value else {
        panic!()
    };
    assert_eq!((count.lower, count.upper), (2, u64::MAX));
}

#[test]
fn scalar_evaluation_checks_each_intermediate_and_refines_before_scaling() {
    let x = word(10, 0, u64::MAX);
    let mut facts = Facts::new();
    add_relation(&mut facts, x.clone(), constant(1), Comparison::LessEqual);
    let scaled = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (
            LogicType::Usize,
            Scale {
                operand: 0,
                factor: u64::MAX,
            },
        ),
    ]);
    let value = facts
        .evaluate_word(
            &scaled,
            &[(0, Some(x.clone()))],
            &mut LogicBudget::default(),
        )
        .unwrap()
        .unwrap();
    let LogicValue::Word(value) = value.value else {
        panic!()
    };
    assert_eq!((value.lower, value.upper), (0, u64::MAX));
    // Both complete expressions algebraically equal zero, but neither may
    // discard an unproved intermediate underflow/overflow.
    for operation in [Sub(0, 1), Add(0, 1)] {
        let query = expression(vec![
            (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
            (LogicType::Usize, Word(1)),
            (LogicType::Usize, operation),
            (LogicType::Usize, Sub(2, 2)),
        ]);
        assert_eq!(
            Facts::new().evaluate_word(
                &query,
                &[(0, Some(x.clone()))],
                &mut LogicBudget::default()
            ),
            Ok(None)
        );
    }
    assert_eq!(
        facts.evaluate_word(&scaled, &[(0, None)], &mut LogicBudget::default()),
        Ok(None)
    );
    assert_eq!(
        facts.evaluate_word(&scaled, &[(0, Some(x))], &mut LogicBudget { remaining: 1 }),
        Err(LogicError::Budget)
    );
}

#[test]
fn scalar_domain_evaluation_preserves_boolean_shape_and_checks_all_intermediates() {
    let low = word(10, 0, 9);
    let high = word(20, 0, 9);
    let leaves = [(0, Some(low.clone())), (1, Some(high.clone()))];
    let mut facts = Facts::new();
    facts
        .extend_difference(&low, &high, 0, &mut LogicBudget::default())
        .unwrap();
    let comparison = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
        (LogicType::Usize, Sub(1, 0)),
        (LogicType::Usize, Word(3)),
        (LogicType::Bool, LessEqual(2, 3)),
        (LogicType::Bool, Not(4)),
    ]);
    let value = facts
        .evaluate_scalar(&comparison, &leaves, &mut LogicBudget::default())
        .unwrap()
        .unwrap();
    let LogicValue::BoolComparison {
        left,
        right,
        comparison: op,
        negated,
        word_type,
    } = value.value
    else {
        panic!()
    };
    assert!(negated);
    assert_eq!(word_type, WordType::Usize);
    assert_eq!(op, WordComparison::LessEqual);
    assert_eq!((left.lower, left.upper), (0, 9));
    assert_eq!(left.terms, BTreeMap::from([(10, -1), (20, 1)]));
    assert_eq!(right, AffineValue::exact(3));
    assert_eq!(
        Facts::new().evaluate_scalar(&comparison, &leaves, &mut LogicBudget::default()),
        Ok(None)
    );
    let cancellation = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(0, 1)),
        (LogicType::Usize, Sub(2, 1)),
        (LogicType::Bool, Equal(3, 0)),
    ]);
    assert_eq!(
        Facts::new().evaluate_scalar(
            &cancellation,
            &[(0, Some(word(10, 0, u64::MAX)))],
            &mut LogicBudget::default()
        ),
        Ok(None)
    );
    assert_eq!(
        facts.evaluate_scalar(&comparison, &leaves, &mut LogicBudget { remaining: 1 }),
        Err(LogicError::Budget)
    );
}

#[test]
fn imported_difference_bounds_keep_types_and_reject_contradictions() {
    let mut facts = Facts::new();
    let x = word(10, 0, 9);
    let y = word(20, 0, 9);
    facts
        .extend_difference(&x, &y, -1, &mut LogicBudget::default())
        .unwrap();
    assert_eq!(
        facts.extend_difference(&y, &x, 0, &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
    let result = facts
        .evaluate_word(
            &difference(),
            &[(0, Some(x.clone())), (1, Some(y.clone()))],
            &mut LogicBudget::default(),
        )
        .unwrap()
        .unwrap();
    let LogicValue::Word(result) = result.value else {
        panic!()
    };
    assert_eq!((result.lower, result.upper), (1, 9));
    let mut other = y;
    other.ty = LogicType::U64;
    assert_eq!(
        Facts::new().extend_difference(&x, &other, 0, &mut LogicBudget::default()),
        Err(LogicError::TypeMismatch)
    );
    assert_eq!(
        Facts::new().extend_difference(&constant(3), &constant(1), 0, &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
}

#[test]
fn relation_checked_comparison_capture_keeps_known_truth_and_operand_shape() {
    let low = word(10, 0, 9);
    let high = word(20, 0, 9);
    let mut facts = Facts::new();
    add_relation(&mut facts, low.clone(), high.clone(), Comparison::LessEqual);
    let mut e = difference();
    e.nodes.extend([
        LogicNode {
            ty: LogicType::Usize,
            kind: Word(9),
        },
        LogicNode {
            ty: LogicType::Bool,
            kind: LessEqual(2, 3),
        },
    ]);
    e.root = 4;
    let leaves = [(0, Some(low)), (1, Some(high))];
    let captured = facts
        .evaluate_scalar(&e, &leaves, &mut LogicBudget::default())
        .unwrap()
        .unwrap();
    assert!(matches!(captured.value, LogicValue::BoolComparison { .. }));
    assert_eq!(captured.value.known_boolean(), Some(true));
    let query = expression(vec![(LogicType::Bool, Binder(LogicBinder::Parameter(0)))]);
    assert_eq!(
        facts.proves(&query, &[(0, Some(captured))], &mut LogicBudget::default()),
        Ok(true)
    );
    assert_eq!(
        Facts::new().evaluate_scalar(&e, &leaves, &mut LogicBudget::default()),
        Ok(None)
    );
}

#[test]
fn checked_scalar_reduction_never_admits_dead_source_nodes() {
    // This dead term comes from the input, unlike operands made redundant by
    // substituting an already checked arithmetic result.
    let dead = expression(vec![
        (LogicType::Usize, Word(0)),
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
    ]);
    assert_eq!(
        Facts::new().evaluate_scalar(
            &dead,
            &[(1, Some(word(10, 0, 9)))],
            &mut LogicBudget::default(),
        ),
        Err(LogicError::InvalidNode),
    );
}
