use super::*;
use LogicNodeKind::*;

fn flag() -> Value {
    Value {
        ty: LogicType::Bool,
        value: LogicValue::BoolAtom {
            atom: 30,
            negated: false,
            known: None,
        },
    }
}
fn clause(op: Comparison) -> LogicExpression<u32> {
    expression(vec![
        (LogicType::Bool, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(2))),
        (
            LogicType::Bool,
            match op {
                Comparison::Equal => Equal(1, 2),
                Comparison::Less => Less(1, 2),
                Comparison::LessEqual => LessEqual(1, 2),
            },
        ),
        (LogicType::Bool, Or(0, 3)),
    ])
}
fn import(
    facts: &mut Facts,
    e: &LogicExpression<u32>,
    left: Option<Value>,
    right: Option<Value>,
) -> Result<(), LogicError> {
    facts.extend(
        e,
        &[(0, Some(flag())), (1, left), (2, right)],
        &mut LogicBudget::default(),
    )
}
fn assume_flag(facts: &mut Facts, truth: bool) -> Result<(), LogicError> {
    let mut e = expression(vec![(LogicType::Bool, Binder(LogicBinder::Parameter(0)))]);
    if !truth {
        e.nodes.push(LogicNode {
            ty: LogicType::Bool,
            kind: Not(0),
        });
        e.root = 1;
    }
    facts.extend(&e, &[(0, Some(flag()))], &mut LogicBudget::default())
}
fn entails(facts: &Facts, op: Comparison, a: &Value, b: &Value) -> Result<bool, LogicError> {
    facts.entails(op, a, b, &mut LogicBudget::default())
}

#[test]
fn propositional_numeric_observations_keep_types_and_do_not_justify_new_arithmetic() {
    use super::boolean::{atom, binary, import as import_bool, known, typed};
    let proposition = |word_type| LogicValue::BoolComparison {
        word_type,
        comparison: WordComparison::LessEqual,
        left: AffineValue::identified(1, 0, u64::MAX).unwrap(),
        right: AffineValue::exact(8),
        negated: false,
    };
    let p = proposition(WordType::Usize);
    let mut facts = Facts::new();
    import_bool(
        &mut facts,
        binary(BooleanOperation::Or, p.clone(), atom(30)),
        true,
    )
    .unwrap();
    import_bool(
        &mut facts,
        binary(BooleanOperation::Or, p.clone(), atom(30).bool_not()),
        true,
    )
    .unwrap();
    assert_eq!(known(&facts, p.clone()).unwrap(), Some(true));
    assert_eq!(known(&facts, atom(30)).unwrap(), None);
    assert_eq!(known(&facts, proposition(WordType::U64)).unwrap(), None);
    let identity = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(u64::MAX)),
        (LogicType::Usize, Add(0, 1)),
        (LogicType::Bool, Equal(2, 2)),
    ]);
    assert!(
        !facts
            .proves(
                &identity,
                &[(0, Some(word(1, 0, u64::MAX)))],
                &mut LogicBudget::default()
            )
            .unwrap()
    );
    assert!(
        facts
            .entails(
                Comparison::Equal,
                &typed(p),
                &typed(LogicValue::Bool(Some(true))),
                &mut LogicBudget::default()
            )
            .unwrap()
    );
}

#[test]
fn false_disjunct_exposes_typed_numeric_bounds_and_checked_arithmetic() {
    let x = word(1, 0, u64::MAX);
    let limit = constant(7);
    let mut facts = Facts::new();
    import(
        &mut facts,
        &clause(Comparison::Less),
        Some(x.clone()),
        Some(limit.clone()),
    )
    .unwrap();
    assert_eq!(entails(&facts, Comparison::Less, &x, &limit), Ok(false));
    assume_flag(&mut facts, false).unwrap();
    assert_eq!(entails(&facts, Comparison::Less, &x, &limit), Ok(true));
    let refined = facts
        .refine(x.clone(), &mut LogicBudget::default())
        .unwrap();
    let LogicValue::Word(value) = refined.value else {
        panic!()
    };
    assert_eq!((value.lower, value.upper), (0, 6));
    let next = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(0, 1)),
    ]);
    let value = facts
        .evaluate_word(&next, &[(0, Some(x))], &mut LogicBudget::default())
        .unwrap()
        .unwrap();
    let LogicValue::Word(value) = value.value else {
        panic!()
    };
    assert_eq!((value.lower, value.upper), (1, 7));
}

#[test]
fn numeric_relations_force_boolean_results_and_enable_further_numeric_relations() {
    let x = word(1, 0, 20);
    let y = word(2, 0, 20);
    let mut facts = Facts::new();
    import(
        &mut facts,
        &clause(Comparison::Less),
        Some(x.clone()),
        Some(y.clone()),
    )
    .unwrap();
    add_relation(&mut facts, y.clone(), x.clone(), Comparison::LessEqual);
    assert_eq!(
        facts
            .refine(flag(), &mut LogicBudget::default())
            .unwrap()
            .value
            .known_boolean(),
        Some(true)
    );
    // The true flag forces the bound in !flag || x <= 10.
    let mut next = clause(Comparison::LessEqual);
    next.nodes.insert(
        3,
        LogicNode {
            ty: LogicType::Bool,
            kind: Not(0),
        },
    );
    next.nodes[4].kind = LessEqual(1, 2);
    next.nodes[5].kind = Or(3, 4);
    next.root = 5;
    import(&mut facts, &next, Some(x.clone()), Some(constant(10))).unwrap();
    assert_eq!(
        entails(&facts, Comparison::LessEqual, &y, &constant(10)),
        Ok(true)
    );
}

#[test]
fn unavailable_inputs_and_other_word_types_do_not_acquire_constraints() {
    let x = word(1, 0, 20);
    let y = word(2, 0, 20);
    let mut missing = Facts::new();
    import(
        &mut missing,
        &clause(Comparison::Less),
        None,
        Some(y.clone()),
    )
    .unwrap();
    assume_flag(&mut missing, false).unwrap();
    assert_eq!(entails(&missing, Comparison::Less, &x, &y), Ok(false));
    let mut facts = Facts::new();
    import(
        &mut facts,
        &clause(Comparison::Less),
        Some(x.clone()),
        Some(y.clone()),
    )
    .unwrap();
    assume_flag(&mut facts, false).unwrap();
    let mut other_x = x.clone();
    other_x.ty = LogicType::U64;
    let mut other_y = y.clone();
    other_y.ty = LogicType::U64;
    assert_eq!(
        entails(&facts, Comparison::Less, &other_x, &other_y),
        Ok(false)
    );
    assert_eq!(entails(&facts, Comparison::Less, &x, &y), Ok(true));
    assert_eq!(
        entails(&facts, Comparison::Less, &word(3, 0, 20), &y),
        Ok(false)
    );
}

#[test]
fn disequality_never_selects_a_numeric_direction_and_negated_order_is_exact() {
    let x = word(1, 0, 20);
    let y = word(2, 0, 20);
    for (operator, expected) in [
        (Equal(0, 1), None),
        (Less(0, 1), Some(Comparison::LessEqual)),
        (LessEqual(0, 1), Some(Comparison::Less)),
    ] {
        let e = expression(vec![
            (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
            (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
            (LogicType::Bool, operator),
            (LogicType::Bool, Not(2)),
        ]);
        let mut facts = Facts::new();
        facts
            .extend(
                &e,
                &[(0, Some(x.clone())), (1, Some(y.clone()))],
                &mut LogicBudget::default(),
            )
            .unwrap();
        assert_eq!(entails(&facts, Comparison::Less, &x, &y), Ok(false));
        if let Some(op) = expected {
            assert_eq!(entails(&facts, op, &y, &x), Ok(true));
        } else {
            assert_eq!(entails(&facts, Comparison::Less, &y, &x), Ok(false));
        }
        assert_eq!(
            facts.proves(
                &e,
                &[(0, Some(x.clone())), (1, Some(y.clone()))],
                &mut LogicBudget::default()
            ),
            Ok(true)
        );
    }
}

#[test]
fn mixed_contradictions_and_budget_failure_publish_nothing() {
    let x = word(1, 0, 20);
    let y = word(2, 0, 20);
    let mut facts = Facts::new();
    import(
        &mut facts,
        &clause(Comparison::Less),
        Some(x.clone()),
        Some(y.clone()),
    )
    .unwrap();
    assume_flag(&mut facts, false).unwrap();
    let before = facts.facts.len();
    assert_eq!(
        facts.extend_difference(&y, &x, 0, &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
    assert_eq!(facts.facts.len(), before);
    assert_eq!(entails(&facts, Comparison::Less, &x, &y), Ok(true));
    let mut budget = LogicBudget { remaining: 1 };
    assert_eq!(
        facts.extend(
            &clause(Comparison::Equal),
            &[(0, Some(flag())), (1, Some(x)), (2, Some(y))],
            &mut budget
        ),
        Err(LogicError::Budget)
    );
    assert_eq!(facts.facts.len(), before);
}

#[test]
fn a_true_boolean_branch_cannot_hide_new_undefined_arithmetic() {
    let mut facts = Facts::new();
    assume_flag(&mut facts, true).unwrap();
    let e = expression(vec![
        (LogicType::Bool, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(1, 2)),
        (LogicType::Usize, Sub(3, 1)),
        (LogicType::Bool, Equal(4, 2)),
        (LogicType::Bool, Or(0, 5)),
    ]);
    assert_eq!(
        facts.proves(
            &e,
            &[(0, Some(flag())), (1, Some(constant(u64::MAX)))],
            &mut LogicBudget::default()
        ),
        Ok(false)
    );
}

#[test]
fn established_mixed_arithmetic_bounds_do_not_erase_new_definedness_checks() {
    let x = word(1, 0, u64::MAX);
    let e = expression(vec![
        (LogicType::Bool, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(1, 2)),
        (LogicType::Usize, Word(7)),
        (LogicType::Bool, LessEqual(3, 4)),
        (LogicType::Bool, Or(0, 5)),
    ]);
    let mut facts = Facts::new();
    facts
        .extend(
            &e,
            &[(0, Some(flag())), (1, Some(x.clone()))],
            &mut LogicBudget::default(),
        )
        .unwrap();
    assume_flag(&mut facts, false).unwrap();
    assert_eq!(
        entails(&facts, Comparison::Less, &x, &constant(7)),
        Ok(true)
    );
    let query = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(0, 1)),
        (LogicType::Usize, Word(7)),
        (LogicType::Bool, LessEqual(2, 3)),
    ]);
    assert_eq!(
        facts.proves(&query, &[(0, Some(x))], &mut LogicBudget::default()),
        Ok(true)
    );
}

fn joint_numeric_guarantee(facts: &mut Facts, proposition: LogicValue<u32, u32>) {
    use super::boolean::{atom, binary, import};
    for flag in [atom(30), atom(30).bool_not()] {
        import(
            facts,
            binary(BooleanOperation::Or, flag, proposition.clone()),
            true,
        )
        .unwrap();
    }
}

#[test]
fn joint_boolean_guarantees_feed_typed_bounds_and_new_checked_expressions() {
    for ty in [LogicType::Usize, LogicType::U64] {
        let mut x = word(1, 0, u64::MAX);
        x.ty = ty;
        let word_type = if ty == LogicType::Usize {
            WordType::Usize
        } else {
            WordType::U64
        };
        let mut facts = Facts::new();
        joint_numeric_guarantee(
            &mut facts,
            LogicValue::BoolComparison {
                word_type,
                comparison: WordComparison::LessEqual,
                left: AffineValue::identified(1, 0, u64::MAX).unwrap(),
                right: AffineValue::exact(8),
                negated: false,
            },
        );
        let refined = facts
            .refine(x.clone(), &mut LogicBudget::default())
            .unwrap();
        let LogicValue::Word(value) = refined.value else {
            panic!()
        };
        assert_eq!((value.lower, value.upper), (0, 8));
        assert!(!value.terms.is_empty());
        let next = expression(vec![
            (ty, Binder(LogicBinder::Parameter(0))),
            (ty, Word(1)),
            (ty, Add(0, 1)),
        ]);
        let value = facts
            .evaluate_word(&next, &[(0, Some(x.clone()))], &mut LogicBudget::default())
            .unwrap()
            .unwrap();
        let LogicValue::Word(value) = value.value else {
            panic!()
        };
        assert_eq!((value.lower, value.upper), (1, 9));
        let mut other = x;
        other.ty = if ty == LogicType::Usize {
            LogicType::U64
        } else {
            LogicType::Usize
        };
        let other = facts.refine(other, &mut LogicBudget::default()).unwrap();
        let LogicValue::Word(other) = other.value else {
            panic!()
        };
        assert_eq!((other.lower, other.upper), (0, u64::MAX));
    }
}

#[test]
fn forced_false_equality_never_selects_a_numeric_order() {
    use super::boolean::{known, typed};
    let equal = LogicValue::BoolComparison {
        word_type: WordType::Usize,
        comparison: WordComparison::Equal,
        left: AffineValue::identified(1, 0, 10).unwrap(),
        right: AffineValue::identified(2, 0, 10).unwrap(),
        negated: false,
    };
    let mut facts = Facts::new();
    joint_numeric_guarantee(&mut facts, equal.clone().bool_not());
    assert_eq!(known(&facts, equal.clone()).unwrap(), Some(false));
    for (a, b) in [(1, 2), (2, 1)] {
        assert!(
            !facts
                .entails(
                    Comparison::Less,
                    &word(a, 0, 10),
                    &word(b, 0, 10),
                    &mut LogicBudget::default()
                )
                .unwrap()
        );
    }
    assert!(
        facts
            .entails(
                Comparison::Equal,
                &typed(equal),
                &typed(LogicValue::Bool(Some(false))),
                &mut LogicBudget::default()
            )
            .unwrap()
    );
}

#[test]
fn jointly_forced_conflicting_numeric_premises_are_rejected_before_publication() {
    use super::boolean::{atom, binary, import};
    let relation = |left, right, negated| LogicValue::BoolComparison {
        word_type: WordType::Usize,
        comparison: WordComparison::LessEqual,
        left: AffineValue::identified(left, 0, 10).unwrap(),
        right: AffineValue::identified(right, 0, 10).unwrap(),
        negated,
    };
    let mut facts = Facts::new();
    joint_numeric_guarantee(&mut facts, relation(1, 2, false));
    import(
        &mut facts,
        binary(BooleanOperation::Or, atom(31), relation(1, 2, true)),
        true,
    )
    .unwrap();
    let before = facts.facts.len();
    assert_eq!(
        import(
            &mut facts,
            binary(
                BooleanOperation::Or,
                atom(31).bool_not(),
                relation(1, 2, true)
            ),
            true
        ),
        Err(LogicError::Unproved)
    );
    assert_eq!(facts.facts.len(), before);
    assert!(
        facts
            .entails(
                Comparison::LessEqual,
                &word(1, 0, 10),
                &word(2, 0, 10),
                &mut LogicBudget::default()
            )
            .unwrap()
    );
}

fn order_observation(ty: WordType, left: u32, right: u32, negated: bool) -> LogicValue<u32, u32> {
    LogicValue::BoolComparison {
        word_type: ty,
        comparison: WordComparison::LessEqual,
        left: AffineValue::identified(left, 0, 10).unwrap(),
        right: AffineValue::identified(right, 0, 10).unwrap(),
        negated,
    }
}

#[test]
fn impossible_numeric_branches_force_only_shared_boolean_conclusions() {
    use super::boolean::{atom, binary, import, known};
    for ty in [WordType::Usize, WordType::U64] {
        let mut facts = Facts::new();
        // Antisymmetry excludes unequal values ordered in both directions.
        let unequal = LogicValue::BoolComparison {
            word_type: ty,
            comparison: WordComparison::Equal,
            left: AffineValue::identified(1, 0, 10).unwrap(),
            right: AffineValue::identified(2, 0, 10).unwrap(),
            negated: true,
        };
        // Use <= both ways as one numeric equality and != as its opposite.
        // Equality's complement must not arbitrarily choose a direction.
        let equal = unequal.bool_not();
        let xy = order_observation(ty, 1, 2, false);
        let yx = order_observation(ty, 2, 1, false);
        let query = binary(
            BooleanOperation::Or,
            equal,
            binary(BooleanOperation::Or, xy.bool_not(), yx.bool_not()),
        );
        assert_eq!(known(&facts, query).unwrap(), Some(true));

        // x <= y and y < x cannot both hold. Represent strict order directly
        // in the clause IR to keep two independent numeric observations.
        let mut first = clause(Comparison::LessEqual);
        for node in &mut first.nodes {
            if node.ty == LogicType::Usize {
                node.ty = ty.logic_type();
            }
        }
        let mut second = clause(Comparison::Less);
        for node in &mut second.nodes {
            if node.ty == LogicType::Usize {
                node.ty = ty.logic_type();
            }
        }
        let x = Value {
            ty: ty.logic_type(),
            ..word(1, 0, 10)
        };
        let y = Value {
            ty: ty.logic_type(),
            ..word(2, 0, 10)
        };
        self::import(&mut facts, &first, Some(x.clone()), Some(y.clone())).unwrap();
        self::import(&mut facts, &second, Some(y), Some(x)).unwrap();
        let before = facts.facts.len();
        assert_eq!(known(&facts, atom(30)).unwrap(), Some(true));
        assert_eq!(
            known(&facts, order_observation(ty, 1, 2, false)).unwrap(),
            None
        );
        assert_eq!(facts.facts.len(), before);
        assert_eq!(
            import(&mut facts, atom(30), false),
            Err(LogicError::Unproved)
        );
        assert_eq!(facts.facts.len(), before);
    }
}

#[test]
fn numeric_model_filter_keeps_nominal_types_and_feasible_alternatives() {
    use super::boolean::{atom, binary, import, known};
    let mut facts = Facts::new();
    import(
        &mut facts,
        binary(
            BooleanOperation::Or,
            atom(30),
            order_observation(WordType::Usize, 1, 2, false),
        ),
        true,
    )
    .unwrap();
    import(
        &mut facts,
        binary(
            BooleanOperation::Or,
            atom(30),
            order_observation(WordType::U64, 1, 2, true),
        ),
        true,
    )
    .unwrap();
    assert_eq!(known(&facts, atom(30)).unwrap(), None);
    let mut facts = Facts::new();
    import(
        &mut facts,
        binary(
            BooleanOperation::Or,
            atom(30),
            order_observation(WordType::Usize, 1, 2, false),
        ),
        true,
    )
    .unwrap();
    import(
        &mut facts,
        binary(
            BooleanOperation::Or,
            atom(30),
            order_observation(WordType::Usize, 2, 1, false),
        ),
        true,
    )
    .unwrap();
    // Equality is feasible, hence flag can still be false.
    assert_eq!(known(&facts, atom(30)).unwrap(), None);
}

#[test]
fn disequality_models_preserve_both_orders_and_distinct_source_atoms() {
    use super::boolean::{atom, binary, import, known};
    let mut facts = Facts::new();
    import(
        &mut facts,
        LogicValue::BoolComparison {
            word_type: WordType::Usize,
            comparison: WordComparison::Equal,
            left: AffineValue::identified(1, 0, 10).unwrap(),
            right: AffineValue::identified(2, 0, 10).unwrap(),
            negated: true,
        },
        true,
    )
    .unwrap();
    for (a, b) in [(1, 2), (2, 1)] {
        assert_eq!(
            known(&facts, order_observation(WordType::Usize, a, b, false)).unwrap(),
            None
        );
    }
    let mut facts = Facts::new();
    import(
        &mut facts,
        binary(
            BooleanOperation::Or,
            atom(30),
            order_observation(WordType::Usize, 1, 2, false),
        ),
        true,
    )
    .unwrap();
    import(
        &mut facts,
        binary(
            BooleanOperation::Or,
            atom(30),
            order_observation(WordType::Usize, 1, 3, true),
        ),
        true,
    )
    .unwrap();
    assert_eq!(known(&facts, atom(30)).unwrap(), None);
}
