use super::*;
use LogicNodeKind::*;

fn capture(e: &Expr, inputs: &[Value]) -> Result<Value, LogicError> {
    e.evaluate_for_capture(
        inputs,
        &[],
        &mut |_, _, _, _| Err(LogicError::Unbound),
        &mut |_, _| Err(LogicError::Unbound),
        &mut LogicBudget::default(),
    )
}

fn input(atom: u32, value: u64) -> Value {
    Value {
        ty: LogicType::Usize,
        value: LogicValue::Word(AffineValue::identified(atom, value, value).unwrap()),
    }
}

#[test]
fn known_comparisons_retain_sources_but_ordinary_queries_return_truth() {
    for operation in [Equal(0, 1), Less(0, 1), LessEqual(0, 1)] {
        for initial in [0, 3, 7] {
            let e = expression(vec![
                (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
                (LogicType::Usize, Word(3)),
                (LogicType::Bool, operation.clone()),
            ]);
            let captured = capture(&e, &[input(10, initial)]).unwrap();
            assert!(matches!(captured.value, LogicValue::BoolComparison { .. }));
            let expected = evaluate(&e, &[input(10, initial)]).unwrap();
            assert_eq!(captured.value.bool_equal(&expected.value), Some(true));
            let query = expression(vec![(LogicType::Bool, Binder(LogicBinder::Parameter(0)))]);
            assert_eq!(
                evaluate(&query, std::slice::from_ref(&captured)),
                Ok(expected)
            );
            let template = scalar_template::ScalarTemplate::capture(
                &captured.value,
                &mut |atom, _, _| Ok(*atom),
                &mut LogicBudget::default(),
            )
            .unwrap();
            assert_eq!(
                template.inputs(&mut LogicBudget::default()).unwrap(),
                BTreeMap::from([(10, scalar_template::ScalarKind::Word)])
            );
            for current in [0, 3, 7] {
                let rebuilt = template
                    .instantiate(
                        &mut |atom, kind, _| {
                            assert_eq!((*atom, kind), (10, scalar_template::ScalarKind::Word));
                            Ok(input(20, current).value)
                        },
                        &mut LogicBudget::default(),
                    )
                    .unwrap();
                assert_eq!(rebuilt, evaluate(&e, &[input(20, current)]).unwrap().value);
            }
            let mut literal = e.clone();
            literal.nodes[0].kind = Word(initial);
            assert!(matches!(
                capture(&literal, &[]).unwrap().value,
                LogicValue::Bool(Some(_))
            ));
        }
    }
}

#[test]
fn capture_boolean_rewrites_use_shapes_instead_of_equal_entry_truth() {
    let base = vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(3)),
        (LogicType::Bool, Less(0, 1)),
    ];
    let inputs = [input(10, 0), input(20, 0)];
    let original = capture(&expression(base.clone()), &inputs).unwrap();
    for (literal, operation) in [
        (true, Equal(2, 3)),
        (false, Equal(2, 3)),
        (true, And(2, 3)),
        (false, Or(2, 3)),
    ] {
        let mut nodes = base.clone();
        nodes.extend([
            (LogicType::Bool, Bool(literal)),
            (LogicType::Bool, operation),
        ]);
        let result = capture(&expression(nodes), &inputs).unwrap();
        assert!(matches!(result.value, LogicValue::BoolComparison { .. }));
    }
    for operation in [And(2, 4), Or(2, 4), Equal(2, 4)] {
        let mut nodes = base.clone();
        nodes.extend([
            (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
            (LogicType::Bool, Less(3, 1)),
            (LogicType::Bool, operation),
        ]);
        // Both inputs are initially zero, but their future values are independent.
        assert!(matches!(
            capture(&expression(nodes.clone()), &inputs).unwrap().value,
            LogicValue::BoolBinary { .. }
        ));
        nodes[3].1 = Binder(LogicBinder::Parameter(0));
        let same = capture(&expression(nodes), &inputs).unwrap();
        assert!(same == original || same.value == LogicValue::Bool(Some(true)));
    }
    let mut nodes = base;
    nodes.extend([(LogicType::Bool, Not(2)), (LogicType::Bool, And(2, 3))]);
    assert_eq!(
        capture(&expression(nodes), &inputs).unwrap().value,
        LogicValue::Bool(Some(false))
    );
}

#[test]
fn capture_does_not_skip_overflow_or_reset_the_shared_budget() {
    let e = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(0, 1)),
        (LogicType::Usize, Sub(2, 1)),
        (LogicType::Bool, Equal(0, 3)),
    ]);
    assert_eq!(
        capture(&e, &[input(10, u64::MAX)]),
        Err(LogicError::Overflow)
    );
    assert_eq!(
        e.evaluate_for_capture(
            &[input(10, 0)],
            &[],
            &mut |_, _, _, _| Err(LogicError::Unbound),
            &mut |_, _| Err(LogicError::Unbound),
            &mut LogicBudget { remaining: 1 }
        ),
        Err(LogicError::Budget)
    );
}

#[test]
fn known_false_comparison_cannot_be_imported_as_a_boolean_fact() {
    use crate::predicate_logic::facts::EstablishedFacts;
    let e = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(3)),
        (LogicType::Bool, Less(0, 1)),
    ]);
    let query = expression(vec![(LogicType::Bool, Binder(LogicBinder::Parameter(0)))]);
    for initial in [0, 7] {
        let value = capture(&e, &[input(10, initial)]).unwrap();
        let mut facts = EstablishedFacts::new();
        assert_eq!(
            facts.proves(
                &query,
                &[(0, Some(value.clone()))],
                &mut LogicBudget::default()
            ),
            Ok(initial == 0)
        );
        assert_eq!(
            facts.extend(
                &query,
                &[(0, Some(value.clone()))],
                &mut LogicBudget::default()
            ),
            if initial == 0 {
                Ok(())
            } else {
                Err(LogicError::Unproved)
            }
        );
        let equality = expression(vec![
            (LogicType::Bool, Binder(LogicBinder::Parameter(0))),
            (LogicType::Bool, Bool(initial != 0)),
            (LogicType::Bool, Equal(0, 1)),
        ]);
        assert_eq!(
            facts.extend(&equality, &[(0, Some(value))], &mut LogicBudget::default()),
            Err(LogicError::Unproved)
        );
    }
}

#[test]
fn known_boolean_atoms_keep_identity_through_capture_and_drop_entry_truth_in_templates() {
    for initial in [false, true] {
        for negated in [false, true] {
            let input = Value {
                ty: LogicType::Bool,
                value: LogicValue::BoolAtom {
                    atom: 10,
                    negated,
                    known: Some(initial),
                },
            };
            let direct = expression(vec![(LogicType::Bool, Binder(LogicBinder::Parameter(0)))]);
            assert_eq!(
                capture(&direct, std::slice::from_ref(&input)),
                Ok(input.clone())
            );
            assert_eq!(
                evaluate(&direct, std::slice::from_ref(&input))
                    .unwrap()
                    .value,
                LogicValue::Bool(Some(initial ^ negated))
            );
            let not = expression(vec![
                (LogicType::Bool, Binder(LogicBinder::Parameter(0))),
                (LogicType::Bool, Not(0)),
            ]);
            let inverted = capture(&not, std::slice::from_ref(&input)).unwrap();
            assert_eq!(inverted.value.known_boolean(), Some(!(initial ^ negated)));
            assert!(
                matches!(inverted.value, LogicValue::BoolAtom { atom: 10, known: Some(value), .. } if value == initial)
            );
            let template = scalar_template::ScalarTemplate::capture(
                &input.value,
                &mut |atom, kind, _| {
                    assert_eq!(kind, scalar_template::ScalarKind::Bool);
                    Ok(*atom)
                },
                &mut LogicBudget::default(),
            )
            .unwrap();
            assert_eq!(
                template.inputs(&mut LogicBudget::default()).unwrap(),
                BTreeMap::from([(10, scalar_template::ScalarKind::Bool)])
            );
            for current in [None, Some(false), Some(true)] {
                let result: LogicValue<u32, u32> = template
                    .instantiate(
                        &mut |_, _, _| {
                            Ok(LogicValue::BoolAtom {
                                atom: 20,
                                negated: false,
                                known: current,
                            })
                        },
                        &mut LogicBudget::default(),
                    )
                    .unwrap();
                assert_eq!(
                    result,
                    LogicValue::BoolAtom {
                        atom: 20,
                        negated,
                        known: current
                    }
                );
                assert_eq!(result.known_boolean(), current.map(|v| v ^ negated));
            }
            assert_eq!(
                input.value.with_known_boolean(initial ^ negated),
                Ok(input.value.clone())
            );
            assert_eq!(
                input.value.with_known_boolean(!(initial ^ negated)),
                Err(LogicError::Unproved)
            );
        }
    }
    let unknown: LogicValue<u32, u32> = LogicValue::BoolAtom {
        atom: 10,
        negated: true,
        known: None,
    };
    assert_eq!(
        unknown.with_known_boolean(true).unwrap(),
        LogicValue::BoolAtom {
            atom: 10,
            negated: true,
            known: Some(false)
        }
    );
}

#[test]
fn equal_known_boolean_atoms_are_not_interchangeable_capture_sources() {
    let inputs = [10, 20].map(|atom| Value {
        ty: LogicType::Bool,
        value: LogicValue::BoolAtom {
            atom,
            negated: false,
            known: Some(true),
        },
    });
    for operation in [Equal(0, 1), And(0, 1), Or(0, 1)] {
        let e = expression(vec![
            (LogicType::Bool, Binder(LogicBinder::Parameter(0))),
            (LogicType::Bool, Binder(LogicBinder::Parameter(1))),
            (LogicType::Bool, operation),
        ]);
        assert_eq!(
            evaluate(&e, &inputs).unwrap().value,
            LogicValue::Bool(Some(true))
        );
        assert!(matches!(
            capture(&e, &inputs).unwrap().value,
            LogicValue::BoolBinary { .. }
        ));
    }
    let query = expression(vec![(LogicType::Bool, Binder(LogicBinder::Parameter(0)))]);
    let value = Value {
        ty: LogicType::Bool,
        value: LogicValue::BoolAtom {
            atom: 10,
            negated: true,
            known: Some(true),
        },
    };
    let mut facts = facts::EstablishedFacts::new();
    assert_eq!(
        facts.extend(
            &query,
            &[(0, Some(value.clone()))],
            &mut LogicBudget::default()
        ),
        Err(LogicError::Unproved)
    );
    assert_eq!(
        facts.proves(&query, &[(0, Some(value))], &mut LogicBudget::default()),
        Ok(false)
    );
}

#[test]
fn boolean_combinations_do_not_hide_numeric_definedness_failures() {
    let e = expression(vec![
        (LogicType::Bool, Bool(false)),
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(1, 2)),
        (LogicType::Bool, Equal(1, 3)),
        (LogicType::Bool, And(0, 4)),
    ]);
    assert_eq!(
        capture(&e, &[input(10, u64::MAX)]),
        Err(LogicError::Overflow)
    );
    assert_eq!(
        evaluate(&e, &[input(10, u64::MAX)]),
        Err(LogicError::Overflow)
    );
}
