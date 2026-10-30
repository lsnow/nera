use super::*;

type Expr = LogicExpression<u32>;
type Value = TypedLogicValue<u32, u32, u32>;
fn expression(nodes: Vec<(LogicType<u32>, LogicNodeKind<u32>)>) -> Expr {
    Expr {
        root: nodes.len() as u32 - 1,
        nodes: nodes
            .into_iter()
            .map(|(ty, kind)| LogicNode { ty, kind })
            .collect(),
    }
}
fn validate(e: &Expr) -> Result<LogicType<u32>, LogicError> {
    e.validate(
        &[],
        &[],
        &|_, _, _, _| None,
        &|_, _| None,
        &mut LogicBudget::default(),
    )
}
fn evaluate(e: &Expr, parameters: &[Value]) -> Result<Value, LogicError> {
    e.evaluate(
        parameters,
        &[],
        &mut |_, _, _, _| Err(LogicError::Unbound),
        &mut |_, _| Err(LogicError::Unbound),
        &mut LogicBudget::default(),
    )
}
#[test]
fn nominal_words_and_forward_binders_are_rejected() {
    use LogicNodeKind::*;
    assert_eq!(
        validate(&expression(vec![
            (LogicType::U64, Word(1)),
            (LogicType::Usize, Word(1)),
            (LogicType::Bool, Equal(0, 1))
        ])),
        Err(LogicError::TypeMismatch)
    );
    let mut logic = PredicateLogic {
        parameters: vec![],
        existentials: vec![Existential {
            name: "x".into(),
            ty: LogicType::U64,
            default: Some(expression(vec![(
                LogicType::U64,
                Binder(LogicBinder::Existential(0)),
            )])),
        }],
        constraints: vec![],
    };
    assert_eq!(
        logic.validate(&[], &|_, _, _, _| None, &|_, _| None),
        Err(LogicError::Unbound)
    );
    logic.existentials[0].default = Some(expression(vec![(LogicType::U64, Word(7))]));
    assert!(
        logic
            .validate(&[], &|_, _, _, _| None, &|_, _| None)
            .is_ok()
    );
}
#[test]
fn malformed_dag_and_dead_terms_do_not_pass_admission() {
    use LogicNodeKind::*;
    assert_eq!(
        validate(&expression(vec![(LogicType::U64, Add(0, 0))])),
        Err(LogicError::InvalidNode)
    );
    assert_eq!(
        validate(&expression(vec![
            (LogicType::U64, Word(1)),
            (LogicType::U64, Word(2))
        ])),
        Err(LogicError::InvalidNode)
    );
}
#[test]
fn arithmetic_checks_each_operation_before_cancellation() {
    use LogicNodeKind::*;
    let overflow = expression(vec![
        (LogicType::U64, Word(u64::MAX)),
        (LogicType::U64, Word(1)),
        (LogicType::U64, Add(0, 1)),
        (LogicType::U64, Sub(2, 2)),
    ]);
    assert_eq!(evaluate(&overflow, &[]), Err(LogicError::Overflow));
    let underflow = expression(vec![
        (LogicType::U64, Word(0)),
        (LogicType::U64, Word(1)),
        (LogicType::U64, Sub(0, 1)),
    ]);
    assert_eq!(evaluate(&underflow, &[]), Err(LogicError::Overflow));
    let x = AffineValue::variable(1u32, 0, u64::MAX).unwrap();
    assert_eq!(x.sub(&x).unwrap(), AffineValue::exact(0));
    assert_eq!(x.add(&AffineValue::exact(1)), Err(LogicError::Overflow));
    assert_eq!(x.scale(2), Err(LogicError::Overflow));
}
#[test]
fn affine_equality_requires_the_same_symbol() {
    let a = AffineValue::variable(1u32, 2, 10).unwrap();
    let b = AffineValue::variable(2u32, 2, 10).unwrap();
    assert_eq!(a.equal(&b), None);
    assert_eq!(a.equal(&a), Some(true));
    assert_eq!(
        a.add(&AffineValue::exact(3)).unwrap().sub(&a).unwrap(),
        AffineValue::exact(3)
    );
    let mut sum = AffineValue::exact(0);
    for id in 0..MAX_LINEAR_TERMS as u32 {
        sum = sum.add(&AffineValue::variable(id, 0, 1).unwrap()).unwrap();
    }
    assert_eq!(
        sum.add(&AffineValue::variable(99, 0, 1).unwrap()),
        Err(LogicError::Budget)
    );
}

#[test]
fn refined_singleton_values_are_equal_without_merging_symbol_identity() {
    let mut a = AffineValue::variable(1u32, 2, 10).unwrap();
    let mut b = AffineValue::variable(2u32, 2, 10).unwrap();
    a.lower = 6;
    a.upper = 6;
    assert_eq!(a.equal(&b), None);
    b.lower = 6;
    b.upper = 6;
    assert_eq!(a.equal(&b), Some(true));
    assert_eq!(a.equal(&AffineValue::exact(6)), Some(true));
    assert_ne!(a.terms, b.terms);
    b.lower = 7;
    b.upper = 7;
    assert_eq!(a.equal(&b), Some(false));
}
#[test]
fn negation_cannot_hide_boolean_expansion() {
    use LogicNodeKind::*;
    let mut nodes = vec![(LogicType::Bool, Bool(true))];
    let mut current = 0;
    for _ in 0..3 {
        let not = nodes.len() as u32;
        nodes.push((LogicType::Bool, Not(current)));
        current = nodes.len() as u32;
        nodes.push((LogicType::Bool, And(not, not)));
    }
    assert!(validate(&expression(nodes.clone())).is_ok());
    let not = nodes.len() as u32;
    nodes.push((LogicType::Bool, Not(current)));
    nodes.push((LogicType::Bool, And(not, not)));
    assert_eq!(validate(&expression(nodes)), Err(LogicError::Budget));
}
#[test]
fn substitutions_share_one_budget() {
    let e = expression(vec![(LogicType::Bool, LogicNodeKind::Bool(true))]);
    let mut budget = LogicBudget::default();
    for _ in 0..MAX_SUBSTITUTION_NODES {
        assert!(
            e.validate(&[], &[], &|_, _, _, _| None, &|_, _| None, &mut budget)
                .is_ok()
        );
    }
    assert_eq!(
        e.validate(&[], &[], &|_, _, _, _| None, &|_, _| None, &mut budget),
        Err(LogicError::Budget)
    );
}
#[test]
fn opened_handles_include_declaration_instance_and_opening() {
    let scope = InstanceScope {
        declaration: 7,
        instance: 9,
        opening: 2,
    };
    let opened = OpenedBindings::new(scope, vec![42]).unwrap();
    assert_eq!(opened.read(OpenedBinder { scope, binder: 0 }), Ok(42));
    for foreign in [
        InstanceScope {
            declaration: 8,
            ..scope
        },
        InstanceScope {
            instance: 10,
            ..scope
        },
        InstanceScope {
            opening: 1,
            ..scope
        },
    ] {
        assert_eq!(
            opened.read(OpenedBinder {
                scope: foreign,
                binder: 0
            }),
            Err(LogicError::StaleInstance)
        );
    }
    assert_eq!(
        opened.read(OpenedBinder { scope, binder: 1 }),
        Err(LogicError::Unbound)
    );
}
#[test]
fn explicit_witness_scope_excludes_default_binders() {
    let logic = PredicateLogic {
        parameters: vec![],
        existentials: vec![Existential {
            name: "x".into(),
            ty: LogicType::U64,
            default: None,
        }],
        constraints: vec![],
    };
    let mut args: WitnessArguments<u32, u32> = WitnessArguments::default();
    let check = |args: &WitnessArguments<u32, u32>| {
        args.validate(
            &logic,
            &|_, _, _, _| None,
            &|_, _| None,
            &mut LogicBudget::default(),
        )
    };
    assert_eq!(check(&args), Err(LogicError::MissingWitness));
    args.values.push((
        0,
        expression(vec![(
            LogicType::U64,
            LogicNodeKind::Binder(LogicBinder::Existential(0)),
        )]),
    ));
    assert_eq!(check(&args), Err(LogicError::Unbound));
    args.values[0].1 = expression(vec![(LogicType::U64, LogicNodeKind::Word(42))]);
    assert_eq!(check(&args), Ok(()));
    args.values.push(args.values[0].clone());
    assert_eq!(check(&args), Err(LogicError::DuplicateName));
}
#[test]
fn unknown_boolean_does_not_become_true() {
    let e = expression(vec![(
        LogicType::Bool,
        LogicNodeKind::Binder(LogicBinder::Parameter(0)),
    )]);
    assert_eq!(
        evaluate(
            &e,
            &[Value {
                ty: LogicType::Bool,
                value: LogicValue::Bool(None)
            }]
        )
        .unwrap()
        .value,
        LogicValue::Bool(None)
    );
}

#[test]
fn instantiation_separates_actuals_overrides_and_preceding_defaults() {
    use LogicNodeKind::*;
    let logic = PredicateLogic {
        parameters: vec![LogicParameter {
            position: 0,
            name: "limit".into(),
            ty: LogicType::Usize,
        }],
        existentials: vec![
            Existential {
                name: "used".into(),
                ty: LogicType::Usize,
                default: Some(expression(vec![(
                    LogicType::Usize,
                    Binder(LogicBinder::Parameter(0)),
                )])),
            },
            Existential {
                name: "next".into(),
                ty: LogicType::Usize,
                default: Some(expression(vec![
                    (LogicType::Usize, Binder(LogicBinder::Existential(0))),
                    (LogicType::Usize, Word(1)),
                    (LogicType::Usize, Add(0, 1)),
                ])),
            },
        ],
        constraints: vec![expression(vec![
            (LogicType::Usize, Binder(LogicBinder::Existential(1))),
            (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
            (LogicType::Bool, LessEqual(0, 1)),
        ])],
    };
    let actual = Value {
        ty: LogicType::Usize,
        value: LogicValue::Word(AffineValue::exact(7)),
    };
    let input = Value {
        ty: LogicType::Usize,
        value: LogicValue::Word(AffineValue::exact(6)),
    };
    let explicit = vec![(
        0,
        expression(vec![(LogicType::Usize, Binder(LogicBinder::Parameter(0)))]),
    )];
    let instantiate = |parameters: &[Value],
                       inputs: &[Value],
                       overrides: &[(u32, Expr)],
                       budget: &mut LogicBudget| {
        logic.instantiate(
            parameters,
            inputs,
            overrides,
            &mut |_, _, _, _| Err(LogicError::Unbound),
            &mut |_, _| Err(LogicError::Unbound),
            budget,
        )
    };
    let values = instantiate(
        std::slice::from_ref(&actual),
        std::slice::from_ref(&input),
        &explicit,
        &mut LogicBudget::default(),
    )
    .unwrap();
    assert_eq!(values[0], input);
    assert_eq!(values[1], actual);
    assert_eq!(
        instantiate(
            std::slice::from_ref(&actual),
            &[],
            &[],
            &mut LogicBudget::default()
        ),
        Err(LogicError::Unproved)
    );
    let wrong = Value {
        ty: LogicType::U64,
        ..actual.clone()
    };
    assert_eq!(
        instantiate(
            &[wrong],
            std::slice::from_ref(&input),
            &explicit,
            &mut LogicBudget::default()
        ),
        Err(LogicError::TypeMismatch)
    );
    assert_eq!(
        instantiate(
            &[],
            std::slice::from_ref(&input),
            &explicit,
            &mut LogicBudget::default()
        ),
        Err(LogicError::TypeMismatch)
    );
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES - 2).unwrap();
    assert_eq!(
        instantiate(&[actual], &[input], &explicit, &mut budget),
        Err(LogicError::Budget)
    );
}

#[test]
fn boolean_literals_preserve_identity_without_equating_anonymous_unknowns() {
    use LogicNodeKind::*;
    let atom = |id, negated| Value {
        ty: LogicType::Bool,
        value: LogicValue::BoolAtom {
            atom: id,
            negated,
            known: None,
        },
    };
    let unknown = Value {
        ty: LogicType::Bool,
        value: LogicValue::Bool(None),
    };
    let binary = |op| {
        expression(vec![
            (LogicType::Bool, Binder(LogicBinder::Parameter(0))),
            (LogicType::Bool, Binder(LogicBinder::Parameter(1))),
            (LogicType::Bool, op),
        ])
    };
    for (a, b, expected) in [
        (atom(1, false), atom(1, false), Some(true)),
        (atom(1, false), atom(1, true), Some(false)),
        (atom(1, false), atom(2, false), None),
        (unknown.clone(), unknown.clone(), None),
        (atom(1, false), unknown.clone(), None),
    ] {
        let named = matches!(
            (&a.value, &b.value),
            (LogicValue::BoolAtom { .. }, LogicValue::BoolAtom { .. })
        );
        let result = evaluate(&binary(Equal(0, 1)), &[a, b]).unwrap().value;
        assert_eq!(result.known_boolean(), expected);
        if named && expected.is_none() {
            assert!(matches!(result, LogicValue::BoolBinary { .. }));
        } else {
            assert_eq!(result, LogicValue::Bool(expected));
        }
    }
    let negation = expression(vec![
        (LogicType::Bool, Binder(LogicBinder::Parameter(0))),
        (LogicType::Bool, Not(0)),
        (LogicType::Bool, Not(1)),
    ]);
    assert_eq!(
        evaluate(&negation, &[atom(1, false)]).unwrap(),
        atom(1, false)
    );
    for (op, annihilator) in [(And(0, 1), false), (Or(0, 1), true)] {
        let expr = binary(op);
        let constant = |v| Value {
            ty: LogicType::Bool,
            value: LogicValue::Bool(Some(v)),
        };
        assert_eq!(
            evaluate(&expr, &[atom(1, false), atom(1, true)]).unwrap(),
            constant(annihilator)
        );
        assert_eq!(
            evaluate(&expr, &[atom(1, false), atom(1, false)]).unwrap(),
            atom(1, false)
        );
        assert_eq!(
            evaluate(&expr, &[constant(!annihilator), atom(1, false)]).unwrap(),
            atom(1, false)
        );
        assert_eq!(
            evaluate(&expr, &[unknown.clone(), constant(annihilator)]).unwrap(),
            constant(annihilator)
        );
        let combined = evaluate(&expr, &[atom(1, false), atom(2, false)]).unwrap();
        assert_eq!(combined.value.known_boolean(), None);
        assert!(matches!(combined.value, LogicValue::BoolBinary { .. }));
    }
    let wrong = Value {
        ty: LogicType::Usize,
        value: atom(1, false).value,
    };
    assert_eq!(
        evaluate(
            &expression(vec![(LogicType::Usize, Binder(LogicBinder::Parameter(0)))]),
            &[wrong]
        ),
        Err(LogicError::TypeMismatch)
    );
}

#[test]
fn unknown_word_comparisons_have_bounded_identity_but_are_not_proofs() {
    use LogicNodeKind::*;
    let word = |id| Value {
        ty: LogicType::Usize,
        value: LogicValue::Word(AffineValue::variable(id, 0, 8).unwrap()),
    };
    let expr = |op| {
        expression(vec![
            (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
            (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
            (LogicType::Bool, op),
        ])
    };
    for operator in [Equal(0, 1), Less(0, 1), LessEqual(0, 1)] {
        let comparison = evaluate(&expr(operator.clone()), &[word(1), word(2)]).unwrap();
        assert!(matches!(
            comparison.value,
            LogicValue::BoolComparison { .. }
        ));
        assert_eq!(comparison.value.bool_equal(&comparison.value), Some(true));
        assert_eq!(
            comparison.value.bool_equal(&comparison.value.bool_not()),
            Some(false)
        );
        assert_eq!(
            comparison.value.bool_equal(&LogicValue::Bool(Some(true))),
            None
        );
        let foreign = evaluate(&expr(operator), &[word(3), word(2)]).unwrap();
        assert_eq!(comparison.value.bool_equal(&foreign.value), None);
        assert_eq!(
            comparison
                .value
                .bool_combine(&comparison.value.bool_not(), false),
            LogicValue::Bool(Some(false))
        );
        assert_eq!(
            comparison
                .value
                .bool_combine(&comparison.value.bool_not(), true),
            LogicValue::Bool(Some(true))
        );
        assert_eq!(
            comparison.value.bool_combine(&foreign.value, true),
            LogicValue::Bool(None)
        );
        let logic = PredicateLogic {
            parameters: vec![LogicParameter {
                name: "flag".into(),
                position: 0,
                ty: LogicType::Bool,
            }],
            existentials: vec![],
            constraints: vec![expression(vec![(
                LogicType::Bool,
                Binder(LogicBinder::Parameter(0)),
            )])],
        };
        assert!(
            logic
                .instantiate(
                    &[comparison],
                    &[],
                    &[],
                    &mut |_, _, _, _| Err(LogicError::Unbound),
                    &mut |_, _| Err(LogicError::Unbound),
                    &mut LogicBudget::default()
                )
                .is_err()
        );
    }
    let forward = evaluate(&expr(Equal(0, 1)), &[word(1), word(2)]).unwrap();
    let reversed = evaluate(&expr(Equal(0, 1)), &[word(2), word(1)]).unwrap();
    assert_eq!(forward.value.bool_equal(&reversed.value), Some(true));
    let less = evaluate(&expr(Less(0, 1)), &[word(1), word(2)]).unwrap();
    let complement = evaluate(&expr(LessEqual(0, 1)), &[word(2), word(1)]).unwrap();
    assert_eq!(less.value.bool_equal(&complement.value), Some(false));
}

#[test]
fn hidden_resource_symbols_are_not_concrete_permissions_or_distinct_addresses() {
    let evaluate = |a, b| {
        LogicExpression {
            nodes: vec![
                LogicNode {
                    ty: LogicType::Resource(1u32),
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                },
                LogicNode {
                    ty: LogicType::Resource(1u32),
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(1)),
                },
                LogicNode {
                    ty: LogicType::Bool,
                    kind: LogicNodeKind::Equal(0, 1),
                },
            ],
            root: 2,
        }
        .evaluate(
            &[
                TypedLogicValue {
                    ty: LogicType::Resource(1u32),
                    value: a,
                },
                TypedLogicValue {
                    ty: LogicType::Resource(1u32),
                    value: b,
                },
            ],
            &[],
            &mut |_, _, _, _| Err(LogicError::Unbound),
            &mut |_, _| Err(LogicError::Unbound),
            &mut LogicBudget::default(),
        )
        .unwrap()
        .value
    };
    let hidden: LogicValue<u32, u32> = LogicValue::ResourceAtom { atom: 1 };
    assert_eq!(
        evaluate(hidden.clone(), hidden.clone()),
        LogicValue::Bool(Some(true))
    );
    assert_eq!(
        evaluate(hidden.clone(), LogicValue::ResourceAtom { atom: 2 }),
        LogicValue::Bool(None)
    );
    assert_eq!(
        evaluate(hidden, LogicValue::Resource(1)),
        LogicValue::Bool(None)
    );
}

mod capture;

#[test]
fn witness_selection_keeps_defaults_and_overrides_in_separate_environments() {
    let parameter = expression(vec![(
        LogicType::Usize,
        LogicNodeKind::Binder(LogicBinder::Parameter(0)),
    )]);
    let previous = expression(vec![(
        LogicType::Usize,
        LogicNodeKind::Binder(LogicBinder::Existential(0)),
    )]);
    let logic = PredicateLogic {
        parameters: vec![LogicParameter {
            name: "n".into(),
            position: 0,
            ty: LogicType::Usize,
        }],
        existentials: vec![
            Existential {
                name: "first".into(),
                ty: LogicType::Usize,
                default: Some(parameter.clone()),
            },
            Existential {
                name: "second".into(),
                ty: LogicType::Usize,
                default: Some(previous.clone()),
            },
        ],
        constraints: vec![],
    };
    let word = |n| Value {
        ty: LogicType::Usize,
        value: LogicValue::Word(AffineValue::exact(n)),
    };
    let mut observed = Vec::new();
    let values = logic
        .instantiate_witnesses_using(
            &[word(2)],
            &[word(7)],
            &[(0, parameter)],
            &mut |expr, parameters, witnesses, budget| {
                observed.push((parameters.to_vec(), witnesses.to_vec()));
                expr.evaluate(
                    parameters,
                    witnesses,
                    &mut |_, _, _, _| Err(LogicError::Unbound),
                    &mut |_, _| Err(LogicError::Unbound),
                    budget,
                )
            },
            &mut LogicBudget::default(),
        )
        .unwrap();
    assert_eq!(values, [word(7), word(7)]);
    assert_eq!(
        observed,
        [(vec![word(7)], vec![]), (vec![word(2)], vec![word(7)])]
    );
    // An override cannot read a declaration's earlier existential.
    assert_eq!(
        logic.instantiate_witnesses(
            &[word(2)],
            &[word(7)],
            &[(1, previous)],
            &mut |_, _, _, _| Err(LogicError::Unbound),
            &mut |_, _| Err(LogicError::Unbound),
            &mut LogicBudget::default(),
        ),
        Err(LogicError::Unbound)
    );
}
