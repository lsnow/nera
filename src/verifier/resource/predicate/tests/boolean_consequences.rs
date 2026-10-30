use super::*;
use crate::predicate_logic::*;

fn boolean_definition() -> PredicateDefinition {
    let mut def = definition();
    for name in ["a", "b", "c"] {
        def.logic.existentials.push(Existential {
            name: name.into(),
            ty: LogicType::Bool,
            default: None,
        });
    }
    let expression = |kinds: Vec<LogicNodeKind<VirMemoryAccess>>| LogicExpression {
        root: kinds.len() as u32 - 1,
        nodes: kinds
            .into_iter()
            .map(|kind| LogicNode {
                ty: LogicType::Bool,
                kind,
            })
            .collect(),
    };
    use LogicNodeKind::*;
    def.logic.constraints = vec![
        expression(vec![
            Binder(LogicBinder::Existential(0)),
            Binder(LogicBinder::Existential(1)),
            Binder(LogicBinder::Existential(2)),
            Or(0, 1),
            Equal(1, 2),
            And(3, 4),
        ]),
        expression(vec![Binder(LogicBinder::Existential(0)), Not(0)]),
    ];
    def
}

#[test]
fn boolean_consequences_remain_scoped_to_the_actual_package_across_calls_and_refold() {
    let def = boolean_definition();
    let mut sealed = state();
    sealed
        .import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            false,
        )
        .unwrap();
    let mapping = [PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(8),
    }];
    let (frame, callee) = enter_predicate_call(&sealed, &mapping).unwrap();
    let returned = frame.resume(&callee, &mapping).unwrap();
    assert_eq!(
        returned.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let mut foreign = returned.clone();
    foreign
        .predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .logical_witnesses = sealed.predicates[&PredicateHolder(0)]
        .logical_witnesses
        .clone();
    assert_eq!(
        foreign.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    let opened = open_internal_named(&returned, &def, PredicateHolder(0), binding(10), 42);
    for (binder, truth) in [(0, false), (1, true), (2, true)] {
        let operand = OpenedSpecOperand::Opened {
            action: 42,
            holder: 0,
            binder,
        };
        assert_eq!(
            opened.prove_opened_spec_comparison(
                OpenedSpecComparison::Equal,
                operand,
                OpenedSpecOperand::Bool(truth)
            ),
            Ok(true)
        );
        assert_eq!(
            opened.prove_opened_spec_comparison(
                OpenedSpecComparison::Equal,
                operand,
                OpenedSpecOperand::Bool(!truth)
            ),
            Ok(false)
        );
    }
    let witnesses = WitnessArguments {
        arguments: vec![],
        inputs: (0..3)
            .map(|binder| {
                (
                    LogicType::Bool,
                    WitnessInput::Opened {
                        action: 42,
                        holder: 0,
                        binder,
                    },
                )
            })
            .collect(),
        values: (0..3)
            .map(|binder| {
                (
                    binder,
                    LogicExpression {
                        root: 0,
                        nodes: vec![LogicNode {
                            ty: LogicType::Bool,
                            kind: LogicNodeKind::Binder(LogicBinder::Parameter(binder)),
                        }],
                    },
                )
            })
            .collect(),
    };
    let effect = PredicateEffect::FoldWithWitnesses {
        holder: PredicateHolder(0),
        bindings: vec![binding(10)],
        witnesses: witnesses.clone(),
    };
    let refolded = transfer_predicate(&opened, &def, 7, &effect).unwrap();
    check_predicate_evidence(&opened, &refolded).unwrap();
    assert_eq!(
        refolded.output.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert!(
        refolded
            .output
            .prove_opened_spec_comparison(
                OpenedSpecComparison::Equal,
                OpenedSpecOperand::Opened {
                    action: 42,
                    holder: 0,
                    binder: 1
                },
                OpenedSpecOperand::Bool(true)
            )
            .is_err()
    );
    let mut wrong_action = witnesses;
    for (_, input) in &mut wrong_action.inputs {
        if let WitnessInput::Opened { action, .. } = input {
            *action = 43;
        }
    }
    assert!(
        transfer_predicate(
            &opened,
            &def,
            7,
            &PredicateEffect::FoldWithWitnesses {
                holder: PredicateHolder(0),
                bindings: vec![binding(10)],
                witnesses: wrong_action
            }
        )
        .is_err()
    );
    // Declarations alone do not supply concrete existential values for a local fold.
    assert!(
        transfer_predicate(
            &state(),
            &def,
            7,
            &PredicateEffect::Fold {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)]
            }
        )
        .is_err()
    );
}

#[test]
fn mixed_guarantees_keep_numeric_types_and_opening_scope_through_call_transport() {
    let mut def = definition();
    def.logic.existentials = vec![
        Existential {
            name: "used".into(),
            ty: LogicType::Usize,
            default: None,
        },
        Existential {
            name: "enabled".into(),
            ty: LogicType::Bool,
            default: None,
        },
    ];
    let node = |ty, kind| LogicNode { ty, kind };
    use LogicNodeKind::*;
    def.logic.constraints = vec![
        LogicExpression {
            root: 4,
            nodes: vec![
                node(LogicType::Bool, Binder(LogicBinder::Existential(1))),
                node(LogicType::Usize, Binder(LogicBinder::Existential(0))),
                node(LogicType::Usize, Word(7)),
                node(LogicType::Bool, Less(1, 2)),
                node(LogicType::Bool, Or(0, 3)),
            ],
        },
        LogicExpression {
            root: 1,
            nodes: vec![
                node(LogicType::Bool, Binder(LogicBinder::Existential(1))),
                node(LogicType::Bool, Not(0)),
            ],
        },
    ];
    let mut sealed = state();
    sealed
        .import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            false,
        )
        .unwrap();
    let mapping = [PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(8),
    }];
    let (frame, callee) = enter_predicate_call(&sealed, &mapping).unwrap();
    let returned = frame.resume(&callee, &mapping).unwrap();
    let mut foreign = returned.clone();
    foreign
        .predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .logical_witnesses = sealed.predicates[&PredicateHolder(0)]
        .logical_witnesses
        .clone();
    assert_eq!(
        foreign.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    let opened = open_internal_named(&returned, &def, PredicateHolder(0), binding(10), 52);
    let used = OpenedSpecOperand::Opened {
        action: 52,
        holder: 0,
        binder: 0,
    };
    assert_eq!(
        opened.prove_opened_spec_comparison(
            OpenedSpecComparison::Less,
            used,
            OpenedSpecOperand::Word(7)
        ),
        Ok(true)
    );
    assert_eq!(
        opened.prove_opened_spec_comparison(
            OpenedSpecComparison::Equal,
            used,
            OpenedSpecOperand::Word(7)
        ),
        Ok(false)
    );
    assert!(
        opened
            .prove_opened_spec_comparison(
                OpenedSpecComparison::Less,
                OpenedSpecOperand::Opened {
                    action: 51,
                    holder: 0,
                    binder: 0
                },
                OpenedSpecOperand::Word(7)
            )
            .is_err()
    );
    let witnesses = WitnessArguments {
        arguments: vec![],
        inputs: vec![
            (
                LogicType::Usize,
                WitnessInput::Opened {
                    action: 52,
                    holder: 0,
                    binder: 0,
                },
            ),
            (
                LogicType::Bool,
                WitnessInput::Opened {
                    action: 52,
                    holder: 0,
                    binder: 1,
                },
            ),
        ],
        values: vec![
            (
                0,
                LogicExpression {
                    root: 0,
                    nodes: vec![node(LogicType::Usize, Binder(LogicBinder::Parameter(0)))],
                },
            ),
            (
                1,
                LogicExpression {
                    root: 0,
                    nodes: vec![node(LogicType::Bool, Binder(LogicBinder::Parameter(1)))],
                },
            ),
        ],
    };
    let evidence = transfer_predicate(
        &opened,
        &def,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(10)],
            witnesses,
        },
    )
    .unwrap();
    check_predicate_evidence(&opened, &evidence).unwrap();
    assert_eq!(
        evidence.output.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
}
