use super::*;
use crate::predicate_logic::*;

fn arguments(a: u32, b: u32) -> WitnessArguments<VirMemoryAccess, VirValueId> {
    WitnessArguments {
        inputs: vec![
            (LogicType::Bool, WitnessInput::Scalar(VirValueId::new(a))),
            (LogicType::Bool, WitnessInput::Scalar(VirValueId::new(b))),
        ],
        arguments: vec![LogicExpression {
            nodes: vec![
                LogicNode {
                    ty: LogicType::Bool,
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                },
                LogicNode {
                    ty: LogicType::Bool,
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(1)),
                },
                LogicNode {
                    ty: LogicType::Bool,
                    kind: LogicNodeKind::Or(0, 1),
                },
            ],
            root: 2,
        }],
        values: vec![],
    }
}
fn projected(
    source: u32,
    known: Option<bool>,
    history: bool,
) -> (ResourceState, PredicateDefinition) {
    projected_form(source, known, history, 0)
}
fn projected_form(
    source: u32,
    known: Option<bool>,
    history: bool,
    form: usize,
) -> (ResourceState, PredicateDefinition) {
    let mut def = logical_definition();
    def.logic.parameters.push(LogicParameter {
        position: 1,
        name: "choice".into(),
        ty: LogicType::Bool,
    });
    let mut input = state();
    for slot in [source, source + 2] {
        let id = VirValueId::new(slot);
        input
            .define_value(
                id,
                AbstractValue::Bool(match known {
                    Some(true) => AbstractBool::True,
                    Some(false) => AbstractBool::False,
                    None => AbstractBool::Unknown,
                }),
            )
            .unwrap();
        if history {
            input.set_bool_origin(
                id,
                BoolOrigin::Parameter {
                    function: crate::VirFunctionId::new(0),
                    value: id,
                },
            );
        }
    }
    let mut witnesses = arguments(source, source + 2);
    match form {
        0 => {}
        1 => witnesses.arguments[0].nodes[2].kind = LogicNodeKind::Or(1, 0),
        2 => {
            let expression = &mut witnesses.arguments[0];
            expression.nodes.truncate(2);
            for kind in [
                LogicNodeKind::Not(0),
                LogicNodeKind::Not(1),
                LogicNodeKind::And(3, 2),
                LogicNodeKind::Not(4),
            ] {
                expression.nodes.push(LogicNode {
                    ty: LogicType::Bool,
                    kind,
                });
            }
            expression.root = 5;
        }
        3 | 4 => {
            let expression = &mut witnesses.arguments[0];
            expression.nodes.truncate(2);
            let kinds = if form == 3 {
                // (a || b) && (a || !a)
                vec![
                    LogicNodeKind::Not(0),
                    LogicNodeKind::Or(0, 2),
                    LogicNodeKind::Or(0, 1),
                    LogicNodeKind::And(4, 3),
                ]
            } else {
                // a || (b && !a)
                vec![
                    LogicNodeKind::Not(0),
                    LogicNodeKind::And(1, 2),
                    LogicNodeKind::Or(0, 3),
                ]
            };
            for kind in kinds {
                expression.nodes.push(LogicNode {
                    ty: LogicType::Bool,
                    kind,
                });
            }
            expression.root = expression.nodes.len() as u32 - 1;
        }
        _ => unreachable!(),
    }

    witnesses.values.push((
        0,
        LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Word(0),
            }],
            root: 0,
        },
    ));
    let folded = transfer_predicate(
        &input,
        &def,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses,
        },
    )
    .unwrap()
    .output;
    let edges = [
        (0, 0),
        (1, 1),
        (source, 100),
        (source + 2, 101),
        (source + 2, 102),
    ]
    .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
    let mut result = folded.project_cfg_edge(&edges);
    for (a, b) in edges {
        result.define_value(b, *folded.value(a).unwrap()).unwrap();
    }
    (result, def)
}
#[test]
fn compound_boolean_captures_keep_all_cfg_sources_and_survive_call_transport() {
    for (history, form) in [false, true]
        .into_iter()
        .flat_map(|history| (0..5).map(move |form| (history, form)))
    {
        let (a, def) = projected(90, Some(true), history);
        let (b, _) = projected_form(91, Some(false), history, form);
        let joined = a.join(&b).unwrap();
        assert_eq!(joined, b.join(&a).unwrap());
        assert!(joined.covers_cfg_case(&a));
        assert!(joined.covers_cfg_case(&b));
        assert_eq!(joined.join(&a).unwrap(), joined);
        assert_eq!(joined.widen(&a).unwrap(), joined);
        assert!(matches!(
            joined.predicates[&PredicateHolder(0)].logical_parameters[0].value,
            LogicValue::BoolBinary { .. }
        ));
        for id in [101, 102] {
            joined
                .check_predicate_arguments(&def, PredicateHolder(0), &arguments(100, id))
                .unwrap();
        }
        let mapping = [PredicateCallBinding {
            caller: PredicateHolder(0),
            callee: PredicateHolder(7),
        }];
        let (frame, callee) = enter_predicate_call(&joined, &mapping).unwrap();
        let resumed = frame.resume(&callee, &mapping).unwrap();
        // Transport must visit every nested atom, including duplicated sources.
        assert!(resumed.predicate_representation_valid(&resumed.predicates[&PredicateHolder(0)]));
        let opened = transfer_predicate(
            &joined,
            &def,
            7,
            &PredicateEffect::WithArguments {
                holder: PredicateHolder(0),
                arguments: arguments(100, 102),
                effect: Box::new(PredicateEffect::UnfoldNamed {
                    holder: PredicateHolder(0),
                    bindings: vec![binding(0)],
                    action: 40,
                }),
            },
        )
        .unwrap()
        .output;
        let mut witnesses = arguments(100, 101);
        witnesses.values.push((
            0,
            LogicExpression {
                nodes: vec![LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Word(0),
                }],
                root: 0,
            },
        ));
        let evidence = transfer_predicate(
            &opened,
            &def,
            7,
            &PredicateEffect::FoldWithWitnesses {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
                witnesses,
            },
        )
        .unwrap();
        check_predicate_evidence(&opened, &evidence).unwrap();
    }
}
#[test]
fn known_result_cannot_mask_conflicting_nested_captures() {
    for (history, form) in [false, true]
        .into_iter()
        .flat_map(|history| [2, 4].map(|form| (history, form)))
    {
        let (a, _) = projected(90, Some(true), history);
        let (b, _) = projected_form(91, Some(true), history, form);
        for failure in 0..3 {
            let mut bad = b.clone();
            match failure {
                0 => {
                    for id in [101, 102] {
                        bad.values.insert(
                            VirValueId::new(id),
                            AbstractValue::Bool(AbstractBool::False),
                        );
                    }
                }
                1 => {
                    bad.values.insert(
                        VirValueId::new(102),
                        AbstractValue::Bool(AbstractBool::False),
                    );
                }
                _ => {
                    bad.values.insert(
                        VirValueId::new(102),
                        AbstractValue::U64(U64Interval::exact(1)),
                    );
                }
            }
            let before = (a.clone(), bad.clone());
            assert_eq!(a.join(&bad), Err(ResourceJoinError::PredicateStateMismatch));
            assert_eq!(bad.join(&a), Err(ResourceJoinError::PredicateStateMismatch));
            assert_eq!((a.clone(), bad), before);
        }
    }
}
