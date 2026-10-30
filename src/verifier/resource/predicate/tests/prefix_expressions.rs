use super::*;
use crate::predicate_logic::*;

fn definition_for_difference(bound: u64) -> PredicateDefinition {
    let mut def = logical_definition();
    def.logic.existentials[0].name = "low".into();
    def.logic.existentials.push(Existential {
        name: "high".into(),
        ty: LogicType::Usize,
        default: None,
    });
    def.logic.constraints = vec![
        LogicExpression {
            nodes: vec![
                LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
                },
                LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Binder(LogicBinder::Existential(1)),
                },
                LogicNode {
                    ty: LogicType::Bool,
                    kind: LogicNodeKind::LessEqual(0, 1),
                },
            ],
            root: 2,
        },
        LogicExpression {
            nodes: vec![
                LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
                },
                LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Word(bound),
                },
                LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Add(0, 1),
                },
                LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Binder(LogicBinder::Existential(1)),
                },
                LogicNode {
                    ty: LogicType::Bool,
                    kind: LogicNodeKind::LessEqual(3, 2),
                },
            ],
            root: 4,
        },
    ];
    def.logical_prefixes
        .push(crate::PredicateInitializedPrefix {
            resource: 0,
            array_offset: 0,
            element: VirMemoryAccess::core_u64(),
            length: 2,
            stride: 8,
            count: crate::PredicatePrefixCount::Logical(LogicExpression {
                nodes: vec![
                    LogicNode {
                        ty: LogicType::Usize,
                        kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
                    },
                    LogicNode {
                        ty: LogicType::Usize,
                        kind: LogicNodeKind::Binder(LogicBinder::Existential(1)),
                    },
                    LogicNode {
                        ty: LogicType::Usize,
                        kind: LogicNodeKind::Sub(1, 0),
                    },
                ],
                root: 2,
            }),
        });
    def
}

#[test]
fn correlated_hidden_prefixes_reuse_bytes_and_survive_loop_abstraction() {
    let def = definition_for_difference(1);
    let mut input = state();
    let before = input.clone();
    input
        .import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            true,
        )
        .unwrap();
    assert_eq!(
        input.values.keys().collect::<Vec<_>>(),
        before.values.keys().collect::<Vec<_>>()
    );
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let allocation = AbstractAllocationId::new(0);
    assert_eq!(
        input.allocation(allocation).unwrap().initialization(),
        before.allocation(allocation).unwrap().initialization()
    );
    assert_ne!(
        input
            .allocation(allocation)
            .unwrap()
            .initialization()
            .classify(ByteRange::new(0, 16).unwrap()),
        InitializationClass::Initialized
    );
    let mut head = input.clone();
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    head.abstract_loop_predicates(&repacked).unwrap();
    assert!(head.loop_resources_match_with_predicates(&input, &[], &repacked));
    assert_eq!(head.values, input.values);
    assert_eq!(head.allocations, input.allocations);
}

#[test]
fn correlated_counts_cannot_replace_definedness_initialization_or_authority() {
    for mutation in 0..5 {
        let mut def = definition_for_difference(if mutation == 0 { 2 } else { 1 });
        let mut input = state();
        match mutation {
            1 => {
                def.logic.constraints.remove(0);
            }
            2 => {
                let crate::PredicatePrefixCount::Logical(expression) =
                    &mut def.logical_prefixes[0].count
                else {
                    unreachable!()
                };
                expression.nodes[2].kind = LogicNodeKind::Sub(0, 1);
            }
            3 => {
                input
                    .allocation_mut(AbstractAllocationId::new(0))
                    .unwrap()
                    .mark_uninitialized(ByteRange::new(0, 8).unwrap())
                    .unwrap();
            }
            4 => {
                input.values.remove(&binding(0).permission);
            }
            _ => {}
        }
        let before = input.clone();
        let result = input.import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            true,
        );
        if mutation == 0 || mutation == 3 {
            result.unwrap();
            assert_eq!(
                input.closed_predicate_checks(),
                vec![(PredicateHolder(0), true)]
            );
            assert_ne!(
                input
                    .allocation(AbstractAllocationId::new(0))
                    .unwrap()
                    .initialization()
                    .classify(ByteRange::new(0, 16).unwrap()),
                InitializationClass::Initialized
            );
        } else {
            assert!(result.is_err(), "mutation {mutation}");
            assert_eq!(input, before);
        }
    }
}

#[test]
fn separate_current_inputs_bound_a_prefix_without_creating_initialized_bytes() {
    use crate::verifier::relation::difference::word;

    for saved_constraints in [false, true] {
        let mut def = definition_for_difference(1);
        def.logic.existentials.clear();
        def.logic.parameters = ["low", "high"]
            .into_iter()
            .enumerate()
            .map(|(i, name)| LogicParameter {
                name: name.into(),
                position: i + 1,
                ty: LogicType::Usize,
            })
            .collect();
        for expression in &mut def.logic.constraints {
            for node in &mut expression.nodes {
                if let LogicNodeKind::Binder(LogicBinder::Existential(i)) = node.kind {
                    node.kind = LogicNodeKind::Binder(LogicBinder::Parameter(i));
                }
            }
        }
        if !saved_constraints {
            def.logic.constraints.clear();
        }
        let crate::PredicatePrefixCount::Logical(expression) = &mut def.logical_prefixes[0].count
        else {
            unreachable!()
        };
        for node in &mut expression.nodes {
            if let LogicNodeKind::Binder(LogicBinder::Existential(i)) = node.kind {
                node.kind = LogicNodeKind::Binder(LogicBinder::Parameter(i));
            }
        }
        let ids = [VirValueId::new(90), VirValueId::new(91)];
        let effect = PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses: WitnessArguments {
                inputs: ids
                    .iter()
                    .map(|id| (LogicType::Usize, WitnessInput::Scalar(*id)))
                    .collect(),
                arguments: (0..2)
                    .map(|i| LogicExpression {
                        nodes: vec![LogicNode {
                            ty: LogicType::Usize,
                            kind: LogicNodeKind::Binder(LogicBinder::Parameter(i)),
                        }],
                        root: 0,
                    })
                    .collect(),
                values: vec![],
            },
        };
        for mutation in 0..5 {
            let mut input = state();
            for id in ids {
                input
                    .define_value(id, AbstractValue::U64(U64Interval::new(2, 20).unwrap()))
                    .unwrap();
            }
            input.seed_parameter_origins(crate::VirFunctionId::new(0), &ids);
            let mut premises = vec![DifferencePremise::Bound {
                left: word(ids[1]),
                right: word(ids[0]),
                bound: if mutation == 1 { 2 } else { 1 },
            }];
            if mutation != 2 {
                premises.push(DifferencePremise::Bound {
                    left: word(ids[0]),
                    right: word(ids[1]),
                    bound: 0,
                });
            }
            input.learn_relations(&premises, DifferenceLimits::default());
            if mutation == 3 {
                input
                    .allocation_mut(AbstractAllocationId::new(0))
                    .unwrap()
                    .mark_uninitialized(ByteRange::new(0, 8).unwrap())
                    .unwrap();
            }
            if mutation == 4 {
                input.values.remove(&binding(0).permission);
            }
            let before = input.clone();
            let result = transfer_predicate(&input, &def, 7, &effect);
            if mutation == 0 {
                let evidence = result.unwrap();
                check_predicate_evidence(&input, &evidence).unwrap();
                let allocation = AbstractAllocationId::new(0);
                assert_eq!(
                    evidence
                        .output
                        .allocation(allocation)
                        .unwrap()
                        .initialization(),
                    input.allocation(allocation).unwrap().initialization()
                );
                assert_ne!(
                    evidence
                        .output
                        .allocation(allocation)
                        .unwrap()
                        .initialization()
                        .classify(ByteRange::new(0, 16).unwrap()),
                    InitializationClass::Initialized
                );
            } else {
                assert!(
                    result.is_err(),
                    "saved={saved_constraints}, mutation={mutation}"
                );
            }
            assert_eq!(input, before);
        }
    }
}
