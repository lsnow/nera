use super::*;
use crate::predicate_logic::*;

fn arguments(a: u32, b: u32) -> WitnessArguments<VirMemoryAccess, VirValueId> {
    let leaf = |id| LogicNode {
        ty: LogicType::Usize,
        kind: LogicNodeKind::Binder(LogicBinder::Parameter(id)),
    };
    WitnessArguments {
        inputs: vec![
            (LogicType::Usize, WitnessInput::Scalar(VirValueId::new(a))),
            (LogicType::Usize, WitnessInput::Scalar(VirValueId::new(b))),
        ],
        arguments: vec![
            LogicExpression {
                nodes: vec![leaf(0)],
                root: 0,
            },
            LogicExpression {
                nodes: vec![leaf(1)],
                root: 0,
            },
            LogicExpression {
                nodes: vec![
                    leaf(0),
                    leaf(1),
                    LogicNode {
                        ty: LogicType::Bool,
                        kind: LogicNodeKind::LessEqual(0, 1),
                    },
                ],
                root: 2,
            },
        ],
        values: vec![],
    }
}

fn projected(source: u32, factor: u64) -> (ResourceState, PredicateDefinition) {
    let mut def = logical_definition();
    for (index, ty) in [LogicType::Usize, LogicType::Usize, LogicType::Bool]
        .into_iter()
        .enumerate()
    {
        def.logic.parameters.push(LogicParameter {
            position: index + 1,
            name: format!("p{index}"),
            ty,
        });
    }
    let cell = |value| crate::verifier::resource::ScalarOriginCell {
        root: crate::verifier::resource::ScalarOriginRoot::Parameter {
            function: crate::VirFunctionId::new(0),
            value: VirValueId::new(value),
        },
        initial_lower: 1,
        initial_upper: 2,
    };
    let origin = ScalarOrigin {
        first: cell(source),
        scale: 1,
        second: Some((cell(source + 1000), 1)),
        addend: 1,
    };
    let mut input = state();
    for (slot, origin) in [
        (source, origin),
        (source + 10, origin.scale(factor).unwrap()),
    ] {
        input
            .define_value(
                VirValueId::new(slot),
                AbstractValue::U64(origin.initial_interval().unwrap()),
            )
            .unwrap();
        input.set_word_origin(VirValueId::new(slot), origin);
    }
    let mut witnesses = arguments(source, source + 10);
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
        (source + 10, 101),
        (source, 102),
    ]
    .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
    let mut result = folded.project_cfg_edge(&edges);
    for (a, b) in edges {
        result.define_value(b, *folded.value(a).unwrap()).unwrap();
    }
    (result, def)
}

#[test]
fn dependent_full_slots_remain_separately_usable_through_join_widen_and_refold() {
    for factor in [2, 3] {
        let (a, def) = projected(90, 2);
        let (b, _) = projected(91, factor);
        let before = (a.clone(), b.clone());
        let joined = a.join(&b).unwrap();
        assert_eq!(joined, b.join(&a).unwrap());
        assert!(joined.covers_cfg_case(&a));
        assert!(joined.covers_cfg_case(&b));
        assert_eq!(joined.join(&a).unwrap(), joined);
        let wide = a.widen(&joined).unwrap();
        assert!(wide.covers_cfg_case(&joined));
        let instance = &joined.predicates[&PredicateHolder(0)];
        assert_ne!(
            instance.logical_local_aliases[&VirValueId::new(100)],
            instance.logical_local_aliases[&VirValueId::new(101)]
        );
        assert_eq!(
            instance.logical_local_aliases[&VirValueId::new(100)],
            instance.logical_local_aliases[&VirValueId::new(102)]
        );
        for state in [&joined, &wide] {
            for first in [100, 102] {
                state
                    .check_predicate_arguments(&def, PredicateHolder(0), &arguments(first, 101))
                    .unwrap();
            }
            assert!(
                state
                    .check_predicate_arguments(&def, PredicateHolder(0), &arguments(101, 100))
                    .is_err()
            );
        }
        let opened = transfer_predicate(
            &joined,
            &def,
            7,
            &PredicateEffect::WithArguments {
                holder: PredicateHolder(0),
                arguments: arguments(100, 101),
                effect: Box::new(PredicateEffect::UnfoldNamed {
                    holder: PredicateHolder(0),
                    bindings: vec![binding(0)],
                    action: 40,
                }),
            },
        )
        .unwrap()
        .output;
        let mut witnesses = arguments(102, 101);
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
        assert_eq!((a, b), before);
    }
}

#[test]
fn complete_matching_does_not_bypass_actual_sources_or_public_scope_checks() {
    let (a, _) = projected(90, 2);
    let (b, _) = projected(91, 2);
    for failure in 0..5 {
        let mut bad = b.clone();
        match failure {
            0 => {
                // Equal-value writes cannot supply any old capture identity.
                for id in [100, 101, 102] {
                    let id = VirValueId::new(id);
                    let value = *bad.value(id).unwrap();
                    *bad.value_mut(id).unwrap() = value;
                }
            }
            1 => {
                // The duplicate of the first coordinate must agree.
                bad.values.insert(
                    VirValueId::new(102),
                    AbstractValue::U64(U64Interval::exact(99)),
                );
            }
            2 => {
                bad.values.insert(
                    VirValueId::new(102),
                    AbstractValue::Bool(AbstractBool::Unknown),
                );
            }
            3 => {
                // One predecessor's duplicate cannot identify a distinct source.
                let origin = bad.word_origin(VirValueId::new(101)).unwrap();
                bad.set_word_origin(VirValueId::new(102), origin);
            }
            _ => {
                let instance = bad.predicates.get_mut(&PredicateHolder(0)).unwrap();
                let LogicValue::Word(word) = &mut instance.logical_parameters[1].value else {
                    panic!()
                };
                word.terms = std::mem::take(&mut word.terms)
                    .into_iter()
                    .map(|(mut atom, n)| {
                        if let logic::ObservationAtom::Historical { scope, .. } = &mut atom {
                            scope.instance += 1;
                        }
                        (atom, n)
                    })
                    .collect();
            }
        }
        let before = (a.clone(), bad.clone());
        assert_eq!(a.join(&bad), Err(ResourceJoinError::PredicateStateMismatch));
        assert_eq!(bad.join(&a), Err(ResourceJoinError::PredicateStateMismatch));
        assert_eq!((a.clone(), bad), before);
    }
}
