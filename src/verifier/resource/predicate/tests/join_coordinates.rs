use super::*;
use crate::predicate_logic::*;

fn arguments(slot: u32, form: u8) -> WitnessArguments<VirMemoryAccess, VirValueId> {
    let ty = LogicType::Usize;
    let mut nodes = vec![LogicNode {
        ty,
        kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
    }];
    match form {
        1 => {
            nodes.push(LogicNode {
                ty,
                kind: LogicNodeKind::Word(1),
            });
            nodes.push(LogicNode {
                ty,
                kind: LogicNodeKind::Add(0, 1),
            });
        }
        2 => {
            nodes.push(LogicNode {
                ty,
                kind: LogicNodeKind::Word(4),
            });
            nodes.push(LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::LessEqual(0, 1),
            });
        }
        _ => {}
    }
    WitnessArguments {
        inputs: vec![(ty, WitnessInput::Scalar(VirValueId::new(slot)))],
        arguments: vec![LogicExpression {
            root: nodes.len() as u32 - 1,
            nodes,
        }],
        values: vec![],
    }
}

// Actual full origins are established before capture. Historical root names
// deliberately have no live SSA slots after projection.
fn projected(
    source: u32,
    origin_kind: u8,
    form: u8,
    exact: u64,
) -> (ResourceState, PredicateDefinition) {
    let (_, mut def) = super::join_captures::captured(false, source, true);
    if form == 2 {
        def.logic.parameters[0].ty = LogicType::Bool;
    }
    let mut input = state();
    let slot = VirValueId::new(source);
    input
        .define_value(slot, AbstractValue::U64(U64Interval::exact(exact)))
        .unwrap();
    if origin_kind != 0 {
        let cell = |id| crate::verifier::resource::ScalarOriginCell {
            root: crate::verifier::resource::ScalarOriginRoot::Parameter {
                function: crate::VirFunctionId::new(0),
                value: VirValueId::new(id),
            },
            initial_lower: 0,
            initial_upper: 7,
        };
        input.set_word_origin(
            slot,
            ScalarOrigin {
                first: cell(source),
                scale: if origin_kind == 2 { 2 } else { 1 },
                second: if origin_kind == 3 {
                    Some((cell(source + 1000), 1))
                } else {
                    None
                },
                addend: 1,
            },
        );
    }
    let mut witnesses = arguments(source, form);
    witnesses
        .values
        .push((0, arguments(source, 0).arguments.remove(0)));
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
    let edges = [(0, 0), (1, 1), (source, 100), (source, 101)]
        .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
    let mut projected = folded.project_cfg_edge(&edges);
    for (a, b) in edges {
        projected
            .define_value(b, *folded.value(a).unwrap())
            .unwrap();
    }
    (projected, def)
}

#[test]
fn full_coordinates_align_offsets_scales_sums_and_known_comparisons() {
    for origin in 1..=3 {
        for other_origin in [0, origin] {
            for form in 0..=2 {
                let (a, def) = projected(90, origin, form, 3);
                let (b, _) = projected(91, other_origin, form, 5);
                let before = (a.clone(), b.clone());
                let joined = a.join(&b).unwrap();
                assert_eq!(joined, b.join(&a).unwrap());
                assert!(joined.covers_cfg_case(&a));
                assert!(joined.covers_cfg_case(&b));
                assert_eq!(joined.join(&a).unwrap(), joined);
                let wide = a.widen(&joined).unwrap();
                assert!(wide.covers_cfg_case(&joined));
                assert!(joined.word_origin(VirValueId::new(100)).is_none());
                for id in [100, 101] {
                    joined
                        .check_predicate_arguments(&def, PredicateHolder(0), &arguments(id, form))
                        .unwrap();
                    let widened_argument = wide.check_predicate_arguments(
                        &def,
                        PredicateHolder(0),
                        &arguments(id, form),
                    );
                    if form == 1 {
                        // Widening loses the upper bound needed for a new
                        // `slot + 1`; the saved capture grants no overflow waiver.
                        assert!(widened_argument.is_err());
                    } else {
                        widened_argument.unwrap();
                    }
                }
                if form == 2 {
                    assert!(matches!(
                        joined.predicates[&PredicateHolder(0)].logical_parameters[0].value,
                        LogicValue::BoolComparison {
                            word_type: crate::predicate_logic::WordType::Usize,
                            ..
                        }
                    ));
                }
                let opened = transfer_predicate(
                    &joined,
                    &def,
                    7,
                    &PredicateEffect::WithArguments {
                        holder: PredicateHolder(0),
                        arguments: arguments(100, form),
                        effect: Box::new(PredicateEffect::UnfoldNamed {
                            holder: PredicateHolder(0),
                            bindings: vec![binding(0)],
                            action: 40,
                        }),
                    },
                )
                .unwrap()
                .output;
                let mut witnesses = arguments(100, form);
                witnesses
                    .values
                    .push((0, arguments(100, 0).arguments.remove(0)));
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
    }
}

#[test]
fn composite_coordinates_require_complete_unambiguous_consistent_actual_sources() {
    let (a, _) = projected(90, 3, 0, 3);
    let (b, _) = projected(91, 3, 0, 5);
    for failure in 0..6 {
        let mut bad = b.clone();
        match failure {
            0 => {
                for id in [100, 101] {
                    let value = *bad.value(VirValueId::new(id)).unwrap();
                    *bad.value_mut(VirValueId::new(id)).unwrap() = value;
                }
            }
            1 => {
                bad.values.insert(
                    VirValueId::new(101),
                    AbstractValue::U64(U64Interval::exact(6)),
                );
            }
            2 => {
                bad.values.insert(
                    VirValueId::new(101),
                    AbstractValue::Bool(AbstractBool::Unknown),
                );
            }
            3 => {
                let mut origin = bad.word_origin(VirValueId::new(101)).unwrap();
                origin.addend += 1;
                bad.set_word_origin(VirValueId::new(101), origin);
            }
            4 => {
                // A scaled complete value cannot be silently divided into its roots.
                for id in [100, 101] {
                    let origin = bad
                        .word_origin(VirValueId::new(id))
                        .unwrap()
                        .scale(2)
                        .unwrap();
                    bad.set_word_origin(VirValueId::new(id), origin);
                }
            }
            _ => {
                let instance = bad.predicates.get_mut(&PredicateHolder(0)).unwrap();
                let LogicValue::Word(word) = &mut instance.logical_parameters[0].value else {
                    panic!()
                };
                word.terms = std::mem::take(&mut word.terms)
                    .into_iter()
                    .map(|(mut atom, coefficient)| {
                        if let logic::ObservationAtom::Historical { local, .. } = &mut atom {
                            *local = false;
                        }
                        (atom, coefficient)
                    })
                    .collect();
            }
        }
        let before = (a.clone(), bad.clone());
        assert_eq!(a.join(&bad), Err(ResourceJoinError::PredicateStateMismatch));
        assert_eq!(bad.join(&a), Err(ResourceJoinError::PredicateStateMismatch));
        assert_eq!((a.clone(), bad), before);
    }
    let instance = &a.predicates[&PredicateHolder(0)];
    let aligned = a
        .join_predicate_parameters(
            &a,
            instance,
            instance,
            instance.logic_scope.unwrap(),
            &mut LogicBudget::default(),
        )
        .unwrap();
    assert_eq!(aligned.values, instance.logical_parameters);
    assert!(aligned.aliases.is_empty());
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert!(matches!(
        a.join_predicate_parameters(
            &b,
            instance,
            &b.predicates[&PredicateHolder(0)],
            instance.logic_scope.unwrap(),
            &mut budget
        ),
        Err(PredicateError::Budget)
    ));
}

#[test]
fn coordinate_names_cannot_capture_an_existing_public_snapshot() {
    let (mut a, _) = projected(90, 3, 0, 3);
    let (mut b, _) = projected(91, 3, 0, 5);
    let target = a.predicates[&PredicateHolder(0)].logic_scope.unwrap();
    let local = TypedLogicValue {
        ty: LogicType::Usize,
        value: LogicValue::Word(
            AffineValue::identified(
                logic::ObservationAtom::Local {
                    scope: target,
                    value: VirValueId::new(100),
                },
                0,
                7,
            )
            .unwrap(),
        ),
    };
    for state in [&mut a, &mut b] {
        state
            .predicates
            .get_mut(&PredicateHolder(0))
            .unwrap()
            .logical_parameters
            .push(local.clone());
    }
    let before = (a.clone(), b.clone());
    assert!(matches!(
        a.join_predicate_parameters(
            &b,
            &a.predicates[&PredicateHolder(0)],
            &b.predicates[&PredicateHolder(0)],
            target,
            &mut LogicBudget::default()
        ),
        Err(PredicateError::InvalidBinding)
    ));
    assert_eq!((a, b), before);
}
