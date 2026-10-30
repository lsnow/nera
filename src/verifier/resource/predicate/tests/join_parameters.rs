use super::*;
use crate::predicate_logic::*;

fn projected(boolean: bool, source: u32, fanout: bool) -> (ResourceState, PredicateDefinition) {
    let (state, def) = super::join_captures::captured(boolean, source, true);
    let mut edges = vec![(0, 0), (1, 1), (source, 100)];
    if fanout {
        edges.push((source, 101));
    }
    let edges: Vec<_> = edges
        .into_iter()
        .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)))
        .collect();
    let mut output = state.project_cfg_edge(&edges);
    for (source, target) in edges {
        output
            .define_value(target, *state.value(source).unwrap())
            .unwrap();
    }
    (output, def)
}

fn arguments(boolean: bool, id: u32) -> WitnessArguments<VirMemoryAccess, VirValueId> {
    let ty = if boolean {
        LogicType::Bool
    } else {
        LogicType::Usize
    };
    WitnessArguments {
        inputs: vec![(ty, WitnessInput::Scalar(VirValueId::new(id)))],
        arguments: vec![LogicExpression {
            nodes: vec![LogicNode {
                ty,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            }],
            root: 0,
        }],
        values: vec![],
    }
}

fn word_captures(public: u32, private: u32, edges: &[(u32, u32)]) -> ResourceState {
    let (_, def) = super::join_captures::captured(false, 90, true);
    let mut input = state();
    for id in [90, 91, 100] {
        input
            .define_value(
                VirValueId::new(id),
                AbstractValue::U64(U64Interval::new(1, 6).unwrap()),
            )
            .unwrap();
    }
    let mut witnesses = arguments(false, public);
    witnesses.inputs.push((
        LogicType::Usize,
        WitnessInput::Scalar(VirValueId::new(private)),
    ));
    witnesses.values.push((
        0,
        LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(1)),
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
    let edges: Vec<_> = [(0, 0), (1, 1)]
        .iter()
        .chain(edges)
        .map(|&(a, b)| (VirValueId::new(a), VirValueId::new(b)))
        .collect();
    let mut projected = folded.project_cfg_edge(&edges);
    for (a, b) in edges {
        projected
            .define_value(b, *folded.value(a).unwrap())
            .unwrap();
    }
    projected
}

#[test]
fn ambiguous_fanout_does_not_identify_independent_public_captures() {
    let a = word_captures(90, 90, &[(90, 100), (90, 101)]);
    let b = word_captures(91, 90, &[(91, 100), (90, 101)]);
    assert_eq!(a.join(&b), Err(ResourceJoinError::PredicateStateMismatch));
    assert_eq!(b.join(&a), Err(ResourceJoinError::PredicateStateMismatch));
}

#[test]
fn private_alias_names_cannot_be_used_as_evidence_for_a_public_capture() {
    let a = word_captures(90, 91, &[(90, 100)]);
    // The public snapshot was taken at SSA 100, but this current SSA 100
    // contains the unrelated private value. Numeric IDs are not identity.
    let b = word_captures(100, 91, &[(91, 100)]);
    assert_eq!(a.join(&b), Err(ResourceJoinError::PredicateStateMismatch));
    assert_eq!(b.join(&a), Err(ResourceJoinError::PredicateStateMismatch));
}

#[test]
fn public_captures_follow_common_cfg_values_without_granting_resources() {
    for boolean in [false, true] {
        for fanout in [false, true] {
            let (a, def) = projected(boolean, 90, fanout);
            let (b, _) = projected(boolean, 91, fanout);
            let before = (a.clone(), b.clone());
            let joined = a.join(&b).unwrap();
            assert_eq!(joined, b.join(&a).unwrap());
            assert_eq!(joined.join(&a).unwrap(), joined);
            assert_eq!(joined.join(&b).unwrap(), joined);
            assert_eq!(joined.widen(&b).unwrap(), joined);
            assert!(joined.covers_cfg_case(&a));
            assert!(joined.covers_cfg_case(&b));
            assert_eq!(joined.values, a.values);
            assert_eq!(joined.allocations, a.allocations);
            assert_eq!(joined.loans, a.loans);
            assert_eq!(
                joined.predicates[&PredicateHolder(0)].resources,
                a.predicates[&PredicateHolder(0)].resources
            );
            assert_eq!(
                joined.next_predicate_scope,
                a.next_predicate_scope.max(b.next_predicate_scope)
            );
            for id in if fanout { vec![100, 101] } else { vec![100] } {
                joined
                    .check_predicate_arguments(&def, PredicateHolder(0), &arguments(boolean, id))
                    .unwrap();
            }
            let actual = arguments(boolean, 100);
            let opened = transfer_predicate(
                &joined,
                &def,
                7,
                &PredicateEffect::WithArguments {
                    holder: PredicateHolder(0),
                    arguments: actual.clone(),
                    effect: Box::new(PredicateEffect::UnfoldNamed {
                        holder: PredicateHolder(0),
                        bindings: vec![binding(0)],
                        action: 40,
                    }),
                },
            )
            .unwrap()
            .output;
            let mut witnesses = actual;
            let ty = witnesses.inputs[0].0;
            witnesses.inputs.push((
                ty,
                WitnessInput::Opened {
                    action: 40,
                    holder: 0,
                    binder: 0,
                },
            ));
            witnesses.values.push((
                0,
                LogicExpression {
                    nodes: vec![LogicNode {
                        ty,
                        kind: LogicNodeKind::Binder(LogicBinder::Parameter(1)),
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
            evidence
                .output
                .check_predicate_arguments(&def, PredicateHolder(0), &arguments(boolean, 100))
                .unwrap();
            assert_eq!((a, b), before);
        }
    }
}

#[test]
fn overwritten_or_missing_values_cannot_reconnect_old_public_captures() {
    for boolean in [false, true] {
        let (a, _) = projected(boolean, 90, false);
        let (b, _) = projected(boolean, 91, false);
        for missing in [false, true] {
            let mut changed = b.clone();
            let id = VirValueId::new(100);
            if missing {
                changed.values.remove(&id);
            } else {
                // Even writing the same abstract interval destroys identity.
                let same = *changed.value(id).unwrap();
                *changed.value_mut(id).unwrap() = same;
            }
            assert_eq!(
                a.join(&changed),
                Err(ResourceJoinError::PredicateStateMismatch)
            );
            assert_eq!(
                changed.join(&a),
                Err(ResourceJoinError::PredicateStateMismatch)
            );
        }
    }
}

#[test]
fn public_parameter_adapter_budget_failure_is_transactional() {
    let (a, _) = projected(false, 90, false);
    let (b, _) = projected(false, 91, false);
    let before = (a.clone(), b.clone());
    let left = &a.predicates[&PredicateHolder(0)];
    let right = &b.predicates[&PredicateHolder(0)];
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert!(matches!(
        a.join_predicate_parameters(&b, left, right, left.logic_scope.unwrap(), &mut budget),
        Err(PredicateError::Budget)
    ));
    assert_eq!((a, b), before);
}

#[test]
fn renaming_cannot_collapse_public_atoms_across_separate_values() {
    let (a, _) = super::join_captures::captured(true, 90, true);
    let mut instance = a.predicates[&PredicateHolder(0)].clone();
    let scope = instance.logic_scope.unwrap();
    let mut second = instance.logical_parameters[0].clone();
    if let LogicValue::BoolAtom { atom, .. } = &mut second.value {
        *atom = logic::ObservationAtom::Local {
            scope,
            value: VirValueId::new(100),
        };
    } else {
        panic!("expected a captured Boolean");
    }
    instance.logical_parameters.push(second);
    let aliases = BTreeMap::from([(
        logic::LocalSnapshot {
            scope,
            value: VirValueId::new(90),
        },
        VirValueId::new(100),
    )]);
    assert_eq!(
        logic::normalize_closed_parameters_with_aliases(
            &instance,
            scope,
            &aliases,
            &mut LogicBudget::default()
        ),
        Err(PredicateError::InvalidBinding)
    );
}

fn projected_value(
    boolean: bool,
    source: u32,
    value: AbstractValue,
    fanout: bool,
) -> (ResourceState, PredicateDefinition) {
    projected_history(boolean, source, value, fanout, false)
}

fn projected_history(
    boolean: bool,
    source: u32,
    value: AbstractValue,
    fanout: bool,
    historical: bool,
) -> (ResourceState, PredicateDefinition) {
    let (state, def) =
        super::join_captures::captured_with_history(boolean, source, true, value, historical);
    let mut edges = vec![(0, 0), (1, 1), (source, 100)];
    if fanout {
        edges.push((source, 101));
    }
    let edges: Vec<_> = edges
        .into_iter()
        .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)))
        .collect();
    let mut projected = state.project_cfg_edge(&edges);
    for (a, b) in edges {
        projected.define_value(b, *state.value(a).unwrap()).unwrap();
    }
    (projected, def)
}

#[test]
fn public_capture_joins_cover_both_predecessors_without_retaining_branch_truth() {
    for boolean in [false, true] {
        for fanout in [false, true] {
            let value = |right| {
                if boolean {
                    AbstractValue::Bool(if right {
                        AbstractBool::False
                    } else {
                        AbstractBool::True
                    })
                } else {
                    AbstractValue::U64(if right {
                        U64Interval::new(5, 6).unwrap()
                    } else {
                        U64Interval::new(1, 2).unwrap()
                    })
                }
            };
            let (a, def) = projected_value(boolean, 90, value(false), fanout);
            let (b, _) = projected_value(boolean, 91, value(true), fanout);
            let before = (a.clone(), b.clone());
            let joined = a.join(&b).unwrap();
            assert_eq!(joined, b.join(&a).unwrap());
            assert_eq!(joined.join(&a).unwrap(), joined);
            assert_eq!(joined.join(&b).unwrap(), joined);
            assert_eq!(joined.widen(&b).unwrap(), joined);
            let wide = a.widen(&joined).unwrap();
            assert!(wide.covers_cfg_case(&joined));
            assert_eq!(wide.widen(&joined).unwrap(), wide);
            if !boolean {
                let LogicValue::Word(word) =
                    &wide.predicates[&PredicateHolder(0)].logical_parameters[0].value
                else {
                    panic!()
                };
                assert_eq!((word.lower, word.upper), (1, u64::MAX));
            }
            wide.check_predicate_arguments(&def, PredicateHolder(0), &arguments(boolean, 100))
                .unwrap();
            assert!(joined.covers_cfg_case(&a));
            assert!(joined.covers_cfg_case(&b));
            assert_eq!(joined.allocations, a.allocations);
            assert_eq!(joined.loans, a.loans);
            assert_eq!(
                joined.predicates[&PredicateHolder(0)].resources,
                a.predicates[&PredicateHolder(0)].resources
            );
            let merged = &joined.predicates[&PredicateHolder(0)].logical_parameters[0];
            if boolean {
                assert!(matches!(
                    merged.value,
                    LogicValue::BoolAtom { known: None, .. }
                ));
                for truth in [false, true] {
                    let literal = TypedLogicValue {
                        ty: LogicType::Bool,
                        value: LogicValue::Bool(Some(truth)),
                    };
                    assert_eq!(
                        joined.predicate_argument_equality(
                            &joined.predicates[&PredicateHolder(0)],
                            merged.clone(),
                            literal,
                            &mut LogicBudget::default()
                        ),
                        Ok(false)
                    );
                }
            } else {
                let LogicValue::Word(word) = &merged.value else {
                    panic!()
                };
                assert_eq!((word.lower, word.upper), (1, 6));
                assert_eq!(word.terms.len(), 1);
            }
            for id in if fanout { vec![100, 101] } else { vec![100] } {
                joined
                    .check_predicate_arguments(&def, PredicateHolder(0), &arguments(boolean, id))
                    .unwrap();
            }
            let opened = transfer_predicate(
                &joined,
                &def,
                7,
                &PredicateEffect::WithArguments {
                    holder: PredicateHolder(0),
                    arguments: arguments(boolean, 100),
                    effect: Box::new(PredicateEffect::UnfoldNamed {
                        holder: PredicateHolder(0),
                        bindings: vec![binding(0)],
                        action: 40,
                    }),
                },
            )
            .unwrap()
            .output;
            let mut actual = arguments(boolean, 100);
            actual.values.push((
                0,
                LogicExpression {
                    nodes: vec![LogicNode {
                        ty: actual.inputs[0].0,
                        kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
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
                    witnesses: actual,
                },
            )
            .unwrap();
            check_predicate_evidence(&opened, &evidence).unwrap();
            assert_eq!((a, b), before);
        }
    }
}

#[test]
fn widening_public_facts_requires_valid_actual_sources_on_each_predecessor() {
    let (a, _) = projected_value(true, 90, AbstractValue::Bool(AbstractBool::True), true);
    let (b, _) = projected_value(true, 91, AbstractValue::Bool(AbstractBool::False), true);
    for failure in 0..5 {
        let mut bad = b.clone();
        match failure {
            0 => {
                let same = *bad.value(VirValueId::new(100)).unwrap();
                *bad.value_mut(VirValueId::new(100)).unwrap() = same;
                let same = *bad.value(VirValueId::new(101)).unwrap();
                *bad.value_mut(VirValueId::new(101)).unwrap() = same;
            }
            1 => {
                bad.values.insert(
                    VirValueId::new(101),
                    AbstractValue::Bool(AbstractBool::True),
                );
            }
            2 => {
                bad.values.insert(
                    VirValueId::new(101),
                    AbstractValue::U64(U64Interval::exact(0)),
                );
            }
            3 => {
                for id in [100, 101] {
                    bad.values
                        .insert(VirValueId::new(id), AbstractValue::Bool(AbstractBool::True));
                }
            }
            _ => {
                if let LogicValue::BoolAtom { negated, .. } = &mut bad
                    .predicates
                    .get_mut(&PredicateHolder(0))
                    .unwrap()
                    .logical_parameters[0]
                    .value
                {
                    *negated = true;
                }
            }
        }
        let before = (a.clone(), bad.clone());
        assert_eq!(a.join(&bad), Err(ResourceJoinError::PredicateStateMismatch));
        assert_eq!(bad.join(&a), Err(ResourceJoinError::PredicateStateMismatch));
        assert_eq!((a.clone(), bad), before);
    }
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert!(matches!(
        a.join_predicate_parameters(
            &b,
            &a.predicates[&PredicateHolder(0)],
            &b.predicates[&PredicateHolder(0)],
            a.predicates[&PredicateHolder(0)].logic_scope.unwrap(),
            &mut budget
        ),
        Err(PredicateError::Budget)
    ));
}

#[test]
fn historical_public_captures_align_via_actual_common_slots_and_remain_usable() {
    for boolean in [false, true] {
        for (left_history, right_history) in [(true, true), (true, false), (false, true)] {
            for fanout in [false, true] {
                let value = |right| {
                    if boolean {
                        AbstractValue::Bool(if right {
                            AbstractBool::False
                        } else {
                            AbstractBool::True
                        })
                    } else {
                        AbstractValue::U64(if right {
                            U64Interval::new(5, 6).unwrap()
                        } else {
                            U64Interval::new(1, 2).unwrap()
                        })
                    }
                };
                let (a, def) = projected_history(boolean, 90, value(false), fanout, left_history);
                let (b, _) = projected_history(boolean, 91, value(true), fanout, right_history);
                let before = (a.clone(), b.clone());
                let joined = a.join(&b).unwrap();
                assert_eq!(joined, b.join(&a).unwrap());
                assert!(joined.covers_cfg_case(&a));
                assert!(joined.covers_cfg_case(&b));
                assert_eq!(joined.join(&a).unwrap(), joined);
                assert_eq!(joined.widen(&b).unwrap(), joined);
                let wide = a.widen(&joined).unwrap();
                assert!(wide.covers_cfg_case(&joined));
                assert_eq!(joined.allocations, a.allocations);
                assert_eq!(joined.loans, a.loans);
                assert!(joined.word_origin(VirValueId::new(100)).is_none());
                assert!(joined.bool_origin(VirValueId::new(100)).is_none());
                for id in if fanout { vec![100, 101] } else { vec![100] } {
                    joined
                        .check_predicate_arguments(
                            &def,
                            PredicateHolder(0),
                            &arguments(boolean, id),
                        )
                        .unwrap();
                }
                wide.check_predicate_arguments(&def, PredicateHolder(0), &arguments(boolean, 100))
                    .unwrap();
                let opened = transfer_predicate(
                    &joined,
                    &def,
                    7,
                    &PredicateEffect::WithArguments {
                        holder: PredicateHolder(0),
                        arguments: arguments(boolean, 100),
                        effect: Box::new(PredicateEffect::UnfoldNamed {
                            holder: PredicateHolder(0),
                            bindings: vec![binding(0)],
                            action: 40,
                        }),
                    },
                )
                .unwrap()
                .output;
                let mut actual = arguments(boolean, 100);
                actual.values.push((0, actual.arguments[0].clone()));
                let evidence = transfer_predicate(
                    &opened,
                    &def,
                    7,
                    &PredicateEffect::FoldWithWitnesses {
                        holder: PredicateHolder(0),
                        bindings: vec![binding(0)],
                        witnesses: actual,
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
fn unchanged_historical_sources_keep_their_identity_instead_of_local_rebinding() {
    for boolean in [false, true] {
        let value = if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::new(1, 6).unwrap())
        };
        let (a, def) = projected_history(boolean, 90, value, true, true);
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
        a.join(&a)
            .unwrap()
            .check_predicate_arguments(&def, PredicateHolder(0), &arguments(boolean, 100))
            .unwrap();
    }
}

#[test]
fn historical_source_alignment_rejects_missing_changed_foreign_and_ambiguous_evidence() {
    for boolean in [false, true] {
        let value = if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::new(1, 6).unwrap())
        };
        let (a, _) = projected_history(boolean, 90, value, true, true);
        let (b, _) = projected_history(boolean, 91, value, true, true);
        for failure in 0..6 {
            let mut bad = b.clone();
            match failure {
                0 => {
                    for id in [100, 101] {
                        *bad.value_mut(VirValueId::new(id)).unwrap() = value;
                    }
                }
                1 => {
                    bad.values.insert(
                        VirValueId::new(101),
                        if boolean {
                            AbstractValue::U64(U64Interval::exact(0))
                        } else {
                            AbstractValue::Bool(AbstractBool::Unknown)
                        },
                    );
                }
                2 => {
                    // A second unrelated source on one predecessor must not
                    // collapse onto the first predecessor's duplicated source.
                    if boolean {
                        bad.set_bool_origin(
                            VirValueId::new(101),
                            BoolOrigin::Parameter {
                                function: crate::VirFunctionId::new(9),
                                value: VirValueId::new(99),
                            },
                        );
                    } else {
                        let mut origin = bad.word_origin(VirValueId::new(101)).unwrap();
                        origin.first.root =
                            crate::verifier::resource::ScalarOriginRoot::Parameter {
                                function: crate::VirFunctionId::new(9),
                                value: VirValueId::new(99),
                            };
                        bad.set_word_origin(VirValueId::new(101), origin);
                    }
                }
                3 | 4 => {
                    let value = &mut bad
                        .predicates
                        .get_mut(&PredicateHolder(0))
                        .unwrap()
                        .logical_parameters[0]
                        .value;
                    let change = |atom: &mut logic::ObservationAtom| match atom {
                        logic::ObservationAtom::Historical { local, scope, .. }
                        | logic::ObservationAtom::HistoricalBool { local, scope, .. } => {
                            if failure == 3 {
                                *local = false;
                            } else {
                                scope.instance += 1;
                            }
                        }
                        _ => panic!(),
                    };
                    match value {
                        LogicValue::BoolAtom { atom, .. } => change(atom),
                        LogicValue::Word(word) => {
                            word.terms = std::mem::take(&mut word.terms)
                                .into_iter()
                                .map(|(mut atom, n)| {
                                    change(&mut atom);
                                    (atom, n)
                                })
                                .collect();
                        }
                        _ => panic!(),
                    }
                }
                _ => {
                    // Equal current values cannot replace a complete origin.
                    for id in [100, 101] {
                        if boolean {
                            bad.set_bool_origin(
                                VirValueId::new(id),
                                BoolOrigin::Parameter {
                                    function: crate::VirFunctionId::new(1),
                                    value: VirValueId::new(91),
                                },
                            );
                        } else {
                            let origin = bad
                                .word_origin(VirValueId::new(id))
                                .unwrap()
                                .scale(2)
                                .unwrap();
                            bad.set_word_origin(VirValueId::new(id), origin);
                        }
                    }
                }
            }
            let before = (a.clone(), bad.clone());
            assert_eq!(a.join(&bad), Err(ResourceJoinError::PredicateStateMismatch));
            assert_eq!(bad.join(&a), Err(ResourceJoinError::PredicateStateMismatch));
            assert_eq!((a.clone(), bad), before);
        }
        let mut budget = LogicBudget::default();
        budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
        assert!(matches!(
            a.join_predicate_parameters(
                &b,
                &a.predicates[&PredicateHolder(0)],
                &b.predicates[&PredicateHolder(0)],
                a.predicates[&PredicateHolder(0)].logic_scope.unwrap(),
                &mut budget
            ),
            Err(PredicateError::Budget)
        ));
    }
}

#[test]
fn explicit_historical_rebinding_cannot_bypass_scope_or_injectivity() {
    let (a, _) = projected_history(
        true,
        90,
        AbstractValue::Bool(AbstractBool::Unknown),
        false,
        true,
    );
    let original = a.predicates[&PredicateHolder(0)].clone();
    let scope = original.logic_scope.unwrap();
    let LogicValue::BoolAtom {
        atom: original_atom,
        ..
    } = &original.logical_parameters[0].value
    else {
        panic!()
    };
    for foreign in [false, true] {
        let mut invalid = original.clone();
        let LogicValue::BoolAtom { atom, .. } = &mut invalid.logical_parameters[0].value else {
            panic!()
        };
        let logic::ObservationAtom::HistoricalBool { local, scope, .. } = atom else {
            panic!()
        };
        if foreign {
            *local = false;
        } else {
            scope.instance += 1;
        }
        let mapping = BTreeMap::from([(atom.clone(), VirValueId::new(100))]);
        assert_eq!(
            logic::normalize_closed_parameters_with_sources(
                &invalid,
                original.logic_scope.unwrap(),
                &mapping,
                &mut LogicBudget::default()
            ),
            Err(PredicateError::InvalidBinding)
        );
    }
    let mut duplicated = original.clone();
    let mut second = original.logical_parameters[0].clone();
    let LogicValue::BoolAtom {
        atom: second_atom, ..
    } = &mut second.value
    else {
        panic!()
    };
    let logic::ObservationAtom::HistoricalBool { origin, .. } = second_atom else {
        panic!()
    };
    *origin = BoolOrigin::Parameter {
        function: crate::VirFunctionId::new(0),
        value: VirValueId::new(91),
    };
    let mapping = BTreeMap::from([
        (original_atom.clone(), VirValueId::new(100)),
        (second_atom.clone(), VirValueId::new(100)),
    ]);
    duplicated.logical_parameters.push(second);
    assert_eq!(
        logic::normalize_closed_parameters_with_sources(
            &duplicated,
            scope,
            &mapping,
            &mut LogicBudget::default()
        ),
        Err(PredicateError::InvalidBinding)
    );
}
