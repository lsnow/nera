use super::*;
use crate::predicate_logic::*;

#[derive(Clone, Copy)]
enum Form {
    Offset,
    Scale,
    Subtract,
    Negated,
    Boolean,
    And,
    Or,
    Equal,
    Compare,
    SumAndFixed,
    Difference,
}

impl Form {
    fn input_bool(self) -> bool {
        matches!(
            self,
            Self::Negated | Self::Boolean | Self::And | Self::Or | Self::Equal
        )
    }
    fn result_type(self) -> LogicType<VirMemoryAccess> {
        if matches!(
            self,
            Self::Negated | Self::Boolean | Self::Compare | Self::And | Self::Or | Self::Equal
        ) {
            LogicType::Bool
        } else {
            LogicType::Usize
        }
    }
    fn arguments(self, x: u32, y: u32) -> WitnessArguments<VirMemoryAccess, VirValueId> {
        let ty = if self.input_bool() {
            LogicType::Bool
        } else {
            LogicType::Usize
        };
        let mut inputs = vec![(ty, WitnessInput::Scalar(VirValueId::new(x)))];
        let mut nodes = vec![LogicNode {
            ty,
            kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
        }];
        match self {
            Self::Offset => {
                nodes.push(LogicNode {
                    ty,
                    kind: LogicNodeKind::Word(1),
                });
                nodes.push(LogicNode {
                    ty,
                    kind: LogicNodeKind::Add(0, 1),
                });
            }
            Self::Scale => nodes.push(LogicNode {
                ty,
                kind: LogicNodeKind::Scale {
                    operand: 0,
                    factor: 2,
                },
            }),
            Self::Subtract => {
                nodes.push(LogicNode {
                    ty,
                    kind: LogicNodeKind::Word(10),
                });
                nodes.push(LogicNode {
                    ty,
                    kind: LogicNodeKind::Sub(1, 0),
                });
            }
            Self::Boolean => {}
            Self::Negated => nodes.push(LogicNode {
                ty,
                kind: LogicNodeKind::Not(0),
            }),
            Self::Compare
            | Self::SumAndFixed
            | Self::Difference
            | Self::And
            | Self::Or
            | Self::Equal => {
                inputs.push((ty, WitnessInput::Scalar(VirValueId::new(y))));
                nodes.push(LogicNode {
                    ty,
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(1)),
                });
                nodes.push(LogicNode {
                    ty: self.result_type(),
                    kind: if matches!(self, Self::And) {
                        LogicNodeKind::And(0, 1)
                    } else if matches!(self, Self::Or) {
                        LogicNodeKind::Or(0, 1)
                    } else if matches!(self, Self::Equal) {
                        LogicNodeKind::Equal(0, 1)
                    } else if matches!(self, Self::Compare) {
                        LogicNodeKind::LessEqual(0, 1)
                    } else if matches!(self, Self::Difference) {
                        LogicNodeKind::Sub(0, 1)
                    } else {
                        LogicNodeKind::Add(0, 1)
                    },
                });
            }
        }
        let root = nodes.len() as u32 - 1;
        let mut arguments = vec![LogicExpression { nodes, root }];
        if matches!(self, Self::SumAndFixed) {
            arguments.push(LogicExpression {
                nodes: vec![LogicNode {
                    ty,
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(1)),
                }],
                root: 0,
            });
        }
        WitnessArguments {
            inputs,
            arguments,
            values: vec![],
        }
    }
    fn fold(
        self,
        input: &ResourceState,
        def: &PredicateDefinition,
        x: u32,
        y: u32,
    ) -> ResourceState {
        let mut witnesses = self.arguments(x, y);
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
            input,
            def,
            7,
            &PredicateEffect::FoldWithWitnesses {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
                witnesses,
            },
        )
        .unwrap();
        check_predicate_evidence(input, &evidence).unwrap();
        evidence.output
    }
}

fn entry(form: Form) -> (ResourceState, PredicateDefinition, LoopPredicateParameters) {
    entry_with_history(form, false)
}

fn entry_with_history(
    form: Form,
    historical: bool,
) -> (ResourceState, PredicateDefinition, LoopPredicateParameters) {
    entry_with_source_shape(form, historical, 0)
}

fn entry_with_source_shape(
    form: Form,
    historical: bool,
    shape: u8,
) -> (ResourceState, PredicateDefinition, LoopPredicateParameters) {
    entry_with_shapes(form, historical, shape, 0)
}

fn entry_with_shapes(
    form: Form,
    historical: bool,
    shape: u8,
    fixed_shape: u8,
) -> (ResourceState, PredicateDefinition, LoopPredicateParameters) {
    entry_with_ranges(form, historical, shape, fixed_shape, false)
}

fn entry_with_ranges(
    form: Form,
    historical: bool,
    shape: u8,
    fixed_shape: u8,
    singleton: bool,
) -> (ResourceState, PredicateDefinition, LoopPredicateParameters) {
    let mut def = logical_definition();
    def.logic.parameters.push(LogicParameter {
        position: 1,
        name: "expression".into(),
        ty: form.result_type(),
    });
    if matches!(form, Form::SumAndFixed) {
        def.logic.parameters.push(LogicParameter {
            position: 2,
            name: "fixed".into(),
            ty: LogicType::Usize,
        });
    }
    let mut input = state();
    for id in [90, 92] {
        input
            .define_value(
                VirValueId::new(id),
                if form.input_bool() {
                    AbstractValue::Bool(if singleton {
                        AbstractBool::True
                    } else {
                        AbstractBool::Unknown
                    })
                } else {
                    AbstractValue::U64(if singleton {
                        U64Interval::exact(1)
                    } else if matches!(form, Form::Difference) && id == 90 {
                        U64Interval::new(4, 7).unwrap()
                    } else {
                        U64Interval::new(1, 3).unwrap()
                    })
                },
            )
            .unwrap();
    }
    if historical {
        for id in [90, 92] {
            let slot = VirValueId::new(id);
            if form.input_bool() {
                input.set_bool_origin(
                    slot,
                    BoolOrigin::Parameter {
                        function: crate::VirFunctionId::new(0),
                        value: slot,
                    },
                );
            } else {
                let Some(AbstractValue::U64(interval)) = input.value(slot) else {
                    unreachable!()
                };
                input.set_word_origin(
                    slot,
                    ScalarOrigin {
                        first: crate::verifier::resource::ScalarOriginCell {
                            root: crate::verifier::resource::ScalarOriginRoot::Parameter {
                                function: crate::VirFunctionId::new(0),
                                value: slot,
                            },
                            initial_lower: interval.lower(),
                            initial_upper: interval.upper(),
                        },
                        scale: 1,
                        second: None,
                        addend: 0,
                    },
                );
            }
        }
    }
    if historical && !form.input_bool() && shape != 0 {
        let slot = VirValueId::new(90);
        let original = input.word_origin(slot).unwrap();
        let origin = match shape {
            1 => original.add(1).unwrap(),
            2 => original.scale(2).unwrap(),
            3 => {
                let mut other = original;
                other.first.root = crate::verifier::resource::ScalarOriginRoot::Parameter {
                    function: crate::VirFunctionId::new(0),
                    value: VirValueId::new(95),
                };
                original.sum(other).unwrap()
            }
            4 => original.scale(2).unwrap().add(1).unwrap(),
            5 => original
                .sum(input.word_origin(VirValueId::new(92)).unwrap())
                .unwrap(),
            _ => unreachable!(),
        };
        *input.value_mut(slot).unwrap() = AbstractValue::U64(origin.initial_interval().unwrap());
        input.set_word_origin(slot, origin);
    }
    if historical && fixed_shape != 0 {
        let slot = VirValueId::new(92);
        let original = input.word_origin(slot).unwrap();
        let origin = match fixed_shape {
            1 => original.add(1).unwrap(),
            2 => original.scale(2).unwrap(),
            3 => {
                let mut other = original;
                other.first.root = crate::verifier::resource::ScalarOriginRoot::Parameter {
                    function: crate::VirFunctionId::new(0),
                    value: VirValueId::new(96),
                };
                original.sum(other).unwrap()
            }
            4 => original.scale(2).unwrap().add(1).unwrap(),
            _ => unreachable!(),
        };
        *input.value_mut(slot).unwrap() = AbstractValue::U64(origin.initial_interval().unwrap());
        input.set_word_origin(slot, origin);
    }
    let entry = form.fold(&input, &def, 90, 92);
    let plan = entry
        .loop_predicate_parameters(
            &BTreeSet::from([VirValueId::new(90), VirValueId::new(92)]),
            &BTreeSet::new(),
            &BTreeSet::from([PredicateHolder(0)]),
        )
        .unwrap();
    assert!(plan.expression(PredicateHolder(0), 0).is_some());
    (entry, def, plan)
}

fn frame(entry: &ResourceState, form: Form, bounded: bool) -> ResourceState {
    let mut head = ResourceState::new();
    assert!(head.inherit_loop_resources_with_predicates(
        entry,
        &BTreeSet::new(),
        &BTreeSet::from([PredicateHolder(0)])
    ));
    head.inherit_loop_scalar_frame(entry, &BTreeSet::new());
    for id in [0, 1] {
        let id = VirValueId::new(id);
        head.define_value(id, *entry.value(id).unwrap()).unwrap();
    }
    for id in [90, 92] {
        head.define_value(
            VirValueId::new(id),
            if form.input_bool() {
                AbstractValue::Bool(AbstractBool::Unknown)
            } else {
                AbstractValue::U64(if bounded {
                    U64Interval::new(0, 7).unwrap()
                } else {
                    U64Interval::unknown()
                })
            },
        )
        .unwrap();
    }
    head
}

#[test]
fn compound_public_parameters_rebuild_at_the_head_and_check_each_backedge() {
    for form in [
        Form::Offset,
        Form::Scale,
        Form::Subtract,
        Form::Negated,
        Form::Compare,
        Form::And,
        Form::Or,
        Form::Equal,
    ] {
        for historical in [false, true] {
            for shape in 0..=if historical && !form.input_bool() {
                5
            } else {
                0
            } {
                let (entry, def, plan) = entry_with_source_shape(form, historical, shape);
                let repacked = BTreeSet::from([PredicateHolder(0)]);
                let mut head = frame(&entry, form, true);
                head.abstract_loop_predicates_after_havoc_with_parameters(
                    &entry,
                    &BTreeSet::new(),
                    &repacked,
                    &plan,
                )
                .unwrap();
                assert_eq!(head.allocations, entry.allocations);
                assert_eq!(head.loans, entry.loans);
                head.check_predicate_arguments(&def, PredicateHolder(0), &form.arguments(90, 92))
                    .unwrap();
                // Exit/branch refinement can make the actual expression constant.
                // This must use the live aliases, not the old capture's interval.
                let mut narrowed = head.clone();
                if form.input_bool() {
                    assert!(narrowed.narrow_bool_value(VirValueId::new(90), true));
                } else {
                    narrowed.narrow_word_interval(VirValueId::new(90), U64Interval::exact(2));
                    narrowed.narrow_word_interval(VirValueId::new(92), U64Interval::exact(3));
                }
                narrowed
                    .check_predicate_arguments(&def, PredicateHolder(0), &form.arguments(90, 92))
                    .unwrap();
                let same = *narrowed.value(VirValueId::new(90)).unwrap();
                *narrowed.value_mut(VirValueId::new(90)).unwrap() = same;
                assert!(
                    narrowed
                        .check_predicate_arguments(
                            &def,
                            PredicateHolder(0),
                            &form.arguments(90, 92)
                        )
                        .is_err()
                );
                let open = transfer_predicate(
                    &head,
                    &def,
                    7,
                    &PredicateEffect::WithArguments {
                        holder: PredicateHolder(0),
                        arguments: form.arguments(90, 92),
                        effect: Box::new(PredicateEffect::UnfoldNamed {
                            holder: PredicateHolder(0),
                            bindings: vec![binding(0)],
                            action: 60,
                        }),
                    },
                )
                .unwrap()
                .output;
                for stale in [false, true] {
                    let mut updated = open.clone();
                    for id in [91, 93] {
                        updated
                            .define_value(
                                VirValueId::new(id),
                                if form.input_bool() {
                                    AbstractValue::Bool(AbstractBool::Unknown)
                                } else {
                                    AbstractValue::U64(U64Interval::new(2, 7).unwrap())
                                },
                            )
                            .unwrap();
                    }
                    let closed = if stale {
                        form.fold(&updated, &def, 90, 92)
                    } else {
                        form.fold(&updated, &def, 91, 93)
                    };
                    let renames = [(0, 0), (1, 1), (91, 90), (93, 92)]
                        .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
                    let mut back = closed.project_cfg_edge(&renames);
                    for (a, b) in renames {
                        back.define_value(b, *closed.value(a).unwrap()).unwrap();
                    }
                    assert_eq!(
                        back.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan),
                        !stale
                    );
                }
            }
        }
    }
}

#[test]
fn unbounded_expression_havoc_fails_without_leaking_new_aliases_or_epochs() {
    for form in [Form::Offset, Form::Scale, Form::Subtract] {
        let (entry, _, plan) = entry(form);
        let mut head = frame(&entry, form, false);
        let before = head.clone();
        assert!(
            head.abstract_loop_predicates_after_havoc_with_parameters(
                &entry,
                &BTreeSet::new(),
                &BTreeSet::from([PredicateHolder(0)]),
                &plan
            )
            .is_err()
        );
        assert_eq!(head, before);
    }
}

#[test]
fn conflicting_surviving_alias_facts_are_not_cherry_picked_for_parameter_equality() {
    for form in [Form::Offset, Form::Negated] {
        let (entry, def, plan) = entry(form);
        let mut head = frame(&entry, form, true);
        head.abstract_loop_predicates_after_havoc_with_parameters(
            &entry,
            &BTreeSet::new(),
            &BTreeSet::from([PredicateHolder(0)]),
            &plan,
        )
        .unwrap();
        let edges = [(0, 0), (1, 1), (90, 90), (90, 94)]
            .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
        let mut conflicting = head.project_cfg_edge(&edges);
        for (a, b) in edges {
            conflicting
                .define_value(b, *head.value(a).unwrap())
                .unwrap();
        }
        // Deliberately inconsistent abstract facts for the same captured value.
        // Production writes use value_mut and invalidate these aliases instead.
        for (id, flag) in [(90, false), (94, true)] {
            conflicting.values.insert(
                VirValueId::new(id),
                if form.input_bool() {
                    AbstractValue::Bool(if flag {
                        AbstractBool::True
                    } else {
                        AbstractBool::False
                    })
                } else {
                    AbstractValue::U64(U64Interval::exact(if flag { 3 } else { 2 }))
                },
            );
        }
        assert!(
            conflicting
                .check_predicate_arguments(&def, PredicateHolder(0), &form.arguments(90, 92))
                .is_err()
        );
    }
}

fn mixed_plan(entry: &ResourceState) -> LoopPredicateParameters {
    entry
        .loop_predicate_parameters(
            &BTreeSet::from([VirValueId::new(90)]),
            &BTreeSet::from([VirValueId::new(92)]),
            &BTreeSet::from([PredicateHolder(0)]),
        )
        .unwrap()
}

fn mixed_frame(entry: &ResourceState, form: Form) -> ResourceState {
    let mut head = frame(entry, form, true);
    head.inherit_loop_scalar_frame(entry, &BTreeSet::from([VirValueId::new(92)]));
    // The retained slot has the actual entry value, never the havoc range.
    head.narrow_word_interval(VirValueId::new(92), U64Interval::new(1, 3).unwrap());
    head
}

#[test]
fn mixed_parameters_preserve_fixed_capture_across_head_refold_and_backedge() {
    for form in [Form::SumAndFixed, Form::Compare] {
        for historical in [false, true] {
            for (shape, fixed_shape) in (0..=if historical { 5 } else { 0 })
                .map(|shape| (shape, 0))
                .chain((1..=if historical { 4 } else { 0 }).map(|fixed| (0, fixed)))
            {
                let (entry, def, _) = entry_with_shapes(form, historical, shape, fixed_shape);
                let plan = mixed_plan(&entry);
                let holder = PredicateHolder(0);
                let repacked = BTreeSet::from([holder]);
                assert!(plan.expression(holder, 0).is_some());
                assert!(plan.expression(holder, 1).is_none());
                let fixed = entry.predicates[&holder].logical_local_aliases[&VirValueId::new(92)];
                let mut head = mixed_frame(&entry, form);
                head.abstract_loop_predicates_after_havoc_with_parameters(
                    &entry,
                    &BTreeSet::new(),
                    &repacked,
                    &plan,
                )
                .unwrap();
                assert_eq!(
                    head.predicates[&holder].logical_local_aliases[&VirValueId::new(92)],
                    fixed
                );
                if matches!(form, Form::SumAndFixed) && !historical {
                    assert_eq!(
                        head.predicates[&holder].logical_parameters[1],
                        entry.predicates[&holder].logical_parameters[1]
                    );
                }
                head.check_predicate_arguments(&def, holder, &form.arguments(90, 92))
                    .unwrap();
                let mut narrowed = head.clone();
                narrowed.narrow_word_interval(VirValueId::new(90), U64Interval::exact(2));
                narrowed.narrow_word_interval(VirValueId::new(92), U64Interval::exact(3));
                narrowed
                    .check_predicate_arguments(&def, holder, &form.arguments(90, 92))
                    .unwrap();
                let open = transfer_predicate(
                    &head,
                    &def,
                    7,
                    &PredicateEffect::WithArguments {
                        holder,
                        arguments: form.arguments(90, 92),
                        effect: Box::new(PredicateEffect::UnfoldNamed {
                            holder,
                            bindings: vec![binding(0)],
                            action: 60,
                        }),
                    },
                )
                .unwrap()
                .output;
                for stale in [false, true] {
                    let mut updated = open.clone();
                    updated
                        .define_value(
                            VirValueId::new(91),
                            AbstractValue::U64(U64Interval::new(2, 7).unwrap()),
                        )
                        .unwrap();
                    let closed = form.fold(&updated, &def, if stale { 90 } else { 91 }, 92);
                    let renames = [(0, 0), (1, 1), (91, 90), (92, 92)]
                        .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
                    let mut back = closed.project_cfg_edge(&renames);
                    for (a, b) in renames {
                        back.define_value(b, *closed.value(a).unwrap()).unwrap();
                    }
                    assert_eq!(
                        back.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan),
                        !stale
                    );
                    // Even a numerically identical retained slot loses its evidence on
                    // a write. The matcher must not fall back to the new current value.
                    let same = *back.value(VirValueId::new(92)).unwrap();
                    *back.value_mut(VirValueId::new(92)).unwrap() = same;
                    assert!(!back.loop_resources_match_with_parameters(
                        &entry,
                        &[],
                        &repacked,
                        &plan
                    ));
                }
                // Refolding with a newly captured fixed operand is also insufficient,
                // even if the backedge projects it to the original fixed slot.
                let mut replaced = open.clone();
                for id in [91, 93] {
                    replaced
                        .define_value(
                            VirValueId::new(id),
                            AbstractValue::U64(U64Interval::new(1, 3).unwrap()),
                        )
                        .unwrap();
                }
                let closed = form.fold(&replaced, &def, 91, 93);
                let renames = [(0, 0), (1, 1), (91, 90), (93, 92)]
                    .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
                let mut back = closed.project_cfg_edge(&renames);
                for (a, b) in renames {
                    back.define_value(b, *closed.value(a).unwrap()).unwrap();
                }
                assert!(!back.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan));

                let mut budget = LogicBudget::default();
                budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
                assert_eq!(
                    head.loop_parameter_actual(
                        &head.predicates[&holder],
                        plan.expression(holder, 0).unwrap(),
                        &mut budget,
                    ),
                    Err(PredicateError::Budget)
                );
            }
        }
    }
}

#[test]
fn mixed_parameter_selection_requires_explicit_retained_identity() {
    let (entry, _, _) = entry(Form::SumAndFixed);
    let changing = BTreeSet::from([VirValueId::new(90)]);
    let retained = BTreeSet::from([VirValueId::new(92)]);
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    assert_eq!(
        entry
            .loop_predicate_parameters(&changing, &BTreeSet::new(), &repacked)
            .unwrap(),
        LoopPredicateParameters::default()
    );
    assert!(
        entry
            .loop_predicate_parameters(&changing, &changing, &repacked)
            .is_err()
    );
    assert_eq!(
        entry
            .loop_predicate_parameters(
                &BTreeSet::new(),
                &BTreeSet::from([VirValueId::new(90), VirValueId::new(92)]),
                &repacked
            )
            .unwrap(),
        LoopPredicateParameters::default()
    );
    let mut ambiguous = entry.clone();
    let alias =
        ambiguous.predicates[&PredicateHolder(0)].logical_local_aliases[&VirValueId::new(92)];
    ambiguous
        .define_value(
            VirValueId::new(94),
            *entry.value(VirValueId::new(92)).unwrap(),
        )
        .unwrap();
    ambiguous
        .predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .logical_local_aliases
        .insert(VirValueId::new(94), alias);
    let mut fanout = retained.clone();
    fanout.insert(VirValueId::new(94));
    let fanout_plan = ambiguous
        .loop_predicate_parameters(&changing, &fanout, &repacked)
        .unwrap();
    assert_eq!(fanout_plan, mixed_plan(&entry));
    // Retained copies have the same immutable identity; contradictory bounds
    // must be rejected rather than selecting the more useful alias.
    ambiguous.values.insert(
        VirValueId::new(92),
        AbstractValue::U64(U64Interval::exact(1)),
    );
    ambiguous.values.insert(
        VirValueId::new(94),
        AbstractValue::U64(U64Interval::exact(3)),
    );
    assert!(
        ambiguous
            .loop_parameter_actual(
                &ambiguous.predicates[&PredicateHolder(0)],
                fanout_plan.expression(PredicateHolder(0), 0).unwrap(),
                &mut LogicBudget::default()
            )
            .is_err()
    );
}

#[test]
fn lost_or_replaced_fixed_identity_rolls_back_head_abstraction() {
    let form = Form::SumAndFixed;
    let (entry, _, _) = entry(form);
    let plan = mixed_plan(&entry);
    for replaced in [false, true] {
        let mut head = mixed_frame(&entry, form);
        let instance = head.predicates.get_mut(&PredicateHolder(0)).unwrap();
        let alias = instance
            .logical_local_aliases
            .remove(&VirValueId::new(92))
            .unwrap();
        if replaced {
            // The same SSA number with another capture epoch is a different
            // immutable value; no interval equality can restore the old one.
            instance.logical_local_aliases.insert(
                VirValueId::new(92),
                logic::LocalSnapshot {
                    scope: InstanceScope {
                        instance: alias.scope.instance + 100,
                        ..alias.scope
                    },
                    ..alias
                },
            );
        }
        let before = head.clone();
        assert!(
            head.abstract_loop_predicates_after_havoc_with_parameters(
                &entry,
                &BTreeSet::new(),
                &BTreeSet::from([PredicateHolder(0)]),
                &plan,
            )
            .is_err()
        );
        assert_eq!(head, before);
    }
}

fn order(state: &mut ResourceState, low: u32, high: u32) {
    use crate::verifier::relation::{
        RelationComparison,
        difference::{DifferenceLimits, DifferencePremise, word},
    };
    state.learn_relations(
        &[DifferencePremise::Compare {
            comparison: RelationComparison::LessOrEqual,
            left: word(VirValueId::new(low)),
            right: word(VirValueId::new(high)),
        }],
        DifferenceLimits::default(),
    );
}

#[test]
fn relational_difference_parameters_require_current_head_and_backedge_domains() {
    let form = Form::Difference;
    let (entry, def, plan) = entry(form);
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    let mut head = frame(&entry, form, true);
    let before = head.clone();
    assert!(
        head.abstract_loop_predicates_after_havoc_with_parameters(
            &entry,
            &BTreeSet::new(),
            &repacked,
            &plan
        )
        .is_err()
    );
    assert_eq!(head, before);
    order(&mut head, 92, 90);
    head.abstract_loop_predicates_after_havoc_with_parameters(
        &entry,
        &BTreeSet::new(),
        &repacked,
        &plan,
    )
    .unwrap();
    head.check_predicate_arguments(&def, PredicateHolder(0), &form.arguments(90, 92))
        .unwrap();
    let open = transfer_predicate(
        &head,
        &def,
        7,
        &PredicateEffect::WithArguments {
            holder: PredicateHolder(0),
            arguments: form.arguments(90, 92),
            effect: Box::new(PredicateEffect::UnfoldNamed {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
                action: 60,
            }),
        },
    )
    .unwrap()
    .output;
    let mut updated = open.clone();
    for id in [91, 93] {
        updated
            .define_value(
                VirValueId::new(id),
                AbstractValue::U64(U64Interval::new(0, 7).unwrap()),
            )
            .unwrap();
    }
    // Old head ordering does not establish a relation between the new inputs.
    let mut witnesses = form.arguments(91, 93);
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
    assert!(
        transfer_predicate(
            &updated,
            &def,
            7,
            &PredicateEffect::FoldWithWitnesses {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
                witnesses,
            }
        )
        .is_err()
    );
    order(&mut updated, 93, 91);
    for stale in [false, true] {
        let closed = if stale {
            form.fold(&updated, &def, 90, 92)
        } else {
            form.fold(&updated, &def, 91, 93)
        };
        let renames = [(0, 0), (1, 1), (91, 90), (93, 92)]
            .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
        let mut back = closed.project_cfg_edge(&renames);
        for (a, b) in renames {
            back.define_value(b, *closed.value(a).unwrap()).unwrap();
        }
        assert_eq!(
            back.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan),
            !stale
        );
        let same = *back.value(VirValueId::new(92)).unwrap();
        *back.value_mut(VirValueId::new(92)).unwrap() = same;
        assert!(!back.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan));
    }
}

#[test]
fn argument_relation_fallback_checks_overflow_before_cancellation() {
    let (entry, def, _) = entry(Form::Offset);
    let mut args = Form::Offset.arguments(90, 92);
    args.arguments[0].nodes.push(LogicNode {
        ty: LogicType::Usize,
        kind: LogicNodeKind::Sub(2, 1),
    });
    args.arguments[0].root = 3;
    let mut state = entry.clone();
    *state.value_mut(VirValueId::new(90)).unwrap() = AbstractValue::U64(U64Interval::unknown());
    // This algebraically equals x, but its x+1 intermediate is not defined.
    assert!(
        state
            .check_predicate_arguments(&def, PredicateHolder(0), &args)
            .is_err()
    );
}

fn copy_scalar_history(state: &mut ResourceState, from: u32, to: u32) {
    let from = VirValueId::new(from);
    let to = VirValueId::new(to);
    state.define_value(to, *state.value(from).unwrap()).unwrap();
    if let Some(origin) = state.word_origin(from) {
        state.set_word_origin(to, origin);
    }
    if let Some(origin) = state.bool_origin(from) {
        state.set_bool_origin(to, origin);
    }
}

#[test]
fn historical_binding_prefers_changing_slot_to_retained_entry_anchor() {
    for form in [Form::Offset, Form::Negated] {
        let (mut entry, def, expected) = entry_with_history(form, true);
        copy_scalar_history(&mut entry, 90, 94);
        let repacked = BTreeSet::from([PredicateHolder(0)]);
        let plan = entry
            .loop_predicate_parameters(
                &BTreeSet::from([VirValueId::new(90), VirValueId::new(92)]),
                &BTreeSet::from([VirValueId::new(94)]),
                &repacked,
            )
            .unwrap();
        assert_eq!(plan, expected);
        assert_eq!(
            entry
                .loop_predicate_parameters(
                    &BTreeSet::from([VirValueId::new(90), VirValueId::new(94)]),
                    &BTreeSet::new(),
                    &repacked
                )
                .unwrap(),
            LoopPredicateParameters::default()
        );
        let mut head = frame(&entry, form, true);
        head.inherit_loop_scalar_frame(&entry, &BTreeSet::from([VirValueId::new(94)]));
        head.define_value(
            VirValueId::new(94),
            *entry.value(VirValueId::new(94)).unwrap(),
        )
        .unwrap();
        head.abstract_loop_predicates_after_havoc_with_parameters(
            &entry,
            &BTreeSet::new(),
            &repacked,
            &plan,
        )
        .unwrap();
        // The immutable anchor must not pin the changing parameter to its entry
        // value. The normal header argument still matches after havoc.
        head.check_predicate_arguments(&def, PredicateHolder(0), &form.arguments(90, 92))
            .unwrap();
    }
}

#[test]
fn history_binding_requires_exact_or_integrally_rebased_sources() {
    for form in [Form::Offset, Form::Negated] {
        let (entry, _, _) = entry_with_history(form, true);
        let slot = VirValueId::new(90);
        for mode in 0..6 {
            let mut bad = entry.clone();
            match mode {
                0 => {
                    bad.word_origins.remove(&slot);
                    bad.bool_origins.remove(&slot);
                }
                1 => {
                    if form.input_bool() {
                        bad.set_bool_origin(
                            slot,
                            BoolOrigin::Parameter {
                                function: crate::VirFunctionId::new(99),
                                value: slot,
                            },
                        );
                    } else {
                        let mut origin = bad.word_origin(slot).unwrap();
                        origin.first.root =
                            crate::verifier::resource::ScalarOriginRoot::Parameter {
                                function: crate::VirFunctionId::new(99),
                                value: slot,
                            };
                        bad.set_word_origin(slot, origin);
                    }
                }
                2 => {
                    let value = &mut bad
                        .predicates
                        .get_mut(&PredicateHolder(0))
                        .unwrap()
                        .logical_parameters[0]
                        .value;
                    if let LogicValue::Word(word) = value {
                        let terms = std::mem::take(&mut word.terms);
                        word.terms = terms
                            .into_iter()
                            .map(|(a, c)| match a {
                                logic::ObservationAtom::Historical { scope, cell, .. } => (
                                    logic::ObservationAtom::Historical {
                                        scope,
                                        cell,
                                        local: false,
                                    },
                                    c,
                                ),
                                _ => panic!(),
                            })
                            .collect();
                    } else if let LogicValue::BoolAtom {
                        atom: logic::ObservationAtom::HistoricalBool { local, .. },
                        ..
                    } = value
                    {
                        *local = false;
                    } else {
                        panic!()
                    }
                }
                3 if !form.input_bool() => {
                    let origin = bad.word_origin(slot).unwrap().add(1).unwrap();
                    bad.set_word_origin(slot, origin);
                }
                4 if !form.input_bool() => {
                    let origin = bad.word_origin(slot).unwrap().scale(2).unwrap();
                    bad.set_word_origin(slot, origin);
                }
                5 if !form.input_bool() => {
                    let mut origin = bad.word_origin(slot).unwrap();
                    origin.first.initial_upper += 1;
                    bad.set_word_origin(slot, origin);
                }
                _ => {
                    let same = *bad.value(slot).unwrap();
                    *bad.value_mut(slot).unwrap() = same;
                }
            }
            let plan = bad
                .loop_predicate_parameters(
                    &BTreeSet::from([slot]),
                    &BTreeSet::new(),
                    &BTreeSet::from([PredicateHolder(0)]),
                )
                .unwrap();
            if mode == 3 && !form.input_bool() {
                // The complete source now equals the saved x+1 expression;
                // integral rebasing binds that value without inventing x.
                assert!(plan.expression(PredicateHolder(0), 0).is_some());
            } else {
                assert_eq!(plan, LoopPredicateParameters::default());
            }
        }
    }
}

#[test]
fn retained_history_survives_copies_but_not_conflicting_bounds_or_origin_loss() {
    let form = Form::SumAndFixed;
    let (mut entry, _, _) = entry_with_history(form, true);
    let expected = mixed_plan(&entry);
    copy_scalar_history(&mut entry, 92, 94);
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    let retained = BTreeSet::from([VirValueId::new(92), VirValueId::new(94)]);
    let plan = entry
        .loop_predicate_parameters(&BTreeSet::from([VirValueId::new(90)]), &retained, &repacked)
        .unwrap();
    assert_eq!(plan, expected);
    let mut head = mixed_frame(&entry, form);
    head.inherit_loop_scalar_frame(&entry, &retained);
    head.define_value(
        VirValueId::new(94),
        *entry.value(VirValueId::new(94)).unwrap(),
    )
    .unwrap();
    for lost in [false, true] {
        let mut invalid = head.clone();
        if lost {
            invalid.word_origins.remove(&VirValueId::new(92));
        } else {
            // Deliberately inconsistent analysis data: a normal write would
            // discard the origins. Domain reads must not cherry-pick aliases.
            invalid.values.insert(
                VirValueId::new(92),
                AbstractValue::U64(U64Interval::exact(1)),
            );
            invalid.values.insert(
                VirValueId::new(94),
                AbstractValue::U64(U64Interval::exact(3)),
            );
        }
        let before = invalid.clone();
        assert!(
            invalid
                .abstract_loop_predicates_after_havoc_with_parameters(
                    &entry,
                    &BTreeSet::new(),
                    &repacked,
                    &plan
                )
                .is_err()
        );
        assert_eq!(invalid, before);
    }
    head.abstract_loop_predicates_after_havoc_with_parameters(
        &entry,
        &BTreeSet::new(),
        &repacked,
        &plan,
    )
    .unwrap();
}

#[test]
fn historical_boolean_reader_rejects_conflicting_aliases_types_and_budget() {
    let (mut entry, _, _) = entry_with_history(Form::Negated, true);
    copy_scalar_history(&mut entry, 90, 94);
    let slot = VirValueId::new(90);
    let capture = logic::ScalarCapture::Bool(entry.bool_origin(slot).unwrap());
    let instance = &entry.predicates[&PredicateHolder(0)];
    assert!(
        entry
            .read_predicate_capture(
                instance,
                capture,
                slot,
                LogicType::Bool,
                &mut LogicBudget::default()
            )
            .is_ok()
    );
    assert!(
        entry
            .read_predicate_capture(
                instance,
                capture,
                slot,
                LogicType::Usize,
                &mut LogicBudget::default()
            )
            .is_err()
    );
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert_eq!(
        entry.read_predicate_capture(instance, capture, slot, LogicType::Bool, &mut budget),
        Err(PredicateError::Budget)
    );
    entry
        .values
        .insert(slot, AbstractValue::Bool(AbstractBool::True));
    entry.values.insert(
        VirValueId::new(94),
        AbstractValue::Bool(AbstractBool::False),
    );
    let before = entry.clone();
    assert_eq!(
        entry.read_predicate_capture(
            &entry.predicates[&PredicateHolder(0)],
            capture,
            slot,
            LogicType::Bool,
            &mut LogicBudget::default()
        ),
        Err(PredicateError::UnprovedRepresentation)
    );
    assert_eq!(entry, before);
}

#[test]
fn composite_sources_require_current_identity_and_unambiguous_coefficients() {
    let form = Form::Offset;
    for shape in 1..=5 {
        let (entry, _, plan) = entry_with_source_shape(form, true, shape);
        let repacked = BTreeSet::from([PredicateHolder(0)]);
        let changing = BTreeSet::from([VirValueId::new(90)]);
        let source = entry.word_origin(VirValueId::new(90)).unwrap();
        let mut missing = entry.clone();
        missing.word_origins.remove(&VirValueId::new(90));
        assert_eq!(
            missing
                .loop_predicate_parameters(&changing, &BTreeSet::new(), &repacked)
                .unwrap(),
            LoopPredicateParameters::default()
        );
        let mut foreign = entry.clone();
        let mut different = source;
        different.first.root = crate::verifier::resource::ScalarOriginRoot::Parameter {
            function: crate::VirFunctionId::new(99),
            value: VirValueId::new(90),
        };
        foreign.set_word_origin(VirValueId::new(90), different);
        assert_eq!(
            foreign
                .loop_predicate_parameters(&changing, &BTreeSet::new(), &repacked)
                .unwrap(),
            LoopPredicateParameters::default()
        );
        let mut ambiguous = entry.clone();
        copy_scalar_history(&mut ambiguous, 90, 94);
        assert_eq!(
            ambiguous
                .loop_predicate_parameters(
                    &BTreeSet::from([VirValueId::new(90), VirValueId::new(94)]),
                    &BTreeSet::new(),
                    &repacked
                )
                .unwrap(),
            LoopPredicateParameters::default()
        );
        let mut head = frame(&entry, form, false);
        let before = head.clone();
        assert!(
            head.abstract_loop_predicates_after_havoc_with_parameters(
                &entry,
                &BTreeSet::new(),
                &repacked,
                &plan
            )
            .is_err()
        );
        assert_eq!(head, before);
    }
}

#[test]
fn retained_composite_capture_reconciles_copies_and_rechecks_complete_origin() {
    for fixed_shape in 1..=4 {
        let (mut entry, def, _) = entry_with_shapes(Form::SumAndFixed, true, 0, fixed_shape);
        let expected = mixed_plan(&entry);
        copy_scalar_history(&mut entry, 92, 94);
        let repacked = BTreeSet::from([PredicateHolder(0)]);
        let retained = BTreeSet::from([VirValueId::new(92), VirValueId::new(94)]);
        let plan = entry
            .loop_predicate_parameters(&BTreeSet::from([VirValueId::new(90)]), &retained, &repacked)
            .unwrap();
        assert_eq!(plan, expected);
        let origin = entry.word_origin(VirValueId::new(92)).unwrap();
        let capture = logic::ScalarCapture::Word(origin);
        let mut head = mixed_frame(&entry, Form::SumAndFixed);
        head.inherit_loop_scalar_frame(&entry, &retained);
        head.define_value(
            VirValueId::new(94),
            *entry.value(VirValueId::new(94)).unwrap(),
        )
        .unwrap();
        for failure in 0..4 {
            let mut invalid = head.clone();
            match failure {
                0 => {
                    invalid.word_origins.remove(&VirValueId::new(92));
                }
                1 => {
                    invalid.set_word_origin(VirValueId::new(92), origin.add(1).unwrap());
                }
                2 => {
                    let interval = origin.initial_interval().unwrap();
                    invalid.values.insert(
                        VirValueId::new(92),
                        AbstractValue::U64(U64Interval::exact(interval.lower())),
                    );
                    invalid.values.insert(
                        VirValueId::new(94),
                        AbstractValue::U64(U64Interval::exact(interval.upper())),
                    );
                }
                _ => {
                    invalid.values.insert(
                        VirValueId::new(94),
                        AbstractValue::Bool(AbstractBool::Unknown),
                    );
                }
            }
            let before = invalid.clone();
            assert!(
                invalid
                    .abstract_loop_predicates_after_havoc_with_parameters(
                        &entry,
                        &BTreeSet::new(),
                        &repacked,
                        &plan,
                    )
                    .is_err()
            );
            assert_eq!(invalid, before);
        }
        head.abstract_loop_predicates_after_havoc_with_parameters(
            &entry,
            &BTreeSet::new(),
            &repacked,
            &plan,
        )
        .unwrap();
        head.narrow_word_interval(VirValueId::new(90), U64Interval::exact(2));
        head.narrow_word_interval(VirValueId::new(92), U64Interval::exact(3));
        head.narrow_word_interval(VirValueId::new(94), U64Interval::exact(3));
        // Only the complete fixed value is live, not its historical root(s).
        head.check_predicate_arguments(
            &def,
            PredicateHolder(0),
            &Form::SumAndFixed.arguments(90, 92),
        )
        .unwrap();
        let mut budget = LogicBudget::default();
        budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
        assert_eq!(
            head.read_predicate_capture(
                &head.predicates[&PredicateHolder(0)],
                capture,
                VirValueId::new(92),
                LogicType::Usize,
                &mut budget,
            ),
            Err(PredicateError::Budget)
        );
    }
}

#[test]
fn singleton_numeric_captures_select_induction_without_turning_equal_values_into_aliases() {
    for form in [Form::Offset, Form::Scale, Form::Subtract, Form::SumAndFixed] {
        for historical in [false, true] {
            for shape in 0..=if historical { 4 } else { 0 } {
                let fixed_shape = if historical && matches!(form, Form::SumAndFixed) {
                    2
                } else {
                    0
                };
                let (entry, def, mut plan) =
                    entry_with_ranges(form, historical, shape, fixed_shape, true);
                let mixed = matches!(form, Form::SumAndFixed);
                if mixed {
                    plan = mixed_plan(&entry);
                }
                assert!(plan.expression(PredicateHolder(0), 0).is_some());
                let repacked = BTreeSet::from([PredicateHolder(0)]);
                let mut head = if mixed {
                    mixed_frame(&entry, form)
                } else {
                    frame(&entry, form, true)
                };
                head.abstract_loop_predicates_after_havoc_with_parameters(
                    &entry,
                    &BTreeSet::new(),
                    &repacked,
                    &plan,
                )
                .unwrap();
                head.check_predicate_arguments(&def, PredicateHolder(0), &form.arguments(90, 92))
                    .unwrap();
                let mut exit = head.clone();
                exit.narrow_word_interval(VirValueId::new(90), U64Interval::exact(2));
                exit.check_predicate_arguments(&def, PredicateHolder(0), &form.arguments(90, 92))
                    .unwrap();
                let open = transfer_predicate(
                    &head,
                    &def,
                    7,
                    &PredicateEffect::WithArguments {
                        holder: PredicateHolder(0),
                        arguments: form.arguments(90, 92),
                        effect: Box::new(PredicateEffect::UnfoldNamed {
                            holder: PredicateHolder(0),
                            bindings: vec![binding(0)],
                            action: 60,
                        }),
                    },
                )
                .unwrap()
                .output;
                for stale in [false, true] {
                    let mut updated = open.clone();
                    updated
                        .define_value(
                            VirValueId::new(91),
                            AbstractValue::U64(U64Interval::new(2, 7).unwrap()),
                        )
                        .unwrap();
                    let closed = form.fold(&updated, &def, if stale { 90 } else { 91 }, 92);
                    let renames = [(0, 0), (1, 1), (91, 90), (92, 92)]
                        .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
                    let mut back = closed.project_cfg_edge(&renames);
                    for (a, b) in renames {
                        back.define_value(b, *closed.value(a).unwrap()).unwrap();
                    }
                    assert_eq!(
                        back.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan),
                        !stale
                    );
                }
                let mut lost = entry.clone();
                let same = *lost.value(VirValueId::new(90)).unwrap();
                *lost.value_mut(VirValueId::new(90)).unwrap() = same;
                lost.define_value(VirValueId::new(94), same).unwrap();
                for candidate in [90, 94] {
                    assert_eq!(
                        lost.loop_predicate_parameters(
                            &BTreeSet::from([VirValueId::new(candidate)]),
                            &BTreeSet::from([VirValueId::new(92)]),
                            &repacked,
                        )
                        .unwrap(),
                        LoopPredicateParameters::default()
                    );
                }
                let mut invalid = frame(&entry, form, false);
                if mixed {
                    invalid
                        .inherit_loop_scalar_frame(&entry, &BTreeSet::from([VirValueId::new(92)]));
                }
                let before = invalid.clone();
                assert!(
                    invalid
                        .abstract_loop_predicates_after_havoc_with_parameters(
                            &entry,
                            &BTreeSet::new(),
                            &repacked,
                            &plan,
                        )
                        .is_err()
                );
                assert_eq!(invalid, before);
            }
        }
    }
}

#[test]
fn known_entry_comparisons_select_numeric_induction_and_check_changed_truth() {
    let form = Form::Compare;
    let holder = PredicateHolder(0);
    let repacked = BTreeSet::from([holder]);
    for historical in [false, true] {
        for shape in 0..=if historical { 4 } else { 0 } {
            let (entry, def, plan) = entry_with_ranges(form, historical, shape, 0, true);
            let captured = &entry.predicates[&holder].logical_parameters[0].value;
            assert!(matches!(
                captured,
                LogicValue::BoolComparison {
                    word_type: WordType::Usize,
                    ..
                }
            ));
            assert_eq!(captured.known_boolean(), Some(shape == 0));
            let mut head = frame(&entry, form, true);
            head.abstract_loop_predicates_after_havoc_with_parameters(
                &entry,
                &BTreeSet::new(),
                &repacked,
                &plan,
            )
            .unwrap();
            assert_eq!(
                head.predicates[&holder].logical_parameters[0]
                    .value
                    .known_boolean(),
                None
            );
            assert!(matches!(
                head.predicates[&holder].logical_parameters[0].value,
                LogicValue::BoolComparison {
                    word_type: WordType::Usize,
                    ..
                }
            ));
            head.check_predicate_arguments(&def, holder, &form.arguments(90, 92))
                .unwrap();
            let open = transfer_predicate(
                &head,
                &def,
                7,
                &PredicateEffect::WithArguments {
                    holder,
                    arguments: form.arguments(90, 92),
                    effect: Box::new(PredicateEffect::UnfoldNamed {
                        holder,
                        bindings: vec![binding(0)],
                        action: 60,
                    }),
                },
            )
            .unwrap()
            .output;
            for truth in [false, true] {
                for stale in [false, true] {
                    let mut updated = open.clone();
                    for (id, value) in [(91, if truth { 0 } else { 7 }), (93, 1)] {
                        updated
                            .define_value(
                                VirValueId::new(id),
                                AbstractValue::U64(U64Interval::exact(value)),
                            )
                            .unwrap();
                    }
                    let closed = if stale {
                        form.fold(&updated, &def, 90, 92)
                    } else {
                        form.fold(&updated, &def, 91, 93)
                    };
                    let renames = [(0, 0), (1, 1), (91, 90), (93, 92)]
                        .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
                    let mut back = closed.project_cfg_edge(&renames);
                    for (a, b) in renames {
                        back.define_value(b, *closed.value(a).unwrap()).unwrap();
                    }
                    assert_eq!(
                        back.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan),
                        !stale
                    );
                }
                let mut exit = head.clone();
                exit.narrow_word_interval(
                    VirValueId::new(90),
                    U64Interval::exact(if truth { 0 } else { 7 }),
                );
                exit.narrow_word_interval(VirValueId::new(92), U64Interval::exact(1));
                exit.check_predicate_arguments(&def, holder, &form.arguments(90, 92))
                    .unwrap();
            }
            // Equal numeric replacement cannot supply the lost source identity.
            let mut lost = entry.clone();
            let same = *lost.value(VirValueId::new(90)).unwrap();
            *lost.value_mut(VirValueId::new(90)).unwrap() = same;
            assert_eq!(
                lost.loop_predicate_parameters(
                    &BTreeSet::from([VirValueId::new(90), VirValueId::new(92)]),
                    &BTreeSet::new(),
                    &repacked
                )
                .unwrap(),
                LoopPredicateParameters::default()
            );
        }
    }
}

#[test]
fn known_boolean_captures_select_induction_without_pinning_entry_truth() {
    let holder = PredicateHolder(0);
    let slot = VirValueId::new(90);
    let repacked = BTreeSet::from([holder]);
    for form in [Form::Boolean, Form::Negated] {
        for historical in [false, true] {
            let (entry, def, plan) = entry_with_ranges(form, historical, 0, 0, true);
            let expected = matches!(form, Form::Boolean);
            let value = &entry.predicates[&holder].logical_parameters[0].value;
            assert!(matches!(
                value,
                LogicValue::BoolAtom {
                    known: Some(true),
                    ..
                }
            ));
            assert_eq!(value.known_boolean(), Some(expected));
            let mut head = frame(&entry, form, true);
            head.abstract_loop_predicates_after_havoc_with_parameters(
                &entry,
                &BTreeSet::new(),
                &repacked,
                &plan,
            )
            .unwrap();
            assert!(matches!(
                head.predicates[&holder].logical_parameters[0].value,
                LogicValue::BoolAtom { known: None, .. }
            ));
            head.check_predicate_arguments(&def, holder, &form.arguments(90, 92))
                .unwrap();
            let open = transfer_predicate(
                &head,
                &def,
                7,
                &PredicateEffect::WithArguments {
                    holder,
                    arguments: form.arguments(90, 92),
                    effect: Box::new(PredicateEffect::UnfoldNamed {
                        holder,
                        bindings: vec![binding(0)],
                        action: 60,
                    }),
                },
            )
            .unwrap()
            .output;
            for truth in [false, true] {
                let actual = AbstractValue::Bool(if truth {
                    AbstractBool::True
                } else {
                    AbstractBool::False
                });
                let mut exit = head.clone();
                assert!(exit.narrow_bool_value(slot, truth));
                exit.check_predicate_arguments(&def, holder, &form.arguments(90, 92))
                    .unwrap();
                for stale in [false, true] {
                    let mut updated = open.clone();
                    updated.define_value(VirValueId::new(91), actual).unwrap();
                    let closed = form.fold(&updated, &def, if stale { 90 } else { 91 }, 92);
                    let renames = [(0, 0), (1, 1), (91, 90)]
                        .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)));
                    let mut back = closed.project_cfg_edge(&renames);
                    for (a, b) in renames {
                        back.define_value(b, *closed.value(a).unwrap()).unwrap();
                    }
                    assert_eq!(
                        back.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan),
                        !stale
                    );
                }
            }
            // A write invalidates the source even if it leaves the same value.
            let mut lost = entry.clone();
            *lost.value_mut(slot).unwrap() = AbstractValue::Bool(AbstractBool::True);
            lost.define_value(VirValueId::new(94), AbstractValue::Bool(AbstractBool::True))
                .unwrap();
            for candidate in [90, 94] {
                assert_eq!(
                    lost.loop_predicate_parameters(
                        &BTreeSet::from([VirValueId::new(candidate)]),
                        &BTreeSet::new(),
                        &repacked
                    )
                    .unwrap(),
                    LoopPredicateParameters::default()
                );
            }
            // Simulate inconsistent producer facts without invalidating identity.
            // Both the old capture and every surviving alias must be reconciled.
            let mut inconsistent = entry.clone();
            inconsistent
                .values
                .insert(slot, AbstractValue::Bool(AbstractBool::False));
            assert!(
                inconsistent
                    .check_predicate_arguments(&def, holder, &form.arguments(90, 92))
                    .is_err()
            );
            let mut copies = entry.project_cfg_edge(&[
                (slot, slot),
                (slot, VirValueId::new(94)),
                (VirValueId::new(0), VirValueId::new(0)),
                (VirValueId::new(1), VirValueId::new(1)),
            ]);
            for id in [90, 94] {
                copies
                    .define_value(VirValueId::new(id), AbstractValue::Bool(AbstractBool::True))
                    .unwrap();
            }
            for id in [0, 1] {
                copies
                    .define_value(
                        VirValueId::new(id),
                        *entry.value(VirValueId::new(id)).unwrap(),
                    )
                    .unwrap();
            }
            copies.values.insert(
                VirValueId::new(94),
                AbstractValue::Bool(AbstractBool::False),
            );
            assert!(
                copies
                    .check_predicate_arguments(&def, holder, &form.arguments(90, 92))
                    .is_err()
            );
            // Losing precision on the same immutable value does not erase truth.
            let mut widened = entry.clone();
            widened
                .values
                .insert(slot, AbstractValue::Bool(AbstractBool::Unknown));
            let literal = TypedLogicValue {
                ty: LogicType::Bool,
                value: LogicValue::Bool(Some(expected)),
            };
            assert_eq!(
                widened.predicate_argument_equality(
                    &widened.predicates[&holder],
                    entry.predicates[&holder].logical_parameters[0].clone(),
                    literal.clone(),
                    &mut LogicBudget::default()
                ),
                Ok(true)
            );
            let mut exhausted = LogicBudget::default();
            exhausted.charge(MAX_SUBSTITUTION_NODES).unwrap();
            assert_eq!(
                widened.predicate_argument_equality(
                    &widened.predicates[&holder],
                    entry.predicates[&holder].logical_parameters[0].clone(),
                    literal,
                    &mut exhausted
                ),
                Err(PredicateError::Budget)
            );
        }
    }
}
