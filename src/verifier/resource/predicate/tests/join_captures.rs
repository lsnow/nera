use super::*;
use crate::predicate_logic::*;

pub(super) fn captured(
    boolean: bool,
    input_id: u32,
    public: bool,
) -> (ResourceState, PredicateDefinition) {
    captured_with_value(
        boolean,
        input_id,
        public,
        if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::new(1, 6).unwrap())
        },
    )
}

pub(super) fn captured_with_value(
    boolean: bool,
    input_id: u32,
    public: bool,
    value: AbstractValue,
) -> (ResourceState, PredicateDefinition) {
    captured_with_history(boolean, input_id, public, value, false)
}

pub(super) fn captured_with_history(
    boolean: bool,
    input_id: u32,
    public: bool,
    value: AbstractValue,
    historical: bool,
) -> (ResourceState, PredicateDefinition) {
    let ty = if boolean {
        LogicType::Bool
    } else {
        LogicType::Usize
    };
    let mut def = logical_definition();
    def.logic.existentials[0].ty = ty;
    if boolean {
        def.logic.constraints.clear();
    }
    if public {
        def.logic.parameters.push(LogicParameter {
            position: 1,
            name: "fixed".into(),
            ty,
        });
    }
    let mut input = state();
    for id in [90, 91] {
        input.define_value(VirValueId::new(id), value).unwrap();
        if historical {
            let slot = VirValueId::new(id);
            if boolean {
                input.set_bool_origin(
                    slot,
                    BoolOrigin::Parameter {
                        function: crate::VirFunctionId::new(0),
                        value: slot,
                    },
                );
            } else {
                let AbstractValue::U64(interval) = value else {
                    panic!()
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
    let expression = LogicExpression {
        nodes: vec![LogicNode {
            ty,
            kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
        }],
        root: 0,
    };
    let effect = PredicateEffect::FoldWithWitnesses {
        holder: PredicateHolder(0),
        bindings: vec![binding(0)],
        witnesses: WitnessArguments {
            inputs: vec![(ty, WitnessInput::Scalar(VirValueId::new(input_id)))],
            arguments: if public {
                vec![expression.clone()]
            } else {
                vec![]
            },
            values: vec![(0, expression)],
        },
    };
    (
        transfer_predicate(&input, &def, 7, &effect).unwrap().output,
        def,
    )
}

// Exercise logical transport independently of the internal call calculus,
// whose result deliberately has no SSA carrier and cannot enter a CFG join.
// The existing real carrier stays unchanged; only captured scalar identities
// become foreign, exactly as the scope transport adapter specifies.
pub(super) fn foreign_capture(mut s: ResourceState) -> ResourceState {
    let resources = s.predicates[&PredicateHolder(0)].resources.clone();
    logic::freshen_instance(
        s.predicates.get_mut(&PredicateHolder(0)).unwrap(),
        &mut s.next_predicate_scope,
        &mut BTreeMap::new(),
        &mut LogicBudget::default(),
        &ScalarOriginTransport::default(),
        &[],
    )
    .unwrap();
    assert_eq!(s.predicates[&PredicateHolder(0)].resources, resources);
    assert_eq!(
        s.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    s
}

#[test]
fn distinct_local_and_foreign_captures_are_forgotten_not_identified() {
    for boolean in [false, true] {
        for foreign in [false, true] {
            let (mut a, def) = captured(boolean, 90, false);
            let (mut b, _) = captured(boolean, 91, false);
            if foreign {
                a = foreign_capture(a);
                b = foreign_capture(foreign_capture(b));
            }
            let before = (a.clone(), b.clone());
            assert_ne!(
                a.predicates[&PredicateHolder(0)].logical_witnesses,
                b.predicates[&PredicateHolder(0)].logical_witnesses
            );
            let scope = a.predicates[&PredicateHolder(0)].logic_scope.unwrap();
            assert!(
                logic::normalize_closed_scope(
                    &a.predicates[&PredicateHolder(0)],
                    scope,
                    &mut LogicBudget::default()
                )
                .is_err()
            );
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
                joined.next_predicate_scope,
                a.next_predicate_scope.max(b.next_predicate_scope)
            );
            assert!(
                joined.predicates[&PredicateHolder(0)]
                    .logical_local_aliases
                    .is_empty()
            );
            let opened = transfer_predicate(
                &joined,
                &def,
                7,
                &PredicateEffect::UnfoldNamed {
                    holder: PredicateHolder(0),
                    bindings: vec![binding(0)],
                    action: 31,
                },
            )
            .unwrap()
            .output;
            let expected = if boolean {
                AbstractValue::Bool(AbstractBool::Unknown)
            } else {
                AbstractValue::U64(U64Interval::new(0, 7).unwrap())
            };
            assert_eq!(
                opened.opened_predicate_snapshot(31, 0, 0),
                Some((expected, None))
            );
            assert_eq!((a, b), before);
        }
    }
}

#[test]
fn public_captures_cannot_be_hidden_even_when_their_ranges_are_equal() {
    for boolean in [false, true] {
        for foreign in [false, true] {
            let (mut a, _) = captured(boolean, 90, true);
            let (mut b, _) = captured(boolean, 91, true);
            if foreign {
                a = foreign_capture(a);
                b = foreign_capture(b);
            }
            let before = (a.clone(), b.clone());
            assert!(a.closed_predicate_checks().iter().all(|(_, valid)| *valid));
            assert!(b.closed_predicate_checks().iter().all(|(_, valid)| *valid));
            assert_eq!(a.join(&b), Err(ResourceJoinError::PredicateStateMismatch));
            assert_eq!(b.join(&a), Err(ResourceJoinError::PredicateStateMismatch));
            assert_eq!((a, b), before);
        }
    }
}

#[test]
fn forgetting_a_private_comparison_does_not_prove_its_truth_or_its_negation() {
    let mut def = logical_definition();
    def.logic.existentials[0].ty = LogicType::Bool;
    def.logic.constraints.clear();
    let make = |reverse| {
        let mut input = state();
        for id in [90, 91] {
            input
                .define_value(
                    VirValueId::new(id),
                    AbstractValue::U64(U64Interval::new(1, 6).unwrap()),
                )
                .unwrap();
        }
        let (left, right) = if reverse { (1, 0) } else { (0, 1) };
        let effect = PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses: WitnessArguments {
                inputs: [90, 91]
                    .into_iter()
                    .map(|id| (LogicType::Usize, WitnessInput::Scalar(VirValueId::new(id))))
                    .collect(),
                arguments: vec![],
                values: vec![(
                    0,
                    LogicExpression {
                        nodes: vec![
                            LogicNode {
                                ty: LogicType::Usize,
                                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                            },
                            LogicNode {
                                ty: LogicType::Usize,
                                kind: LogicNodeKind::Binder(LogicBinder::Parameter(1)),
                            },
                            LogicNode {
                                ty: LogicType::Bool,
                                kind: LogicNodeKind::LessEqual(left, right),
                            },
                        ],
                        root: 2,
                    },
                )],
            },
        };
        transfer_predicate(&input, &def, 7, &effect).unwrap().output
    };
    let joined = make(false).join(&make(true)).unwrap();
    let opened = transfer_predicate(
        &joined,
        &def,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 32,
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        opened.opened_predicate_snapshot(32, 0, 0),
        Some((AbstractValue::Bool(AbstractBool::Unknown), None))
    );
}
