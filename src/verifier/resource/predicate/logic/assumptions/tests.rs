use super::*;
use crate::predicate_logic::facts::Comparison;
use crate::verifier::relation::{RelationComparison, difference::word};

fn scope() -> InstanceScope {
    InstanceScope {
        declaration: 0,
        instance: 1,
        opening: 0,
    }
}
fn inputs(strict: bool) -> (ResourceState, PredicateLogicValue, PredicateLogicValue) {
    let mut state = ResourceState::new();
    let mut values = Vec::new();
    for n in 0..2 {
        let id = VirValueId::new(n);
        state
            .define_value(id, AbstractValue::U64(U64Interval::new(0, 20).unwrap()))
            .unwrap();
        state.seed_parameter_origins(crate::VirFunctionId::new(0), &[id]);
        values.push(
            state
                .predicate_scalar_input(scope(), LogicType::Usize, id, &BTreeMap::new())
                .unwrap(),
        );
    }
    if strict {
        state.learn_relations(
            &[DifferencePremise::Compare {
                comparison: RelationComparison::LessThan,
                left: word(VirValueId::new(0)),
                right: word(VirValueId::new(1)),
            }],
            DifferenceLimits::default(),
        );
    }
    (state, values.remove(0), values.remove(0))
}
fn hidden(binder: u32) -> PredicateLogicValue {
    TypedLogicValue {
        ty: LogicType::Usize,
        value: LogicValue::Word(
            AffineValue::identified(
                ObservationAtom::Existential {
                    scope: scope(),
                    binder,
                },
                0,
                20,
            )
            .unwrap(),
        ),
    }
}
fn equality(a: PredicateLogicValue, b: PredicateLogicValue) -> PredicateConstraintFact {
    PredicateConstraintFact {
        expression: LogicExpression {
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
                    kind: LogicNodeKind::Equal(0, 1),
                },
            ],
            root: 2,
        },
        leaves: vec![(0, a), (1, b)],
    }
}

#[test]
fn actual_relations_bridge_separate_saved_clauses_and_opened_query_leaves() {
    let (state, x, y) = inputs(true);
    let a = hidden(0);
    let b = hidden(1);
    let snapshots = [
        equality(a.clone(), x.clone()),
        equality(b.clone(), y.clone()),
    ];
    let before = state.clone();
    let (facts, queries) = state
        .established_constraint_facts_with_inputs(
            &snapshots,
            &[a.clone(), b.clone()],
            Some(scope()),
            &mut LogicBudget::default(),
        )
        .unwrap();
    let [Some(left), Some(right)] = queries.as_slice() else {
        panic!()
    };
    assert_eq!(
        facts.entails(Comparison::Less, left, right, &mut LogicBudget::default()),
        Ok(true)
    );
    // One endpoint may occur only in the query, outside all saved clauses.
    let (facts, _) = state
        .established_constraint_facts_with_inputs(
            &snapshots[..1],
            &[a.clone(), y.clone()],
            Some(scope()),
            &mut LogicBudget::default(),
        )
        .unwrap();
    assert_eq!(
        facts.entails(Comparison::Less, &a, &y, &mut LogicBudget::default()),
        Ok(true)
    );
    assert_eq!(state, before);
}

#[test]
fn queries_only_supply_coordinates_not_unproved_guarantees() {
    let (state, x, y) = inputs(false);
    let (LogicValue::Word(left), LogicValue::Word(right)) = (&x.value, &y.value) else {
        panic!()
    };
    let candidate = TypedLogicValue {
        ty: LogicType::Bool,
        value: LogicValue::BoolComparison {
            word_type: WordType::Usize,
            comparison: WordComparison::LessEqual,
            left: left.clone(),
            right: right.clone(),
            negated: false,
        },
    };
    let (facts, _) = state
        .established_constraint_facts_with_inputs(
            &[],
            &[candidate.clone(), x.clone(), y.clone()],
            Some(scope()),
            &mut LogicBudget::default(),
        )
        .unwrap();
    assert_eq!(
        facts.entails(Comparison::LessEqual, &x, &y, &mut LogicBudget::default()),
        Ok(false)
    );
    assert_eq!(
        facts
            .refine(candidate, &mut LogicBudget::default())
            .unwrap()
            .value
            .known_boolean(),
        None
    );
}

#[test]
fn unavailable_memory_leaf_cannot_establish_a_saved_equality_or_endpoint() {
    let (state, _, y) = inputs(true);
    let memory = TypedLogicValue {
        ty: LogicType::Usize,
        value: LogicValue::Word(
            AffineValue::identified(
                ObservationAtom::Memory {
                    scope: scope(),
                    allocation: AbstractAllocationId::new(0),
                    offset: 0,
                    access: VirMemoryAccess::core_u64(),
                    time: ObservationTime::Current,
                    captured: false,
                },
                0,
                20,
            )
            .unwrap(),
        ),
    };
    let a = hidden(0);
    let (facts, _) = state
        .established_constraint_facts_with_inputs(
            &[equality(a.clone(), memory)],
            &[a.clone(), y.clone()],
            Some(scope()),
            &mut LogicBudget::default(),
        )
        .unwrap();
    assert_eq!(
        facts.entails(Comparison::Less, &a, &y, &mut LogicBudget::default()),
        Ok(false)
    );
}

#[test]
fn a_complete_composite_source_can_span_distinct_query_leaves() {
    let (mut state, x, y) = inputs(false);
    let mut origin = state.word_origin(VirValueId::new(0)).unwrap();
    origin.second = Some((state.word_origin(VirValueId::new(1)).unwrap().first, 1));
    state.word_origins.clear();
    state
        .define_value(
            VirValueId::new(2),
            AbstractValue::U64(U64Interval::exact(7)),
        )
        .unwrap();
    state.set_word_origin(VirValueId::new(2), origin);
    let (facts, _) = state
        .established_constraint_facts_with_inputs(
            &[],
            &[x.clone(), y.clone()],
            None,
            &mut LogicBudget::default(),
        )
        .unwrap();
    let (LogicValue::Word(x), LogicValue::Word(y)) = (x.value, y.value) else {
        panic!()
    };
    let sum = TypedLogicValue {
        ty: LogicType::Usize,
        value: LogicValue::Word(x.add(&y).unwrap()),
    };
    let seven = TypedLogicValue {
        ty: LogicType::Usize,
        value: LogicValue::Word(AffineValue::exact(7)),
    };
    assert_eq!(
        facts.entails(Comparison::Equal, &sum, &seven, &mut LogicBudget::default()),
        Ok(true)
    );
    assert_eq!(state.word_origins.len(), 1);
}

#[test]
fn saved_package_relations_define_new_expressions_without_runtime_hidden_slots() {
    let (state, x, y) = inputs(true);
    let a = hidden(0);
    let b = hidden(1);
    let saved = [equality(a.clone(), x), equality(b.clone(), y)];
    let values = [a, b];
    let arguments = WitnessArguments {
        inputs: (0..2)
            .map(|binder| {
                (
                    LogicType::Usize,
                    WitnessInput::Opened {
                        action: 1,
                        holder: 0,
                        binder,
                    },
                )
            })
            .collect(),
        arguments: vec![],
        values: vec![],
    };
    let expression = LogicExpression {
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
                ty: LogicType::Usize,
                kind: LogicNodeKind::Sub(1, 0),
            },
        ],
        root: 2,
    };
    let before = state.clone();
    for available in [&saved[..], &saved[..1], &[]] {
        // These inputs have already passed the holder/action adapter. Here the
        // context contains only prior guarantees, never new declaration facts.
        let context = ExpressionFacts::new(
            &state,
            scope(),
            available,
            &arguments,
            &values,
            &mut LogicBudget::default(),
        )
        .unwrap();
        let result = state.evaluate_predicate_expression(
            &expression,
            &values,
            &[],
            &context,
            &mut |_, _, _, _| Err(LogicError::Unbound),
            &mut |_, _| Err(LogicError::Unbound),
            true,
            &mut LogicBudget::default(),
        );
        if available.len() == 2 {
            let LogicValue::Word(word) = result.unwrap().value else {
                panic!()
            };
            assert_eq!((word.lower, word.upper), (1, 20));
        } else {
            assert_eq!(result, Err(PredicateError::UnprovedRepresentation));
        }
    }
    assert_eq!(state, before);
}
