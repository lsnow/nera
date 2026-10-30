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
fn boolean(state: &mut ResourceState, id: u32, known: AbstractBool) -> PredicateLogicValue {
    let id = VirValueId::new(id);
    state.define_value(id, AbstractValue::Bool(known)).unwrap();
    state.seed_parameter_origins(crate::VirFunctionId::new(0), &[id]);
    TypedLogicValue {
        ty: LogicType::Bool,
        value: LogicValue::BoolAtom {
            atom: ObservationAtom::HistoricalBool {
                scope: scope(),
                origin: state.bool_origin(id).unwrap(),
                local: true,
            },
            negated: false,
            known: None,
        },
    }
}
fn known(facts: &Facts, value: PredicateLogicValue) -> Option<bool> {
    facts
        .refine(value, &mut LogicBudget::default())
        .unwrap()
        .value
        .known_boolean()
}
fn comparison(
    state: &mut ResourceState,
) -> (
    PredicateLogicValue,
    PredicateLogicValue,
    PredicateLogicValue,
) {
    let mut values = Vec::new();
    for n in [0, 1] {
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
    let a = values.remove(0);
    let b = values.remove(0);
    let (LogicValue::Word(left), LogicValue::Word(right)) = (&a.value, &b.value) else {
        panic!()
    };
    let capture = TypedLogicValue {
        ty: LogicType::Bool,
        value: LogicValue::BoolComparison {
            word_type: WordType::Usize,
            comparison: WordComparison::LessEqual,
            left: left.clone(),
            right: right.clone(),
            negated: false,
        },
    };
    (a, b, capture)
}

#[test]
fn actual_relation_is_imported_without_erasing_comparison_or_mutating_resources() {
    let mut state = ResourceState::new();
    let (a, b, capture) = comparison(&mut state);
    state.learn_relations(
        &[DifferencePremise::Compare {
            comparison: RelationComparison::LessOrEqual,
            left: word(VirValueId::new(0)),
            right: word(VirValueId::new(1)),
        }],
        DifferenceLimits::default(),
    );
    let before = state.clone();
    let mut facts = Facts::new();
    let prepared = state
        .prepare_logic_fact_value(
            capture.clone(),
            None,
            &mut facts,
            &mut LogicBudget::default(),
        )
        .unwrap()
        .unwrap();
    assert_eq!(prepared, capture);
    assert_eq!(prepared.value.known_boolean(), None);
    assert_eq!(known(&facts, prepared), Some(true));
    assert_eq!(
        facts.entails(Comparison::LessEqual, &a, &b, &mut LogicBudget::default()),
        Ok(true)
    );
    assert_eq!(state, before);
}

#[test]
fn runtime_boolean_truth_keeps_history_and_negation_while_foreign_history_gets_no_fact() {
    let mut state = ResourceState::new();
    let mut capture = boolean(&mut state, 0, AbstractBool::True);
    let LogicValue::BoolAtom { negated, .. } = &mut capture.value else {
        panic!()
    };
    *negated = true;
    for local in [true, false] {
        let mut value = capture.clone();
        let LogicValue::BoolAtom {
            atom: ObservationAtom::HistoricalBool { local: flag, .. },
            ..
        } = &mut value.value
        else {
            panic!()
        };
        *flag = local;
        let mut facts = Facts::new();
        let prepared = state
            .prepare_logic_fact_value(value.clone(), None, &mut facts, &mut LogicBudget::default())
            .unwrap()
            .unwrap();
        assert_eq!(prepared, value);
        assert_eq!(known(&facts, prepared), local.then_some(false));
    }
}

#[test]
fn conflicting_boolean_copies_cannot_hide_below_a_true_or_or_publish_partial_facts() {
    let mut state = ResourceState::new();
    let first = boolean(&mut state, 0, AbstractBool::True);
    let conflict = boolean(&mut state, 1, AbstractBool::True);
    state
        .define_value(VirValueId::new(2), AbstractValue::Bool(AbstractBool::False))
        .unwrap();
    state.set_bool_origin(
        VirValueId::new(2),
        state.bool_origin(VirValueId::new(1)).unwrap(),
    );
    let nested = TypedLogicValue {
        ty: LogicType::Bool,
        value: LogicValue::BoolBinary {
            operation: BooleanOperation::Or,
            left: Box::new(first.value.clone()),
            right: Box::new(conflict.value),
            negated: false,
        },
    };
    let mut facts = Facts::new();
    assert_eq!(
        state.prepare_logic_fact_value(nested, None, &mut facts, &mut LogicBudget::default()),
        Err(PredicateError::UnprovedRepresentation)
    );
    assert_eq!(known(&facts, first), None);
}

#[test]
fn failed_observation_import_does_not_change_existing_facts() {
    let mut state = ResourceState::new();
    let capture = boolean(&mut state, 0, AbstractBool::True);
    let mut facts = Facts::new();
    facts
        .extend_booleans(&[(capture.clone(), false)], &mut LogicBudget::default())
        .unwrap();
    assert_eq!(
        state.prepare_logic_fact_value(
            capture.clone(),
            None,
            &mut facts,
            &mut LogicBudget::default()
        ),
        Err(PredicateError::UnprovedRepresentation)
    );
    assert_eq!(known(&facts, capture.clone()), Some(false));
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert_eq!(
        state.prepare_logic_fact_value(capture.clone(), None, &mut facts, &mut budget),
        Err(PredicateError::Budget)
    );
    assert_eq!(known(&facts, capture), Some(false));
}

#[test]
fn constraint_leaf_capture_preserves_the_original_numeric_expression() {
    let mut state = ResourceState::new();
    let (_, _, capture) = comparison(&mut state);
    state.learn_relations(
        &[DifferencePremise::Compare {
            comparison: RelationComparison::LessOrEqual,
            left: word(VirValueId::new(0)),
            right: word(VirValueId::new(1)),
        }],
        DifferenceLimits::default(),
    );
    let def = PredicateDefinition::new(
        crate::VirPredicateId::new(0),
        0,
        vec![PredicateResourceShape {
            size_bytes: 8,
            initialized: vec![],
        }],
    )
    .unwrap();
    let e = LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Bool,
            kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
        }],
        root: 0,
    };
    let leaves = state
        .capture_predicate_logic_leaves(
            &def,
            &[],
            scope(),
            std::slice::from_ref(&capture),
            &[],
            &e,
            &mut LogicBudget::default(),
        )
        .unwrap();
    assert_eq!(leaves, vec![(0, capture)]);
}

#[test]
fn inconsistent_word_sources_are_errors_not_unavailable_one_shot_observations() {
    let mut state = ResourceState::new();
    let (mut value, _, _) = comparison(&mut state);
    let LogicValue::Word(saved) = &mut value.value else {
        panic!()
    };
    saved.lower = 0;
    saved.upper = 0;
    state
        .define_value(
            VirValueId::new(2),
            AbstractValue::U64(U64Interval::exact(1)),
        )
        .unwrap();
    state.set_word_origin(
        VirValueId::new(2),
        state.word_origin(VirValueId::new(0)).unwrap(),
    );
    assert_eq!(
        state.prepare_logic_fact_value(value, None, &mut Facts::new(), &mut LogicBudget::default()),
        Err(PredicateError::UnprovedRepresentation)
    );
}

fn strict_state() -> (ResourceState, PredicateLogicValue) {
    let mut state = ResourceState::new();
    let (_, _, mut capture) = comparison(&mut state);
    let LogicValue::BoolComparison { left, .. } = &mut capture.value else {
        panic!()
    };
    *left = left.add(&AffineValue::exact(1)).unwrap();
    state.learn_relations(
        &[DifferencePremise::Compare {
            comparison: RelationComparison::LessThan,
            left: word(VirValueId::new(0)),
            right: word(VirValueId::new(1)),
        }],
        DifferenceLimits::default(),
    );
    (state, capture)
}

#[test]
fn captured_affine_comparison_uses_source_relations_without_a_slot_for_the_expression() {
    let (state, capture) = strict_state();
    let before = state.clone();
    let mut facts = Facts::new();
    let prepared = state
        .prepare_logic_fact_value(capture, None, &mut facts, &mut LogicBudget::default())
        .unwrap()
        .unwrap();
    assert_eq!(prepared.value.known_boolean(), None);
    assert_eq!(known(&facts, prepared.clone()), Some(true));
    let mut other_type = prepared;
    let LogicValue::BoolComparison { word_type, .. } = &mut other_type.value else {
        panic!()
    };
    *word_type = WordType::U64;
    assert_eq!(known(&facts, other_type), None);
    assert_eq!(state, before);
}

#[test]
fn affine_relation_projection_needs_each_actual_local_source() {
    let (state, capture) = strict_state();
    for missing in [false, true] {
        let mut state = state.clone();
        let mut value = capture.clone();
        if missing {
            state.word_origins.remove(&VirValueId::new(1));
        } else {
            let LogicValue::BoolComparison { left, right, .. } = &mut value.value else {
                panic!()
            };
            for operand in [left, right] {
                operand.terms = std::mem::take(&mut operand.terms)
                    .into_iter()
                    .map(|(mut atom, n)| {
                        if let ObservationAtom::Historical { local, .. } = &mut atom {
                            *local = false;
                        }
                        (atom, n)
                    })
                    .collect();
            }
        }
        let mut facts = Facts::new();
        let value = state
            .prepare_logic_fact_value(value, None, &mut facts, &mut LogicBudget::default())
            .unwrap()
            .unwrap();
        assert_eq!(known(&facts, value), None);
    }
}

#[test]
fn conflicting_source_copies_fail_atomically_even_without_a_whole_expression_alias() {
    let (mut state, capture) = strict_state();
    state
        .define_value(
            VirValueId::new(2),
            AbstractValue::U64(U64Interval::exact(100)),
        )
        .unwrap();
    state.set_word_origin(
        VirValueId::new(2),
        state.word_origin(VirValueId::new(0)).unwrap(),
    );
    let mut facts = Facts::new();
    assert_eq!(
        state.prepare_logic_fact_value(
            capture.clone(),
            None,
            &mut facts,
            &mut LogicBudget::default()
        ),
        Err(PredicateError::UnprovedRepresentation)
    );
    assert_eq!(known(&facts, capture), None);
}

#[test]
fn actual_composite_origin_ranges_refine_captures_without_inventing_component_slots() {
    let mut state = ResourceState::new();
    let (a, _, _) = comparison(&mut state);
    let origin = state
        .word_origin(VirValueId::new(0))
        .unwrap()
        .scale(2)
        .unwrap();
    state.word_origins.clear();
    state
        .define_value(
            VirValueId::new(2),
            AbstractValue::U64(U64Interval::new(6, 8).unwrap()),
        )
        .unwrap();
    state.set_word_origin(VirValueId::new(2), origin);
    let LogicValue::Word(a) = a.value else {
        panic!()
    };
    let target = TypedLogicValue {
        ty: LogicType::Usize,
        value: LogicValue::Word(a.scale(2).unwrap().add(&AffineValue::exact(1)).unwrap()),
    };
    let mut facts = Facts::new();
    let prepared = state
        .prepare_logic_fact_value(target, None, &mut facts, &mut LogicBudget::default())
        .unwrap()
        .unwrap();
    let refined = facts.refine(prepared, &mut LogicBudget::default()).unwrap();
    let LogicValue::Word(word) = refined.value else {
        panic!()
    };
    assert_eq!((word.lower, word.upper), (7, 9));
}

#[test]
fn later_batch_failure_cannot_publish_an_earlier_leaf_observation() {
    let mut state = ResourceState::new();
    let first = boolean(&mut state, 0, AbstractBool::True);
    let bad = TypedLogicValue {
        ty: LogicType::Bool,
        value: LogicValue::Word(AffineValue::exact(0)),
    };
    let mut facts = Facts::new();
    assert!(
        state
            .prepare_logic_fact_values(
                &[first.clone(), bad],
                None,
                &mut facts,
                &mut LogicBudget::default()
            )
            .is_err()
    );
    assert_eq!(known(&facts, first.clone()), None);
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES - 1).unwrap();
    assert_eq!(
        state.prepare_logic_fact_values(
            &[first.clone(), first.clone()],
            None,
            &mut facts,
            &mut budget
        ),
        Err(PredicateError::Budget)
    );
    assert_eq!(known(&facts, first), None);
}

#[test]
fn separate_numeric_inputs_use_only_matching_types_and_local_sources() {
    let mut state = ResourceState::new();
    let (x, y, _) = comparison(&mut state);
    state.learn_relations(
        &[DifferencePremise::Compare {
            comparison: RelationComparison::LessThan,
            left: word(VirValueId::new(0)),
            right: word(VirValueId::new(1)),
        }],
        DifferenceLimits::default(),
    );
    for mode in 0..3 {
        let mut value = y.clone();
        if mode == 1 {
            value.ty = LogicType::U64;
        }
        if mode == 2 {
            let LogicValue::Word(w) = &mut value.value else {
                panic!()
            };
            w.terms = std::mem::take(&mut w.terms)
                .into_iter()
                .map(|(mut atom, n)| {
                    if let ObservationAtom::Historical { local, .. } = &mut atom {
                        *local = false;
                    }
                    (atom, n)
                })
                .collect();
        }
        let mut facts = Facts::new();
        state
            .prepare_logic_fact_values(
                &[x.clone(), value.clone()],
                None,
                &mut facts,
                &mut LogicBudget::default(),
            )
            .unwrap();
        value.ty = LogicType::Usize;
        assert_eq!(
            facts.entails(Comparison::Less, &x, &value, &mut LogicBudget::default()),
            Ok(mode == 0)
        );
    }
}
