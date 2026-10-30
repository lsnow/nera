use super::*;
use crate::verifier::relation::difference::word;

fn setup(
    history: bool,
    ordered: bool,
) -> (
    ResourceState,
    WitnessArguments<VirMemoryAccess, VirValueId>,
    Vec<PredicateLogicValue>,
    InstanceScope,
) {
    let mut state = ResourceState::new();
    let ids = [VirValueId::new(0), VirValueId::new(1)];
    for id in ids {
        state
            .define_value(id, AbstractValue::U64(U64Interval::new(0, 10).unwrap()))
            .unwrap();
    }
    if history {
        state.seed_parameter_origins(crate::VirFunctionId::new(0), &ids);
    }
    if ordered {
        state.learn_relations(
            &[DifferencePremise::Bound {
                left: word(ids[0]),
                right: word(ids[1]),
                bound: 0,
            }],
            DifferenceLimits::default(),
        );
    }
    let scope = InstanceScope {
        declaration: 0,
        instance: 0,
        opening: 0,
    };
    let inputs = ids
        .iter()
        .map(|id| {
            state
                .predicate_scalar_input(scope, LogicType::Usize, *id, &BTreeMap::new())
                .unwrap()
        })
        .collect();
    let args = WitnessArguments {
        inputs: ids
            .iter()
            .map(|id| (LogicType::Usize, WitnessInput::Scalar(*id)))
            .collect(),
        arguments: vec![],
        values: vec![],
    };
    (state, args, inputs, scope)
}

fn difference(reverse: bool) -> LogicExpression<VirMemoryAccess> {
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
                ty: LogicType::Usize,
                kind: if reverse {
                    LogicNodeKind::Sub(0, 1)
                } else {
                    LogicNodeKind::Sub(1, 0)
                },
            },
        ],
        root: 2,
    }
}

#[test]
fn actual_relations_check_new_arithmetic_with_or_without_retained_history() {
    for history in [false, true] {
        for ordered in [false, true] {
            let (state, args, inputs, scope) = setup(history, ordered);
            let before = state.clone();
            let mut budget = LogicBudget::default();
            let context =
                ExpressionFacts::new(&state, scope, &[], &args, &inputs, &mut budget).unwrap();
            for reverse in [false, true] {
                let result = state.evaluate_predicate_expression(
                    &difference(reverse),
                    &inputs,
                    &[],
                    &context,
                    &mut |_, _, _, _| Err(LogicError::Unbound),
                    &mut |_, _| Err(LogicError::Unbound),
                    true,
                    &mut LogicBudget::default(),
                );
                if ordered && !reverse {
                    let LogicValue::Word(value) = result.unwrap().value else {
                        panic!()
                    };
                    assert_eq!((value.lower, value.upper), (0, 10));
                    assert_eq!(value.terms.len(), 2);
                } else {
                    assert_eq!(result, Err(PredicateError::UnprovedRepresentation));
                }
            }
            assert_eq!(state, before);
        }
    }
}

#[test]
fn prepared_arithmetic_context_cannot_cross_resource_states() {
    let (state, args, inputs, scope) = setup(true, true);
    let other = state.clone();
    let context = ExpressionFacts::new(
        &state,
        scope,
        &[],
        &args,
        &inputs,
        &mut LogicBudget::default(),
    )
    .unwrap();
    let evaluate = |state: &ResourceState| {
        state.evaluate_predicate_expression(
            &difference(false),
            &inputs,
            &[],
            &context,
            &mut |_, _, _, _| Err(LogicError::Unbound),
            &mut |_, _| Err(LogicError::Unbound),
            true,
            &mut LogicBudget::default(),
        )
    };
    assert!(evaluate(&state).is_ok());
    // Even an equal clone is another invocation: its facts must be qualified
    // independently instead of inheriting a previously prepared catalog.
    assert_eq!(evaluate(&other), Err(PredicateError::InvalidBinding));
    assert!(evaluate(&state).is_ok());
    assert_eq!(state, other);
}

#[test]
fn cancellation_cannot_hide_an_overflowing_intermediate() {
    let (state, args, inputs, scope) = setup(true, true);
    let context = ExpressionFacts::new(
        &state,
        scope,
        &[],
        &args,
        &inputs,
        &mut LogicBudget::default(),
    )
    .unwrap();
    let expression = LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(1)),
            },
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Word(u64::MAX),
            },
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Add(0, 1),
            },
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Sub(2, 1),
            },
        ],
        root: 3,
    };
    assert_eq!(
        state.evaluate_predicate_expression(
            &expression,
            &inputs,
            &[],
            &context,
            &mut |_, _, _, _| Err(LogicError::Unbound),
            &mut |_, _| Err(LogicError::Unbound),
            true,
            &mut LogicBudget::default(),
        ),
        Err(PredicateError::UnprovedRepresentation)
    );
}

#[test]
fn absent_observations_and_budget_failure_leave_state_unchanged() {
    let (state, args, inputs, scope) = setup(true, true);
    let before = state.clone();
    let context = ExpressionFacts::new(
        &state,
        scope,
        &[],
        &args,
        &inputs,
        &mut LogicBudget::default(),
    )
    .unwrap();
    let mut expression = difference(false);
    expression.nodes[0].kind = LogicNodeKind::Observe {
        resource: 0,
        offset: 0,
        access: VirMemoryAccess::core_u64(),
        time: ObservationTime::Current,
    };
    assert!(
        state
            .evaluate_predicate_expression(
                &expression,
                &inputs,
                &[],
                &context,
                &mut |_, _, _, _| Err(LogicError::Unbound),
                &mut |_, _| Err(LogicError::Unbound),
                true,
                &mut LogicBudget::default(),
            )
            .is_err()
    );
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES - 1).unwrap();
    assert_eq!(
        state.evaluate_predicate_expression(
            &difference(false),
            &inputs,
            &[],
            &context,
            &mut |_, _, _, _| Err(LogicError::Unbound),
            &mut |_, _| Err(LogicError::Unbound),
            true,
            &mut budget,
        ),
        Err(PredicateError::Budget)
    );
    assert_eq!(state, before);
}
