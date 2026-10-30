use super::*;
use crate::verifier::relation::{RelationComparison, difference::word};

fn operand(holder: u32) -> OpenedSpecOperand {
    OpenedSpecOperand::Opened {
        action: 40 + holder,
        holder,
        binder: 0,
    }
}

fn packages(
    ty: LogicType<VirMemoryAccess>,
    relation: Option<RelationComparison>,
    shared_input: bool,
) -> (ResourceState, PredicateDefinition) {
    let mut definition = PredicateDefinition::new(
        VirPredicateId::new(0),
        7,
        vec![PredicateResourceShape {
            size_bytes: 8,
            initialized: vec![ByteRange::new(0, 8).unwrap()],
        }],
    )
    .unwrap();
    definition.logic.parameters.push(LogicParameter {
        name: "value".into(),
        position: 1,
        ty,
    });
    definition.logic.existentials.push(Existential {
        name: "saved".into(),
        ty,
        default: None,
    });
    definition.logic.constraints.push(LogicExpression {
        nodes: vec![
            LogicNode {
                ty,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
            },
            LogicNode {
                ty,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Equal(0, 1),
            },
        ],
        root: 2,
    });
    let mut state = ResourceState::new();
    let inputs = [VirValueId::new(10), VirValueId::new(11)];
    for id in inputs {
        state
            .define_value(
                id,
                if ty == LogicType::Bool {
                    AbstractValue::Bool(AbstractBool::Unknown)
                } else {
                    AbstractValue::U64(U64Interval::new(2, 20).unwrap())
                },
            )
            .unwrap();
    }
    state.seed_parameter_origins(crate::VirFunctionId::new(0), &inputs);
    if let Some(comparison) = relation {
        state.learn_relations(
            &[DifferencePremise::Compare {
                comparison,
                left: word(inputs[0]),
                right: word(inputs[1]),
            }],
            DifferenceLimits::default(),
        );
    }
    for i in 0..2u32 {
        let id = AbstractAllocationId::new(i);
        let mut allocation = AbstractAllocation::new(VirRegionId::new(0), 8, 8).unwrap();
        let bytes = ByteRange::new(0, 8).unwrap();
        allocation.mark_initialized(bytes).unwrap();
        allocation.mark_valid(bytes).unwrap();
        state.define_allocation(id, allocation).unwrap();
        let binding = PredicateBinding {
            pointer: VirValueId::new(2 * i),
            permission: VirValueId::new(2 * i + 1),
        };
        state
            .define_value(
                binding.pointer,
                AbstractValue::Pointer(AbstractPointer::new(
                    AbstractProvenance::Known(id),
                    U64Interval::exact(0),
                    GuaranteedAlignment::new(8).unwrap(),
                )),
            )
            .unwrap();
        state
            .define_value(
                binding.permission,
                AbstractValue::Permission(AbstractPermission::new(
                    AbstractProvenance::Known(id),
                    AbstractByteRange::Exact(bytes),
                    AccessPermission::Write,
                    FreeCapability::Yes,
                )),
            )
            .unwrap();
        let actuals = WitnessArguments {
            inputs: vec![(
                ty,
                WitnessInput::Scalar(inputs[if shared_input { 0 } else { i as usize }]),
            )],
            arguments: vec![LogicExpression {
                nodes: vec![LogicNode {
                    ty,
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                }],
                root: 0,
            }],
            values: vec![],
        };
        state
            .import_predicate_interface_with_arguments(
                &definition,
                &[binding],
                PredicateHolder(i),
                &actuals,
                true,
            )
            .unwrap();
    }
    for i in 0..2u32 {
        state = transfer_predicate(
            &state,
            &definition,
            7,
            &PredicateEffect::UnfoldNamed {
                holder: PredicateHolder(i),
                bindings: vec![PredicateBinding {
                    pointer: VirValueId::new(2 * i),
                    permission: VirValueId::new(2 * i + 1),
                }],
                action: 40 + i,
            },
        )
        .unwrap()
        .output;
    }
    (state, definition)
}

#[test]
fn two_opened_packages_compose_equalities_and_current_relations() {
    for ty in [LogicType::U64, LogicType::Usize] {
        let (state, _) = packages(ty, Some(RelationComparison::LessThan), false);
        let before = state.clone();
        assert_ne!(
            state.predicates[&PredicateHolder(0)].logic_scope,
            state.predicates[&PredicateHolder(1)].logic_scope
        );
        for (comparison, a, b, expected) in [
            (OpenedSpecComparison::Less, 0, 1, true),
            (OpenedSpecComparison::LessEqual, 0, 1, true),
            (OpenedSpecComparison::Less, 1, 0, false),
            (OpenedSpecComparison::Equal, 0, 1, false),
        ] {
            assert_eq!(
                state.prove_opened_spec_comparison(comparison, operand(a), operand(b)),
                Ok(expected)
            );
        }
        assert_eq!(state, before);
    }
}

#[test]
fn shared_numeric_and_boolean_origins_connect_distinct_existentials() {
    for ty in [LogicType::U64, LogicType::Usize, LogicType::Bool] {
        for shared in [false, true] {
            let (state, _) = packages(ty, None, shared);
            assert_eq!(
                state.prove_opened_spec_comparison(
                    OpenedSpecComparison::Equal,
                    operand(0),
                    operand(1),
                ),
                Ok(shared)
            );
        }
    }
}

#[test]
fn queries_require_both_guarantees_and_do_not_equate_equal_ranges() {
    let (state, _) = packages(LogicType::Usize, Some(RelationComparison::LessThan), false);
    for holder in [0, 1] {
        let mut missing = state.clone();
        missing
            .predicates
            .get_mut(&PredicateHolder(holder))
            .unwrap()
            .logical_facts
            .clear();
        assert_eq!(
            missing.prove_opened_spec_comparison(
                OpenedSpecComparison::Less,
                operand(0),
                operand(1)
            ),
            Ok(false)
        );
    }
    let (weak, _) = packages(
        LogicType::Usize,
        Some(RelationComparison::LessOrEqual),
        false,
    );
    assert_eq!(
        weak.prove_opened_spec_comparison(OpenedSpecComparison::Less, operand(0), operand(1)),
        Ok(false)
    );
}

#[test]
fn foreign_histories_do_not_reuse_current_frame_relations() {
    let (mut state, _) = packages(LogicType::Usize, Some(RelationComparison::LessThan), false);
    for instance in state.predicates.values_mut() {
        for value in instance
            .logical_parameters
            .iter_mut()
            .chain(instance.logical_witnesses.iter_mut())
            .chain(
                instance
                    .logical_facts
                    .iter_mut()
                    .flat_map(|fact| fact.leaves.iter_mut().map(|(_, value)| value)),
            )
        {
            for leaf in value
                .value
                .capture_leaves_mut(&mut LogicBudget::default())
                .unwrap()
            {
                if let LogicValue::Word(word) = leaf {
                    word.terms = std::mem::take(&mut word.terms)
                        .into_iter()
                        .map(|(mut atom, coefficient)| {
                            if let ObservationAtom::Historical { local, .. } = &mut atom {
                                *local = false;
                            }
                            (atom, coefficient)
                        })
                        .collect();
                }
            }
        }
    }
    assert_eq!(
        state.prove_opened_spec_comparison(OpenedSpecComparison::Less, operand(0), operand(1)),
        Ok(false)
    );
}

#[test]
fn all_opening_actions_binders_and_types_are_checked_before_proving() {
    let (state, _) = packages(LogicType::Usize, None, true);
    for holder in [0, 1] {
        for mutation in 0..5 {
            let mut invalid = state.clone();
            let instance = invalid
                .predicates
                .get_mut(&PredicateHolder(holder))
                .unwrap();
            match mutation {
                0 => instance.folded = true,
                1 => instance.opening_action = Some(100),
                2 => instance.logical_witnesses.clear(),
                3 => instance.logical_witnesses[0].ty = LogicType::U64,
                4 => instance.logic_scope = None,
                _ => unreachable!(),
            }
            let before = invalid.clone();
            assert_eq!(
                invalid.prove_opened_spec_comparison(
                    OpenedSpecComparison::Equal,
                    operand(0),
                    operand(1)
                ),
                Err(PredicateError::InvalidBinding)
            );
            assert_eq!(invalid, before);
        }
    }
    let mut missing = state;
    missing.predicates.remove(&PredicateHolder(1));
    assert_eq!(
        missing.prove_opened_spec_comparison(OpenedSpecComparison::Equal, operand(0), operand(1)),
        Err(PredicateError::MissingHolder)
    );
}

#[test]
fn refolding_and_reopening_invalidates_the_old_query_action() {
    let (state, definition) = packages(LogicType::Usize, Some(RelationComparison::LessThan), false);
    let scalar = |index| LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Usize,
            kind: LogicNodeKind::Binder(LogicBinder::Parameter(index)),
        }],
        root: 0,
    };
    let bindings = vec![PredicateBinding {
        pointer: VirValueId::new(0),
        permission: VirValueId::new(1),
    }];
    let sealed = transfer_predicate(
        &state,
        &definition,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: bindings.clone(),
            witnesses: WitnessArguments {
                inputs: vec![
                    (LogicType::Usize, WitnessInput::Scalar(VirValueId::new(10))),
                    (
                        LogicType::Usize,
                        WitnessInput::Opened {
                            action: 40,
                            holder: 0,
                            binder: 0,
                        },
                    ),
                ],
                arguments: vec![scalar(0)],
                values: vec![(0, scalar(1))],
            },
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        sealed.prove_opened_spec_comparison(OpenedSpecComparison::Less, operand(0), operand(1)),
        Err(PredicateError::InvalidBinding)
    );
    let reopened = transfer_predicate(
        &sealed,
        &definition,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings,
            action: 80,
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        reopened.prove_opened_spec_comparison(OpenedSpecComparison::Less, operand(0), operand(1)),
        Err(PredicateError::InvalidBinding)
    );
    assert_eq!(
        reopened.prove_opened_spec_comparison(
            OpenedSpecComparison::Less,
            OpenedSpecOperand::Opened {
                action: 80,
                holder: 0,
                binder: 0,
            },
            operand(1),
        ),
        Ok(true)
    );
}

#[test]
fn composed_queries_share_a_bounded_budget_without_changing_packages() {
    let (state, _) = packages(LogicType::Usize, None, true);
    let before = state.clone();
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES - 1).unwrap();
    assert_eq!(
        state.prove_opened_spec_comparison_with_budget(
            OpenedSpecComparison::Equal,
            operand(0),
            operand(1),
            &mut budget,
        ),
        Err(PredicateError::Budget)
    );
    let mut oversized = state.clone();
    for instance in oversized.predicates.values_mut() {
        instance.logical_facts = vec![instance.logical_facts[0].clone(); MAX_CONSTRAINTS];
    }
    assert_eq!(
        oversized.prove_opened_spec_comparison(OpenedSpecComparison::Equal, operand(0), operand(1)),
        Err(PredicateError::Budget)
    );
    assert_eq!(state, before);
}

#[test]
fn arithmetic_queries_use_saved_cross_package_relations_without_new_scalar_slots() {
    use crate::predicate_logic::query::Term::*;
    for ty in [LogicType::Usize, LogicType::U64] {
        let (state, _) = packages(ty, Some(RelationComparison::LessThan), false);
        let before = state.clone();
        let terms = [
            Operand(operand(0)),
            Operand(operand(1)),
            Operand(OpenedSpecOperand::Word(1)),
            Add(0, 2),
            Sub(1, 0),
            Scale(4, 2),
            Operand(OpenedSpecOperand::Word(2)),
        ];
        for (left, right) in [(3, 1), (2, 4), (6, 5)] {
            assert_eq!(
                state
                    .prove_opened_spec_query(OpenedSpecComparison::LessEqual, &terms, left, right,),
                Ok(true)
            );
        }
        assert_eq!(
            state.prove_opened_spec_query(OpenedSpecComparison::LessEqual, &terms, 1, 0,),
            Ok(false)
        );
        assert_eq!(state, before);
    }
}

#[test]
fn query_arithmetic_checks_cancelled_and_zero_scaled_intermediates() {
    use crate::predicate_logic::query::Term::*;
    let (state, _) = packages(LogicType::Usize, Some(RelationComparison::LessThan), false);
    let terms = [
        Operand(operand(0)),
        Operand(operand(1)),
        Operand(OpenedSpecOperand::Word(u64::MAX)),
        Add(0, 2),
        Sub(3, 2),
        Scale(3, 0),
        Operand(OpenedSpecOperand::Word(0)),
    ];
    for (left, right) in [(0, 4), (5, 6)] {
        assert_eq!(
            state.prove_opened_spec_query(OpenedSpecComparison::Equal, &terms, left, right,),
            Ok(false)
        );
    }
    let reversed = [Operand(operand(0)), Operand(operand(1)), Sub(0, 1)];
    assert_eq!(
        state.prove_opened_spec_query(OpenedSpecComparison::Equal, &reversed, 2, 2,),
        Ok(false)
    );
}

#[test]
fn query_dags_reject_forward_edges_depth_budget_types_and_stale_actions() {
    use crate::predicate_logic::query::Term::*;
    let (state, _) = packages(LogicType::Usize, None, true);
    assert_eq!(
        state.prove_opened_spec_query(OpenedSpecComparison::Equal, &[Add(0, 0)], 0, 0,),
        Err(PredicateError::InvalidBinding)
    );
    assert_eq!(
        state.prove_opened_spec_query(OpenedSpecComparison::Equal, &[Operand(operand(0))], 0, 1,),
        Err(PredicateError::InvalidBinding)
    );
    let mut deep = vec![Operand(operand(0))];
    for i in 0..MAX_EXPRESSION_DEPTH as u32 {
        deep.push(Scale(i, 1));
    }
    assert_eq!(
        state
            .prove_opened_spec_query(OpenedSpecComparison::Equal, &deep, 0, deep.len() as u32 - 1,),
        Err(PredicateError::Budget)
    );
    let stale = [
        Operand(operand(0)),
        Operand(OpenedSpecOperand::Opened {
            action: 99,
            holder: 1,
            binder: 0,
        }),
        Scale(1, 0),
    ];
    assert_eq!(
        state.prove_opened_spec_query(OpenedSpecComparison::Equal, &stale, 0, 0,),
        Err(PredicateError::InvalidBinding)
    );
    let (booleans, _) = packages(LogicType::Bool, None, true);
    assert!(
        booleans
            .prove_opened_spec_query(
                OpenedSpecComparison::Equal,
                &[Operand(operand(0)), Operand(operand(1)), Sub(0, 1)],
                2,
                2,
            )
            .is_err()
    );
}
