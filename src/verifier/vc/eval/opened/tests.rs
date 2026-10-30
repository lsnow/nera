use super::*;
use crate::predicate_logic::*;
use crate::verifier::resource::*;
use crate::{VirMemoryAccess, VirPredicateId, VirRegionId, VirValueId};

fn logic() -> PredicateLogic<VirMemoryAccess> {
    PredicateLogic {
        existentials: ["low", "high"]
            .into_iter()
            .map(|name| Existential {
                name: name.into(),
                ty: LogicType::Usize,
                default: None,
            })
            .collect(),
        constraints: vec![
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
                        kind: LogicNodeKind::Binder(LogicBinder::Existential(1)),
                    },
                    LogicNode {
                        ty: LogicType::Usize,
                        kind: LogicNodeKind::Word(10),
                    },
                    LogicNode {
                        ty: LogicType::Bool,
                        kind: LogicNodeKind::LessEqual(0, 1),
                    },
                ],
                root: 2,
            },
        ],
        ..PredicateLogic::default()
    }
}

fn state() -> ResourceState {
    state_with_logic(logic())
}

fn state_with_logic(logic: PredicateLogic<VirMemoryAccess>) -> ResourceState {
    let definition = PredicateDefinition::from_vir(
        &crate::VirMemorySchema::core_u64(),
        &crate::VirPredicate {
            id: VirPredicateId::new(0),
            name: "Ready".into(),
            binders: vec![],
            origin: crate::VirOriginId::new(0),
            body: None,
            representation: Some(crate::PredicateRepresentation {
                logic,
                resources: vec![crate::PredicateStorage {
                    name: "p".into(),
                    pointee: VirMemoryAccess::core_u64(),
                    initialized: vec![(0, 8)],
                }],
                bounds: vec![],
                prefixes: vec![],
                witnesses: vec![],
            }),
        },
        7,
    )
    .unwrap();
    let allocation = AbstractAllocationId::new(0);
    let mut state = ResourceState::new();
    state
        .define_allocation(
            allocation,
            AbstractAllocation::new(VirRegionId::new(0), 8, 8).unwrap(),
        )
        .unwrap();
    state
        .define_value(
            VirValueId::new(0),
            AbstractValue::Pointer(
                AbstractPointer::new(
                    AbstractProvenance::Known(allocation),
                    U64Interval::exact(0),
                    GuaranteedAlignment::new(8).unwrap(),
                )
                .with_memory_access(Some(VirMemoryAccess::core_u64())),
            ),
        )
        .unwrap();
    state
        .define_value(
            VirValueId::new(1),
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(allocation),
                AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap()),
                AccessPermission::Write,
                FreeCapability::Yes,
            )),
        )
        .unwrap();
    let binding = PredicateBinding {
        pointer: VirValueId::new(0),
        permission: VirValueId::new(1),
    };
    state
        .import_predicate_interface_with_arguments(
            &definition,
            &[binding],
            PredicateHolder(0),
            &Default::default(),
            true,
        )
        .unwrap();
    transfer_predicate(
        &state,
        &definition,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding],
            action: 9,
        },
    )
    .unwrap()
    .output
}

#[test]
fn complete_vc_query_runs_before_interval_children_lose_hidden_relations() {
    let state = state();
    let before = state.clone();
    let function = super::super::tests::function();
    let mut arena = VcArena::default();
    let low = arena
        .intern(
            VcTerm::Snapshot(VirSpecSnapshot::Opened {
                function: function.id,
                action: 9,
                holder: 0,
                binder: 0,
            }),
            64,
        )
        .unwrap();
    let high = arena
        .intern(
            VcTerm::Snapshot(VirSpecSnapshot::Opened {
                function: function.id,
                action: 9,
                holder: 0,
                binder: 1,
            }),
            64,
        )
        .unwrap();
    let count = arena.intern(VcTerm::CheckedSub(high, low), 64).unwrap();
    let ten = arena.intern(VcTerm::U64(10), 64).unwrap();
    let root = arena.intern(VcTerm::LessOrEqual(count, ten), 64).unwrap();
    assert_eq!(
        evaluate_bool(
            &arena,
            root,
            &BTreeSet::new(),
            SnapshotValues::State(&state),
            &function,
            &mut VcQueryBudget::new(VcLimits::default()),
        ),
        Some(AbstractBool::True)
    );
    let maximum = arena.intern(VcTerm::U64(u64::MAX), 64).unwrap();
    let overflow = arena.intern(VcTerm::CheckedAdd(high, maximum), 64).unwrap();
    let cancelled = arena
        .intern(VcTerm::CheckedSub(overflow, maximum), 64)
        .unwrap();
    let invalid = arena.intern(VcTerm::Equal(cancelled, high), 64).unwrap();
    assert_ne!(
        evaluate_bool(
            &arena,
            invalid,
            &BTreeSet::new(),
            SnapshotValues::State(&state),
            &function,
            &mut VcQueryBudget::new(VcLimits::default()),
        ),
        Some(AbstractBool::True)
    );
    let stale = arena
        .intern(
            VcTerm::Snapshot(VirSpecSnapshot::Opened {
                function: function.id,
                action: 8,
                holder: 0,
                binder: 1,
            }),
            64,
        )
        .unwrap();
    let invisible = arena.intern(VcTerm::CheckedScale(stale, 0), 64).unwrap();
    let zero = arena.intern(VcTerm::U64(0), 64).unwrap();
    let bad_action = arena.intern(VcTerm::Equal(invisible, zero), 64).unwrap();
    assert_ne!(
        evaluate_bool(
            &arena,
            bad_action,
            &BTreeSet::new(),
            SnapshotValues::State(&state),
            &function,
            &mut VcQueryBudget::new(VcLimits::default()),
        ),
        Some(AbstractBool::True)
    );
    let mut budget = VcQueryBudget::new(VcLimits {
        max_query_steps: 16,
        ..VcLimits::default()
    });
    assert_ne!(
        evaluate_bool(
            &arena,
            root,
            &BTreeSet::new(),
            SnapshotValues::State(&state),
            &function,
            &mut budget,
        ),
        Some(AbstractBool::True)
    );
    assert!(budget.exhausted);
    assert_eq!(state, before);
}

#[test]
fn saved_boolean_formulas_are_queried_as_a_whole_without_choosing_a_disjunct() {
    let mut logic = logic();
    for name in ["left", "right"] {
        logic.existentials.push(Existential {
            name: name.into(),
            ty: LogicType::Bool,
            default: None,
        });
    }
    logic.constraints.push(LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(2)),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(3)),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Or(0, 1),
            },
        ],
        root: 2,
    });
    let missing_disjunction = state_with_logic({
        let mut missing = logic.clone();
        missing.constraints.pop();
        missing
    });
    logic.existentials.push(Existential {
        name: "count".into(),
        ty: LogicType::U64,
        default: None,
    });
    logic.constraints.push(LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::U64,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(4)),
            },
            LogicNode {
                ty: LogicType::U64,
                kind: LogicNodeKind::Word(10),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::LessEqual(0, 1),
            },
        ],
        root: 2,
    });
    let state = state_with_logic(logic);
    let before = state.clone();
    let function = super::super::tests::function();
    let mut arena = VcArena::default();
    let mut opened = |binder, action| {
        arena
            .intern(
                VcTerm::Snapshot(VirSpecSnapshot::Opened {
                    function: function.id,
                    action,
                    holder: 0,
                    binder,
                }),
                256,
            )
            .unwrap()
    };
    let low = opened(0, 9);
    let high = opened(1, 9);
    let left = opened(2, 9);
    let right = opened(3, 9);
    let stale = opened(3, 8);
    let count = opened(4, 9);
    let either = arena.intern(VcTerm::Or(vec![left, right]), 256).unwrap();
    let both = arena.intern(VcTerm::And(vec![left, right]), 256).unwrap();
    let neg_left = arena.intern(VcTerm::Not(left), 256).unwrap();
    let neg_right = arena.intern(VcTerm::Not(right), 256).unwrap();
    let neither = arena
        .intern(VcTerm::And(vec![neg_left, neg_right]), 256)
        .unwrap();
    let de_morgan = arena.intern(VcTerm::Not(neither), 256).unwrap();
    let width = arena.intern(VcTerm::CheckedSub(high, low), 256).unwrap();
    let ten = arena.intern(VcTerm::U64(10), 256).unwrap();
    let bound = arena.intern(VcTerm::LessOrEqual(width, ten), 256).unwrap();
    let mixed = arena.intern(VcTerm::And(vec![either, bound]), 256).unwrap();
    let truth = arena.intern(VcTerm::Bool(true), 256).unwrap();
    let equal = arena.intern(VcTerm::Equal(either, truth), 256).unwrap();
    let stale_branch = arena.intern(VcTerm::Or(vec![truth, stale]), 256).unwrap();
    let count_bound = arena.intern(VcTerm::LessOrEqual(count, ten), 256).unwrap();
    let both_domains = arena
        .intern(VcTerm::And(vec![bound, count_bound]), 256)
        .unwrap();
    let domain_query = arena
        .intern(VcTerm::Equal(both_domains, either), 256)
        .unwrap();
    let wrong_domain = arena.intern(VcTerm::Equal(low, count), 256).unwrap();
    let maximum = arena.intern(VcTerm::U64(u64::MAX), 256).unwrap();
    let overflow = arena
        .intern(VcTerm::CheckedAdd(high, maximum), 256)
        .unwrap();
    let zeroed = arena
        .intern(VcTerm::CheckedScale(overflow, 0), 256)
        .unwrap();
    let zero = arena.intern(VcTerm::U64(0), 256).unwrap();
    let cancelled = arena.intern(VcTerm::Equal(zeroed, zero), 256).unwrap();
    let bad_arithmetic = arena.intern(VcTerm::Equal(either, cancelled), 256).unwrap();
    for root in [either, de_morgan, mixed, equal, domain_query] {
        assert_eq!(
            evaluate_bool(
                &arena,
                root,
                &BTreeSet::new(),
                SnapshotValues::State(&state),
                &function,
                &mut VcQueryBudget::new(VcLimits::default())
            ),
            Some(AbstractBool::True)
        );
    }
    for root in [
        left,
        right,
        both,
        neither,
        stale_branch,
        wrong_domain,
        bad_arithmetic,
    ] {
        assert_ne!(
            evaluate_bool(
                &arena,
                root,
                &BTreeSet::new(),
                SnapshotValues::State(&state),
                &function,
                &mut VcQueryBudget::new(VcLimits::default())
            ),
            Some(AbstractBool::True)
        );
    }
    assert_ne!(
        evaluate_bool(
            &arena,
            either,
            &BTreeSet::new(),
            SnapshotValues::State(&missing_disjunction),
            &function,
            &mut VcQueryBudget::new(VcLimits::default())
        ),
        Some(AbstractBool::True)
    );
    let mut budget = VcQueryBudget::new(VcLimits {
        max_query_steps: 32,
        ..VcLimits::default()
    });
    assert_ne!(
        evaluate_bool(
            &arena,
            domain_query,
            &BTreeSet::new(),
            SnapshotValues::State(&state),
            &function,
            &mut budget
        ),
        Some(AbstractBool::True)
    );
    assert!(budget.exhausted);
    assert_eq!(state, before);
}

#[test]
fn whole_vc_queries_use_joint_guarantees_and_preserve_opening_checks() {
    let mut logic = logic();
    for name in ["a", "b"] {
        logic.existentials.push(Existential {
            name: name.into(),
            ty: LogicType::Bool,
            default: None,
        });
    }
    for negated in [false, true] {
        let mut nodes = vec![
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(2)),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(3)),
            },
        ];
        if negated {
            nodes.push(LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Not(1),
            });
        }
        let right = nodes.len() as u32 - 1;
        nodes.push(LogicNode {
            ty: LogicType::Bool,
            kind: LogicNodeKind::Or(0, right),
        });
        logic.constraints.push(LogicExpression {
            root: nodes.len() as u32 - 1,
            nodes,
        });
    }
    let state = state_with_logic(logic.clone());
    logic.constraints.pop();
    let weak = state_with_logic(logic);
    let before = state.clone();
    let function = super::super::tests::function();
    let mut arena = VcArena::default();
    let mut opened = |binder, action| {
        arena
            .intern(
                VcTerm::Snapshot(VirSpecSnapshot::Opened {
                    function: function.id,
                    action,
                    holder: 0,
                    binder,
                }),
                64,
            )
            .unwrap()
    };
    let a = opened(2, 9);
    let b = opened(3, 9);
    let stale = opened(2, 8);
    let truth = arena.intern(VcTerm::Bool(true), 64).unwrap();
    let equal = arena.intern(VcTerm::Equal(a, truth), 64).unwrap();
    let negated = arena.intern(VcTerm::Not(a), 64).unwrap();
    let hidden_stale = arena.intern(VcTerm::Or(vec![truth, stale]), 64).unwrap();
    for root in [a, equal] {
        assert_eq!(
            evaluate_bool(
                &arena,
                root,
                &BTreeSet::new(),
                SnapshotValues::State(&state),
                &function,
                &mut VcQueryBudget::new(VcLimits::default())
            ),
            Some(AbstractBool::True)
        );
        assert_ne!(
            evaluate_bool(
                &arena,
                root,
                &BTreeSet::new(),
                SnapshotValues::State(&weak),
                &function,
                &mut VcQueryBudget::new(VcLimits::default())
            ),
            Some(AbstractBool::True)
        );
    }
    for root in [b, negated, hidden_stale] {
        assert_ne!(
            evaluate_bool(
                &arena,
                root,
                &BTreeSet::new(),
                SnapshotValues::State(&state),
                &function,
                &mut VcQueryBudget::new(VcLimits::default())
            ),
            Some(AbstractBool::True)
        );
    }
    assert_eq!(state, before);
}

#[test]
fn joint_numeric_guarantees_define_arithmetic_before_interval_evaluation() {
    let joint = |complete: bool| {
        let mut logic = logic();
        logic.existentials.push(Existential {
            name: "flag".into(),
            ty: LogicType::Bool,
            default: None,
        });
        let order = logic.constraints.remove(0);
        for negative in [false, true].into_iter().take(if complete { 2 } else { 1 }) {
            let mut expression = order.clone();
            expression.nodes.push(LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(2)),
            });
            if negative {
                expression.nodes.push(LogicNode {
                    ty: LogicType::Bool,
                    kind: LogicNodeKind::Not(3),
                });
            }
            let flag = expression.nodes.len() as u32 - 1;
            expression.nodes.push(LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Or(flag, 2),
            });
            expression.root = expression.nodes.len() as u32 - 1;
            logic.constraints.push(expression);
        }
        state_with_logic(logic)
    };
    let state = joint(true);
    let weak = joint(false);
    let before = state.clone();
    let function = super::super::tests::function();
    let mut arena = VcArena::default();
    let mut opened = |binder| {
        arena
            .intern(
                VcTerm::Snapshot(VirSpecSnapshot::Opened {
                    function: function.id,
                    action: 9,
                    holder: 0,
                    binder,
                }),
                64,
            )
            .unwrap()
    };
    let low = opened(0);
    let high = opened(1);
    let flag = opened(2);
    let count = arena.intern(VcTerm::CheckedSub(high, low), 64).unwrap();
    let ten = arena.intern(VcTerm::U64(10), 64).unwrap();
    let root = arena.intern(VcTerm::LessOrEqual(count, ten), 64).unwrap();
    for (state, expected) in [(&state, true), (&weak, false)] {
        assert_eq!(
            evaluate_bool(
                &arena,
                root,
                &BTreeSet::new(),
                SnapshotValues::State(state),
                &function,
                &mut VcQueryBudget::new(VcLimits::default())
            ) == Some(AbstractBool::True),
            expected
        );
    }
    assert_ne!(
        evaluate_bool(
            &arena,
            flag,
            &BTreeSet::new(),
            SnapshotValues::State(&state),
            &function,
            &mut VcQueryBudget::new(VcLimits::default())
        ),
        Some(AbstractBool::True)
    );
    assert_eq!(state, before);
}

#[test]
fn numeric_model_consistency_proves_opened_flag_without_choosing_an_order() {
    let state_for = |complete: bool| {
        let mut logic = logic();
        logic.constraints.clear();
        logic.existentials.push(Existential {
            name: "flag".into(),
            ty: LogicType::Bool,
            default: None,
        });
        for reversed in [false, true].into_iter().take(if complete { 2 } else { 1 }) {
            logic.constraints.push(LogicExpression {
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
                        kind: if reversed {
                            LogicNodeKind::LessEqual(1, 0)
                        } else {
                            LogicNodeKind::Less(0, 1)
                        },
                    },
                    LogicNode {
                        ty: LogicType::Bool,
                        kind: LogicNodeKind::Binder(LogicBinder::Existential(2)),
                    },
                    LogicNode {
                        ty: LogicType::Bool,
                        kind: LogicNodeKind::Or(3, 2),
                    },
                ],
                root: 4,
            });
        }
        state_with_logic(logic)
    };
    let strong = state_for(true);
    let weak = state_for(false);
    let before = strong.clone();
    let function = super::super::tests::function();
    let mut arena = VcArena::default();
    let flag = arena
        .intern(
            VcTerm::Snapshot(VirSpecSnapshot::Opened {
                function: function.id,
                action: 9,
                holder: 0,
                binder: 2,
            }),
            64,
        )
        .unwrap();
    for (state, expected) in [(&strong, true), (&weak, false)] {
        assert_eq!(
            evaluate_bool(
                &arena,
                flag,
                &BTreeSet::new(),
                SnapshotValues::State(state),
                &function,
                &mut VcQueryBudget::new(VcLimits::default())
            ) == Some(AbstractBool::True),
            expected
        );
    }
    assert_eq!(strong, before);
}
