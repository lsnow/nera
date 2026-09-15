use super::*;
use crate::{ByteSpan, SpannedVirInstruction, VirInstruction, VirType, VirValue};

fn id(n: u32) -> VirValueId {
    VirValueId::new(n)
}
fn define(state: &mut ResourceState, n: u32, value: AbstractValue) {
    state.define_value(id(n), value).unwrap();
}

#[test]
fn parallel_swap_and_repeated_drop_flags_preserve_whole_cases() {
    for consumed in [false, true] {
        let mut state = ResourceState::new();
        define(
            &mut state,
            0,
            AbstractValue::U64(U64Interval::exact(if consumed { 1 } else { 0 })),
        );
        define(
            &mut state,
            1,
            AbstractValue::Bool(if consumed {
                AbstractBool::False
            } else {
                AbstractBool::True
            }),
        );
        let allocation = AbstractAllocationId::new(0);
        let mut memory = AbstractAllocation::new(VirRegionId::new(0), 8, 8).unwrap();
        let mut permission = AbstractPermission::new(
            AbstractProvenance::Known(allocation),
            AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap()),
            AccessPermission::Write,
            FreeCapability::Yes,
        );
        if consumed {
            memory.mark_dead();
            permission.mark_consumed();
        }
        state.define_allocation(allocation, memory).unwrap();
        define(&mut state, 2, AbstractValue::Permission(permission));
        let renames = [
            (id(0), id(1)),
            (id(1), id(0)),
            (id(1), id(3)),
            (id(2), id(4)),
        ];
        let projected = state.project_cfg_case(&renames).unwrap();
        assert_eq!(projected.value(id(1)), state.value(id(0)));
        assert_eq!(projected.value(id(0)), state.value(id(1)));
        assert_eq!(projected.value(id(4)), state.value(id(2)));
        assert_eq!(projected.allocations(), state.allocations());
        for target in [0, 3] {
            assert!(
                projected
                    .path_condition()
                    .implies(PathFact::boolean(id(target), !consumed))
            );
        }
        let reversed: Vec<_> = renames.into_iter().rev().collect();
        assert_eq!(projected, state.project_cfg_case(&reversed).unwrap());
    }
}

#[test]
fn increment_projects_the_new_value_not_the_old_guard_and_respects_wrap() {
    for (lower, upper) in [(0, 0), (0, 1), (u64::MAX, u64::MAX)] {
        let mut state = ResourceState::new();
        define(
            &mut state,
            0,
            AbstractValue::U64(U64Interval::new(lower, upper).unwrap()),
        );
        define(&mut state, 1, AbstractValue::U64(U64Interval::exact(1)));
        state.set_word_expression(id(0), AffineExpression::identity(id(0)));
        if upper <= 1 {
            state.conjoin_path_fact(PathFact::comparison(
                VirIntegerPredicate::LessOrEqual,
                id(0),
                id(1),
            ));
        }
        let transfer = crate::verifier::transfer_instruction(
            &state,
            &SpannedVirInstruction {
                instruction: VirInstruction::WordAdd {
                    result: VirValue {
                        id: id(2),
                        ty: VirType::U64,
                    },
                    left: id(0),
                    right: id(1),
                },
                source_span: ByteSpan::new(0, 1).unwrap(),
            },
        )
        .unwrap();
        let next = transfer
            .state()
            .project_cfg_case(&[(id(2), id(0)), (id(2), id(3))])
            .unwrap();
        let expected = if lower == u64::MAX {
            U64Interval::exact(0)
        } else {
            U64Interval::new(lower + 1, upper + 1).unwrap()
        };
        assert_eq!(next.value(id(0)), Some(&AbstractValue::U64(expected)));
        assert_eq!(next.value(id(3)), next.value(id(0)));
        assert_eq!(next.path_condition(), &PathCondition::empty());
        assert!(next.relations().bounds().all(|b| {
            [b.left, b.right]
                .into_iter()
                .flatten()
                .all(|v| v == id(0) || v == id(3))
        }));
        if lower == u64::MAX {
            assert!(next.word_expression(id(0)).is_none());
        }
    }
}

#[test]
fn unknown_and_dropped_guards_are_not_reinvented_and_targets_are_unique() {
    let mut state = ResourceState::new();
    define(&mut state, 0, AbstractValue::Bool(AbstractBool::Unknown));
    define(&mut state, 1, AbstractValue::Bool(AbstractBool::Unknown));
    state.conjoin_path_fact(PathFact::boolean(id(0), true));
    let projected = state.project_cfg_case(&[(id(1), id(0))]).unwrap();
    assert_eq!(projected.path_condition(), &PathCondition::empty());
    assert!(projected.path_condition().is_reachable());
    assert_eq!(
        state.project_cfg_case(&[(id(0), id(2)), (id(1), id(2))]),
        Err(ResourceStateDefinitionError::DuplicateValue(id(2)))
    );
    let duplicate = state
        .project_cfg_case(&[(id(0), id(2)), (id(0), id(3))])
        .unwrap();
    assert!(
        duplicate
            .path_condition()
            .implies(PathFact::boolean(id(2), true))
    );
    assert!(
        duplicate
            .path_condition()
            .implies(PathFact::boolean(id(3), true))
    );
}

#[test]
fn new_flags_do_not_hide_lost_comparisons() {
    let mut state = ResourceState::new();
    define(&mut state, 0, AbstractValue::U64(U64Interval::exact(0)));
    define(&mut state, 1, AbstractValue::U64(U64Interval::exact(1)));
    define(&mut state, 2, AbstractValue::Bool(AbstractBool::False));
    state.conjoin_path_fact(PathFact::comparison(
        VirIntegerPredicate::LessThan,
        id(0),
        id(1),
    ));
    let renames = [(id(2), id(4)), (id(2), id(5))];
    let projected = state.project_cfg_case(&renames).unwrap();
    assert!(projected.path_condition().atom_count() > state.path_condition().atom_count());
    assert!(state.loses_cfg_guards(&renames));
    assert!(!state.loses_cfg_guards(&[(id(0), id(4)), (id(1), id(5))]));
}
