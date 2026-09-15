use super::*;
use crate::*;

fn id(n: u32) -> VirValueId {
    VirValueId::new(n)
}
fn limits(n: usize) -> GuardedStateLimits {
    GuardedStateLimits {
        max_cases: n,
        max_guard_atoms: 8,
    }
}
fn phase(dead: bool, index: u64) -> ResourceState {
    let mut state = ResourceState::new();
    let allocation = AbstractAllocationId::new(0);
    let mut memory = AbstractAllocation::new(VirRegionId::new(0), 8, 8).unwrap();
    let mut permission = AbstractPermission::new(
        AbstractProvenance::Known(allocation),
        AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap()),
        AccessPermission::Write,
        FreeCapability::Yes,
    );
    if dead {
        memory.mark_dead();
        permission.mark_consumed();
    }
    state.define_allocation(allocation, memory).unwrap();
    state
        .define_value(id(0), AbstractValue::U64(U64Interval::exact(index)))
        .unwrap();
    state
        .define_value(id(1), AbstractValue::Permission(permission))
        .unwrap();
    state
        .define_value(
            id(2),
            AbstractValue::Bool(if dead {
                AbstractBool::False
            } else {
                AbstractBool::True
            }),
        )
        .unwrap();
    state
}
fn singleton(dead: bool, index: u64) -> ConditionalResourceState {
    ConditionalResourceState::singleton(phase(dead, index))
}

fn covers(output: &ConditionalResourceState, input: &ResourceState) -> bool {
    output.cases().iter().any(|out| {
        let Some(AbstractValue::U64(value)) = out.value(id(0)) else {
            return false;
        };
        let Some(AbstractValue::U64(expected)) = input.value(id(0)) else {
            return false;
        };
        let Some(AbstractValue::Permission(p)) = out.value(id(1)) else {
            return false;
        };
        let Some(AbstractValue::Permission(q)) = input.value(id(1)) else {
            return false;
        };
        let live = out
            .allocation(AbstractAllocationId::new(0))
            .unwrap()
            .liveness();
        let expected_live = input
            .allocation(AbstractAllocationId::new(0))
            .unwrap()
            .liveness();
        value.contains(expected.lower())
            && value.contains(expected.upper())
            && (live == LivenessState::MaybeLive || live == expected_live)
            && (p.availability() == PermissionAvailability::MaybeConsumed
                || p.availability() == q.availability())
            && (out.value(id(2)) == Some(&AbstractValue::Bool(AbstractBool::Unknown))
                || out.value(id(2)) == input.value(id(2)))
    })
}

#[test]
fn phase_local_widening_keeps_live_zero_separate_from_consumed_positive_values() {
    let head = singleton(false, 0)
        .join_loop(&singleton(true, 1), limits(4))
        .unwrap();
    let next = head.join_loop(&singleton(true, 2), limits(4)).unwrap();
    let widened = head.widen(&next, limits(4)).unwrap();
    assert_eq!(widened.cases().len(), 2);
    for case in widened.cases() {
        let Some(AbstractValue::U64(index)) = case.value(id(0)) else {
            panic!()
        };
        match case
            .allocation(AbstractAllocationId::new(0))
            .unwrap()
            .liveness()
        {
            LivenessState::Live => assert_eq!(*index, U64Interval::exact(0)),
            LivenessState::Dead => assert_eq!(*index, U64Interval::new(1, u64::MAX).unwrap()),
            LivenessState::MaybeLive => panic!("phases were collapsed"),
        }
    }
    assert_eq!(widened, widened.widen(&next, limits(4)).unwrap());
}

#[test]
fn join_and_widen_cover_both_inputs_including_budget_fallback() {
    for budget in [0, 1, 2, 4] {
        for left_dead in [false, true] {
            for right_dead in [false, true] {
                for a in 0..4 {
                    for b in 0..4 {
                        let left = singleton(left_dead, a);
                        let right = singleton(right_dead, b);
                        for output in [
                            left.join_loop(&right, limits(budget)).unwrap(),
                            left.widen(&right, limits(budget)).unwrap(),
                        ] {
                            assert!(covers(&output, &phase(left_dead, a)));
                            assert!(covers(&output, &phase(right_dead, b)));
                            assert!(output.cases().len() <= budget.max(1));
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn predicate_widening_covers_all_input_values_including_extremes_and_budget_loss() {
    let cuts = [1, 3, u64::MAX];
    let points = [0, 1, 2, 3, 4, u64::MAX - 1, u64::MAX];
    for a in points {
        for b in points {
            for budget in [0, 1, 2, 16] {
                for dead in [false, true] {
                    let left = singleton(false, a);
                    let right = singleton(dead, b);
                    for widening in [false, true] {
                        let out = left
                            .merge_loop(&right, limits(budget), widening, &cuts)
                            .unwrap();
                        assert!(covers(&out, &left.cases()[0]));
                        assert!(covers(&out, &right.cases()[0]));
                    }
                }
            }
            let widened = phase(false, a)
                .widen_loop_predicates(&phase(false, b), &cuts)
                .unwrap();
            let AbstractValue::U64(interval) = widened.value(id(0)).unwrap() else {
                panic!()
            };
            assert!(interval.contains(a) && interval.contains(b));
        }
    }
}

#[test]
fn exhausted_partition_budget_is_sticky_and_never_resurrects_authority() {
    let collapsed = singleton(false, 0)
        .join_loop(&singleton(true, 1), limits(1))
        .unwrap();
    assert!(
        collapsed
            .precision_losses()
            .contains(&GuardedStatePrecisionLoss::LoopPartitionBudget)
    );
    for widening in [false, true] {
        let next = collapsed
            .merge_loop(&singleton(false, 2), limits(16), widening, &[])
            .unwrap();
        assert_eq!(next.cases().len(), 1);
        assert!(covers(&next, &phase(true, 1)) && covers(&next, &phase(false, 2)));
        assert_eq!(
            next.cases()[0]
                .allocation(AbstractAllocationId::new(0))
                .unwrap()
                .liveness(),
            LivenessState::MaybeLive
        );
    }
}

#[test]
fn boolean_phases_survive_even_without_a_resource_difference() {
    let mut a = ResourceState::new();
    let mut b = ResourceState::new();
    a.define_value(id(0), AbstractValue::Bool(AbstractBool::True))
        .unwrap();
    b.define_value(id(0), AbstractValue::Bool(AbstractBool::False))
        .unwrap();
    let joined = ConditionalResourceState::singleton(a)
        .join_loop(&ConditionalResourceState::singleton(b), limits(2))
        .unwrap();
    assert_eq!(joined.cases().len(), 2);
}

#[test]
fn changing_initialization_is_joined_inside_a_phase_without_granting_bytes() {
    let cold = phase(false, 0);
    let mut warm = phase(false, 1);
    let range = ByteRange::new(0, 8).unwrap();
    warm.allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .mark_initialized(range)
        .unwrap();
    assert!(cold.same_loop_partition(&warm));
    let joined = ConditionalResourceState::singleton(cold)
        .join_loop(&ConditionalResourceState::singleton(warm), limits(4))
        .unwrap();
    assert_eq!(joined.cases().len(), 1);
    assert_eq!(
        joined.cases()[0]
            .allocation(AbstractAllocationId::new(0))
            .unwrap()
            .initialization()
            .classify(range),
        InitializationClass::MaybeInitialized
    );
}
