use super::*;

const X: VirValueId = VirValueId::new(41);
const Y: VirValueId = VirValueId::new(42);
const RESULT_X: VirValueId = VirValueId::new(51);
const RESULT_Y: VirValueId = VirValueId::new(52);

fn holders() -> [PredicateCallBinding; 1] {
    [PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(7),
    }]
}
fn inputs() -> [PredicateScalarCallBinding; 2] {
    [
        PredicateScalarCallBinding {
            caller: COUNT,
            callee: X,
        },
        PredicateScalarCallBinding {
            caller: OTHER,
            callee: Y,
        },
    ]
}
fn outputs() -> [PredicateScalarCallBinding; 2] {
    [
        PredicateScalarCallBinding {
            caller: RESULT_X,
            callee: X,
        },
        PredicateScalarCallBinding {
            caller: RESULT_Y,
            callee: Y,
        },
    ]
}
fn caller(local: bool, hidden: bool) -> ResourceState {
    let (mut caller, def, args) = if hidden {
        hidden_sum_setup(true)
    } else {
        composite_setup(true)
    };
    if local {
        caller.word_origins.clear();
    }
    import(&mut caller, &def, &args).unwrap();
    caller
}
fn has_sum(state: &ResourceState, a: VirValueId, b: VirValueId) -> bool {
    state
        .array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8)
        .contains(
            &AffineExpression::identity(a)
                .checked_add(AffineExpression::identity(b))
                .unwrap(),
        )
}

#[test]
fn explicit_scalar_frames_preserve_actual_sum_prefixes_and_capture_identity() {
    for local in [false, true] {
        for hidden in [false, true] {
            let caller = caller(local, hidden);
            let before = caller.clone();
            let (frame, callee) =
                enter_predicate_call_with_scalars(&caller, &holders(), &inputs()).unwrap();
            assert_eq!(caller, before);
            assert_eq!(
                callee.values.keys().copied().collect::<Vec<_>>(),
                vec![X, Y]
            );
            assert!(has_sum(&callee, X, Y));
            assert_eq!(
                callee.closed_predicate_checks(),
                vec![(PredicateHolder(7), true)]
            );
            assert_ne!(
                callee
                    .allocation(ALLOCATION)
                    .unwrap()
                    .initialization()
                    .classify(ByteRange::new(0, 16).unwrap()),
                InitializationClass::Initialized
            );
            if !local {
                assert_ne!(callee.word_origin(X), caller.word_origin(COUNT));
            }
            let returned = frame
                .resume_with_scalars(&callee, &holders(), &outputs())
                .unwrap();
            assert!(has_sum(&returned, RESULT_X, RESULT_Y));
            assert!(!has_sum(&returned, COUNT, OTHER));
            assert_eq!(
                returned.closed_predicate_checks(),
                vec![(PredicateHolder(0), true)]
            );
            assert_eq!(returned.value(COUNT), caller.value(COUNT));
            let mut changed = returned.clone();
            *changed.value_mut(RESULT_Y).unwrap() =
                AbstractValue::U64(U64Interval::new(0, 1).unwrap());
            assert!(!has_sum(&changed, RESULT_X, RESULT_Y));
            assert_eq!(
                changed.closed_predicate_checks(),
                vec![(PredicateHolder(0), false)]
            );
        }
    }
}

#[test]
fn absent_scalar_mappings_and_reused_numbers_do_not_supply_prefix_sources() {
    for local in [false, true] {
        let caller = caller(local, true);
        assert!(enter_predicate_call(&caller, &holders()).is_err());
        for pairs in [
            vec![inputs()[0]],
            vec![inputs()[1]],
            vec![PredicateScalarCallBinding {
                caller: OTHER,
                callee: COUNT,
            }],
        ] {
            assert!(enter_predicate_call_with_scalars(&caller, &holders(), &pairs).is_err());
        }
        let (frame, callee) =
            enter_predicate_call_with_scalars(&caller, &holders(), &inputs()).unwrap();
        assert!(
            frame
                .resume_with_scalars(&callee, &holders(), &outputs()[..1])
                .is_err()
        );
    }
}

#[test]
fn scalar_abi_rejects_missing_nonscalar_duplicate_and_occupied_slots() {
    let caller = caller(false, true);
    let before = caller.clone();
    for pairs in [
        vec![PredicateScalarCallBinding {
            caller: VirValueId::new(999),
            callee: X,
        }],
        vec![PredicateScalarCallBinding {
            caller: VirValueId::new(0),
            callee: X,
        }],
        vec![
            inputs()[0],
            PredicateScalarCallBinding {
                caller: OTHER,
                callee: X,
            },
        ],
        vec![inputs()[0]; MAX_PREDICATE_LOCAL_ALIASES + 1],
    ] {
        assert!(enter_predicate_call_with_scalars(&caller, &holders(), &pairs).is_err());
        assert_eq!(caller, before);
    }
    let (frame, callee) =
        enter_predicate_call_with_scalars(&caller, &holders(), &inputs()).unwrap();
    assert!(matches!(
        frame.resume_with_scalars(&callee, &holders(), &inputs()),
        Err(PredicateError::InvalidBinding)
    ));
}

#[test]
fn callee_source_or_initialization_invalidation_prevents_return() {
    for damage in 0..3 {
        let caller = caller(false, true);
        let (frame, mut callee) =
            enter_predicate_call_with_scalars(&caller, &holders(), &inputs()).unwrap();
        match damage {
            0 => {
                *callee.value_mut(X).unwrap() = AbstractValue::U64(U64Interval::new(0, 1).unwrap());
            }
            1 => callee
                .allocation_mut(ALLOCATION)
                .unwrap()
                .mark_uninitialized(ByteRange::new(0, 8).unwrap())
                .unwrap(),
            _ => callee.seed_parameter_origins(crate::VirFunctionId::new(99), &[X]),
        }
        assert!(
            frame
                .resume_with_scalars(&callee, &holders(), &outputs())
                .is_err()
        );
    }
}

#[test]
fn duplicated_scalar_actual_can_return_through_its_surviving_alias() {
    let alias = VirValueId::new(43);
    for local in [false, true] {
        let caller = caller(local, true);
        let mut pairs = inputs().to_vec();
        pairs.push(PredicateScalarCallBinding {
            caller: COUNT,
            callee: alias,
        });
        let (frame, callee) =
            enter_predicate_call_with_scalars(&caller, &holders(), &pairs).unwrap();
        assert_eq!(
            callee.word_expression(alias),
            Some(AffineExpression::identity(X))
        );
        let mut results = outputs();
        results[0].callee = alias;
        let returned = frame
            .resume_with_scalars(&callee, &holders(), &results)
            .unwrap();
        assert!(has_sum(&returned, RESULT_X, RESULT_Y));
        assert_eq!(
            returned.closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
    }
}
