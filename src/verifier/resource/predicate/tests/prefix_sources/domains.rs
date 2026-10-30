use super::*;

fn bounded_operand_setup() -> (
    ResourceState,
    PredicateDefinition,
    WitnessArguments<VirMemoryAccess, VirValueId>,
) {
    let (mut input, def, args) = composite_setup(true);
    *input.value_mut(COUNT).unwrap() = AbstractValue::U64(U64Interval::new(0, 3).unwrap());
    *input.value_mut(OTHER).unwrap() = AbstractValue::U64(U64Interval::exact(1));
    input.seed_parameter_origins(crate::VirFunctionId::new(0), &[COUNT, OTHER]);
    (input, def, args)
}

#[test]
fn another_actual_operand_bounds_the_imported_sum_without_new_sources() {
    let (mut input, def, args) = bounded_operand_setup();
    let origins = input.word_origins.clone();
    let keys = input.values.keys().copied().collect::<Vec<_>>();
    import(&mut input, &def, &args).unwrap();
    assert_eq!(
        input.value(COUNT),
        Some(&AbstractValue::U64(U64Interval::new(0, 1).unwrap()))
    );
    assert_eq!(
        input.value(OTHER),
        Some(&AbstractValue::U64(U64Interval::exact(1)))
    );
    assert_eq!(input.word_origins, origins);
    assert_eq!(input.values.keys().copied().collect::<Vec<_>>(), keys);
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_eq!(
        input
            .allocation(ALLOCATION)
            .unwrap()
            .initialization()
            .classify(ByteRange::new(0, 8).unwrap()),
        InitializationClass::Initialized
    );
    assert_ne!(
        input
            .allocation(ALLOCATION)
            .unwrap()
            .initialization()
            .classify(ByteRange::new(8, 16).unwrap()),
        InitializationClass::Initialized
    );
    assert!(
        input
            .array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8)
            .contains(
                &AffineExpression::identity(COUNT)
                    .checked_add(AffineExpression::identity(OTHER))
                    .unwrap()
            )
    );
    *input.value_mut(OTHER).unwrap() = AbstractValue::U64(U64Interval::exact(1));
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
}

#[test]
fn joint_bounds_that_do_not_prove_independent_endpoint_ranges_still_roll_back() {
    let (mut input, def, args) = composite_setup(true);
    for id in [COUNT, OTHER] {
        *input.value_mut(id).unwrap() = AbstractValue::U64(U64Interval::new(0, 3).unwrap());
    }
    input.seed_parameter_origins(crate::VirFunctionId::new(0), &[COUNT, OTHER]);
    let before = input.clone();
    // n+m<=2 permits n and m separately up to 2, but their independent box
    // still reaches 4. Projection alone is not a persistent joint certificate.
    assert!(import(&mut input, &def, &args).is_err());
    assert_eq!(input, before);
}

#[test]
fn later_failure_discards_all_projected_operand_bounds_and_initialization() {
    let (mut input, mut def, args) = bounded_operand_setup();
    let binder = def.logic.existentials.len() as u32;
    def.logic.existentials.push(Existential {
        name: "unrelated".into(),
        ty: LogicType::Usize,
        default: None,
    });
    let mut unsupported = def.logical_prefixes[0].clone();
    unsupported.count = crate::PredicatePrefixCount::Logical(expression(vec![(
        LogicType::Usize,
        LogicNodeKind::Binder(LogicBinder::Existential(binder)),
    )]));
    def.logical_prefixes.push(unsupported);
    let before = input.clone();
    assert!(import(&mut input, &def, &args).is_err());
    assert_eq!(input, before);
}

#[test]
fn projected_sum_sources_survive_explicit_internal_scalar_transport() {
    let (mut input, def, args) = bounded_operand_setup();
    import(&mut input, &def, &args).unwrap();
    let holders = [PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(7),
    }];
    let mappings = [
        PredicateScalarCallBinding {
            caller: COUNT,
            callee: VirValueId::new(40),
        },
        PredicateScalarCallBinding {
            caller: OTHER,
            callee: VirValueId::new(41),
        },
    ];
    let (frame, callee) = enter_predicate_call_with_scalars(&input, &holders, &mappings).unwrap();
    assert_eq!(callee.value(VirValueId::new(40)), input.value(COUNT));
    assert_eq!(
        callee.closed_predicate_checks(),
        vec![(PredicateHolder(7), true)]
    );
    let results = [
        PredicateScalarCallBinding {
            caller: VirValueId::new(50),
            callee: VirValueId::new(40),
        },
        PredicateScalarCallBinding {
            caller: VirValueId::new(51),
            callee: VirValueId::new(41),
        },
    ];
    let returned = frame
        .resume_with_scalars(&callee, &holders, &results)
        .unwrap();
    assert_eq!(
        returned.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
}
