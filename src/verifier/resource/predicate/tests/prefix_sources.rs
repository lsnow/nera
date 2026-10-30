use super::*;
use crate::predicate_logic::*;
mod call_scalars;
mod domains;
mod logical_initialization;

const COUNT: VirValueId = VirValueId::new(21);
const OTHER: VirValueId = VirValueId::new(20);
const ALLOCATION: AbstractAllocationId = AbstractAllocationId::new(0);

fn expression(
    kinds: Vec<(LogicType<VirMemoryAccess>, LogicNodeKind<VirMemoryAccess>)>,
) -> LogicExpression<VirMemoryAccess> {
    LogicExpression {
        root: kinds.len() as u32 - 1,
        nodes: kinds
            .into_iter()
            .map(|(ty, kind)| LogicNode { ty, kind })
            .collect(),
    }
}
fn setup(
    equal: bool,
) -> (
    ResourceState,
    PredicateDefinition,
    WitnessArguments<VirMemoryAccess, VirValueId>,
) {
    use LogicNodeKind::*;
    let mut def = logical_definition();
    def.resources[0].initialized.clear();
    def.scalar_constraints.clear();
    def.logic.parameters.push(LogicParameter {
        name: "n".into(),
        position: 1,
        ty: LogicType::Usize,
    });
    def.logic.constraints[0].nodes[1].kind = Word(2);
    def.logic.constraints.push(expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Existential(0))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (
            LogicType::Bool,
            if equal { Equal(0, 1) } else { LessEqual(0, 1) },
        ),
    ]));
    def.logical_prefixes
        .push(crate::PredicateInitializedPrefix {
            resource: 0,
            array_offset: 0,
            element: VirMemoryAccess::core_u64(),
            length: 2,
            stride: 8,
            count: crate::PredicatePrefixCount::Logical(expression(vec![(
                LogicType::Usize,
                Binder(LogicBinder::Existential(0)),
            )])),
        });
    let mut input = state();
    input
        .allocation_mut(ALLOCATION)
        .unwrap()
        .mark_uninitialized(ByteRange::new(0, 16).unwrap())
        .unwrap();
    for id in [OTHER, COUNT] {
        input
            .define_value(id, AbstractValue::U64(U64Interval::new(0, 2).unwrap()))
            .unwrap();
    }
    input.seed_parameter_origins(crate::VirFunctionId::new(0), &[COUNT, OTHER]);
    let args = WitnessArguments {
        inputs: vec![(LogicType::Usize, WitnessInput::Scalar(COUNT))],
        arguments: vec![expression(vec![(
            LogicType::Usize,
            Binder(LogicBinder::Parameter(0)),
        )])],
        values: vec![],
    };
    (input, def, args)
}
fn import(
    input: &mut ResourceState,
    def: &PredicateDefinition,
    args: &WitnessArguments<VirMemoryAccess, VirValueId>,
) -> Result<(), PredicateError> {
    input.import_predicate_interface_with_arguments(
        def,
        &[binding(0)],
        PredicateHolder(0),
        args,
        true,
    )
}

#[test]
fn hidden_count_equality_imports_only_the_actual_symbolic_prefix() {
    let (mut input, def, args) = setup(true);
    let keys = input.values.keys().copied().collect::<Vec<_>>();
    import(&mut input, &def, &args).unwrap();
    assert_eq!(input.values.keys().copied().collect::<Vec<_>>(), keys);
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_eq!(
        input.array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8),
        vec![AffineExpression::identity(COUNT)]
    );
    assert_ne!(
        input
            .allocation(ALLOCATION)
            .unwrap()
            .initialization()
            .classify(ByteRange::new(0, 16).unwrap()),
        InitializationClass::Initialized
    );
    // A write to the unrelated, equally bounded scalar is not a cursor update.
    let mut unrelated = input.clone();
    *unrelated.value_mut(OTHER).unwrap() = AbstractValue::U64(U64Interval::exact(0));
    assert_eq!(
        unrelated.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let mut overwritten = input.clone();
    *overwritten.value_mut(COUNT).unwrap() = AbstractValue::U64(U64Interval::new(0, 2).unwrap());
    assert_eq!(
        overwritten.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    let mut foreign = input.clone();
    foreign.seed_parameter_origins(crate::VirFunctionId::new(1), &[COUNT]);
    assert_eq!(
        foreign.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    let mut invalidated = input;
    invalidated
        .allocation_mut(ALLOCATION)
        .unwrap()
        .mark_uninitialized(ByteRange::new(0, 8).unwrap())
        .unwrap();
    assert_eq!(
        invalidated.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
}

#[test]
fn one_sided_hidden_contract_keeps_a_logical_prefix_without_enlarging_the_cursor() {
    let (mut input, def, args) = setup(false);
    let mut imported = input.clone();
    import(&mut imported, &def, &args).unwrap();
    assert_eq!(
        imported.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert!(
        imported
            .array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8)
            .is_empty()
    );
    assert!(input.bind_array_initialization_prefix(
        ALLOCATION,
        0,
        VirMemoryAccess::core_u64(),
        2,
        8,
        AffineExpression::identity(COUNT)
    ));
    let before = input.allocation(ALLOCATION).unwrap().clone();
    import(&mut input, &def, &args).unwrap();
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_eq!(input.allocation(ALLOCATION), Some(&before));
}

#[test]
fn logical_contract_import_still_requires_authority_and_live_storage() {
    for mutation in 0..4 {
        let (mut input, mut def, args) = setup(true);
        match mutation {
            0 => {
                def.logic.constraints.pop();
            }
            1 => {
                input.values.remove(&binding(0).permission);
            }
            2 => {
                // A prefix associated with an unrelated count is not coverage
                // for the declared count, despite identical numeric ranges.
                def.logic.constraints.pop();
                input.bind_array_initialization_prefix(
                    ALLOCATION,
                    0,
                    VirMemoryAccess::core_u64(),
                    2,
                    8,
                    AffineExpression::identity(OTHER),
                );
            }
            _ => {
                input
                    .allocation_mut(ALLOCATION)
                    .unwrap()
                    .set_liveness(LivenessState::Dead);
            }
        }
        let before = input.clone();
        if mutation == 0 || mutation == 2 {
            import(&mut input, &def, &args).unwrap();
            assert_eq!(
                input.closed_predicate_checks(),
                vec![(PredicateHolder(0), true)]
            );
        } else {
            assert!(
                import(&mut input, &def, &args).is_err(),
                "mutation {mutation}"
            );
            assert_eq!(input, before);
        }
    }
}

fn composite_setup(
    sum: bool,
) -> (
    ResourceState,
    PredicateDefinition,
    WitnessArguments<VirMemoryAccess, VirValueId>,
) {
    use LogicNodeKind::*;
    let (mut input, mut def, mut args) = setup(true);
    // No independent SSA result exists for n+1 or n+m. Each input remains
    // a real runtime coordinate with a different immutable origin.
    for id in [COUNT, OTHER] {
        input.narrow_word_interval(id, U64Interval::new(0, 1).unwrap());
    }
    def.logic.constraints.clear();
    let n = Binder(LogicBinder::Parameter(0));
    let second = if sum {
        def.logic.parameters.push(LogicParameter {
            name: "m".into(),
            position: 2,
            ty: LogicType::Usize,
        });
        args.inputs
            .push((LogicType::Usize, WitnessInput::Scalar(OTHER)));
        args.arguments.push(expression(vec![(
            LogicType::Usize,
            Binder(LogicBinder::Parameter(1)),
        )]));
        Binder(LogicBinder::Parameter(1))
    } else {
        Word(1)
    };
    def.logical_prefixes[0].count = crate::PredicatePrefixCount::Logical(expression(vec![
        (LogicType::Usize, n),
        (LogicType::Usize, second),
        (LogicType::Usize, Add(0, 1)),
    ]));
    (input, def, args)
}

#[test]
fn compound_counts_bind_actual_operands_without_inventing_a_result_slot() {
    for sum in [false, true] {
        let (mut input, def, args) = composite_setup(sum);
        let values = input.values.clone();
        import(&mut input, &def, &args).unwrap();
        for id in [COUNT, OTHER] {
            assert_eq!(
                input.value(id),
                values.get(&id),
                "count bounds are not root bounds"
            );
        }
        assert_eq!(
            input.values.keys().collect::<Vec<_>>(),
            values.keys().collect::<Vec<_>>()
        );
        let expected = if sum {
            AffineExpression::identity(COUNT)
                .checked_add(AffineExpression::identity(OTHER))
                .unwrap()
        } else {
            AffineExpression::identity(COUNT)
                .checked_add_constant(1)
                .unwrap()
        };
        assert_eq!(
            input.array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8),
            vec![expected]
        );
        assert_eq!(
            input.closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
        assert_ne!(
            input
                .allocation(ALLOCATION)
                .unwrap()
                .initialization()
                .classify(ByteRange::new(0, 16).unwrap()),
            InitializationClass::Initialized
        );
        for id in [COUNT, OTHER] {
            let mut changed = input.clone();
            *changed.value_mut(id).unwrap() = AbstractValue::U64(U64Interval::new(0, 1).unwrap());
            assert_eq!(
                changed.closed_predicate_checks(),
                vec![(PredicateHolder(0), !sum && id == OTHER)]
            );
        }
        let mut invalidated = input.clone();
        invalidated
            .allocation_mut(ALLOCATION)
            .unwrap()
            .mark_uninitialized(ByteRange::new(8, 16).unwrap())
            .unwrap();
        assert_eq!(
            invalidated.closed_predicate_checks(),
            vec![(PredicateHolder(0), false)]
        );
        let mut foreign = input;
        foreign.seed_parameter_origins(crate::VirFunctionId::new(1), &[COUNT]);
        assert_eq!(
            foreign.closed_predicate_checks(),
            vec![(PredicateHolder(0), false)]
        );
    }
}

#[test]
fn scaled_count_does_not_narrow_its_operand_to_the_count_interval() {
    use LogicNodeKind::*;
    let (mut input, mut def, args) = composite_setup(false);
    def.logical_prefixes[0].count = crate::PredicatePrefixCount::Logical(expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (
            LogicType::Usize,
            Scale {
                operand: 0,
                factor: 2,
            },
        ),
    ]));
    let before = input.values.clone();
    import(&mut input, &def, &args).unwrap();
    for id in [COUNT, OTHER] {
        assert_eq!(input.value(id), before.get(&id));
    }
    assert_eq!(
        input.array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8),
        vec![AffineExpression::identity(COUNT).checked_scale(2).unwrap()]
    );
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
}

#[test]
fn compound_prefix_domain_and_authority_failures_do_not_publish_partial_state() {
    for mutation in 0..4 {
        let (mut input, mut def, args) = composite_setup(false);
        match mutation {
            0 => {
                input.values.remove(&binding(0).permission);
            }
            1 => {
                *input.value_mut(COUNT).unwrap() = AbstractValue::U64(U64Interval::unknown());
            }
            2 => {
                // No possible operand satisfies n+1 <= length.
                *input.value_mut(COUNT).unwrap() =
                    AbstractValue::U64(U64Interval::new(2, 3).unwrap());
            }
            _ => {
                def.logical_prefixes[0].array_offset = 8;
            }
        }
        let before = input.clone();
        assert!(
            import(&mut input, &def, &args).is_err(),
            "mutation {mutation}"
        );
        assert_eq!(input, before);
    }
}

#[test]
fn compound_prefix_can_choose_an_actual_immutable_alias_but_not_an_equal_range() {
    let (mut input, def, args) = composite_setup(false);
    // OTHER precedes COUNT in the source table. Give it a complete, actual
    // copy of COUNT's immutable history; interval equality alone did not do so
    // in compound_counts_bind_actual_operands_without_inventing_a_result_slot.
    input
        .word_origins
        .insert(OTHER, input.word_origin(COUNT).unwrap());
    import(&mut input, &def, &args).unwrap();
    assert_eq!(
        input.array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8),
        vec![
            AffineExpression::identity(OTHER)
                .checked_add_constant(1)
                .unwrap()
        ]
    );
    *input.value_mut(COUNT).unwrap() = AbstractValue::U64(U64Interval::new(0, 1).unwrap());
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    *input.value_mut(OTHER).unwrap() = AbstractValue::U64(U64Interval::new(0, 1).unwrap());
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
}

#[test]
fn signed_count_retains_a_logical_prefix_without_a_positive_ssa_approximation() {
    let (mut input, mut def, args) = composite_setup(true);
    *input.value_mut(COUNT).unwrap() = AbstractValue::U64(U64Interval::new(1, 2).unwrap());
    let crate::PredicatePrefixCount::Logical(expression) = &mut def.logical_prefixes[0].count
    else {
        unreachable!()
    };
    expression.nodes[2].kind = LogicNodeKind::Sub(0, 1);
    import(&mut input, &def, &args).unwrap();
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert!(
        input
            .array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8)
            .is_empty()
    );
    assert_ne!(
        input
            .allocation(ALLOCATION)
            .unwrap()
            .initialization()
            .classify(ByteRange::new(0, 16).unwrap()),
        InitializationClass::Initialized
    );
}

fn offset_setup(
    offset: u64,
    equal: bool,
) -> (
    ResourceState,
    PredicateDefinition,
    WitnessArguments<VirMemoryAccess, VirValueId>,
) {
    use LogicNodeKind::*;
    let (mut input, mut def, args) = setup(equal);
    let length = offset + 1;
    let bytes = length * 8;
    def.resources[0].size_bytes = bytes;
    def.logical_prefixes[0].length = length;
    def.logic.constraints[0].nodes[1].kind = Word(length);
    *def.logic.constraints.last_mut().unwrap() = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Existential(0))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(offset)),
        (LogicType::Usize, Add(1, 2)),
        (
            LogicType::Bool,
            if equal { Equal(0, 3) } else { LessEqual(0, 3) },
        ),
    ]);
    *input.allocation_mut(ALLOCATION).unwrap() =
        AbstractAllocation::new(VirRegionId::new(0), bytes, 8).unwrap();
    *input.value_mut(binding(0).permission).unwrap() =
        AbstractValue::Permission(AbstractPermission::new(
            AbstractProvenance::Known(ALLOCATION),
            AbstractByteRange::Exact(ByteRange::new(0, bytes).unwrap()),
            AccessPermission::Write,
            FreeCapability::Yes,
        ));
    for id in [COUNT, OTHER] {
        input.narrow_word_interval(id, U64Interval::new(0, 1).unwrap());
    }
    (input, def, args)
}

#[test]
fn hidden_offsets_bind_actual_sources_even_when_operand_intervals_are_disjoint() {
    for offset in [1, 2] {
        let (mut input, def, args) = offset_setup(offset, true);
        let values = input.values.clone();
        import(&mut input, &def, &args).unwrap();
        assert_eq!(input.value(COUNT), values.get(&COUNT));
        assert_eq!(
            input.values.keys().collect::<Vec<_>>(),
            values.keys().collect::<Vec<_>>()
        );
        assert_eq!(
            input.array_initialization_counts(
                ALLOCATION,
                0,
                VirMemoryAccess::core_u64(),
                offset + 1,
                8
            ),
            vec![
                AffineExpression::identity(COUNT)
                    .checked_add_constant(offset)
                    .unwrap()
            ]
        );
        assert_eq!(
            input.closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
        let allocation = input.allocation(ALLOCATION).unwrap();
        assert_eq!(
            allocation
                .initialization()
                .classify(ByteRange::new(0, offset * 8).unwrap()),
            InitializationClass::Initialized
        );
        assert_ne!(
            allocation
                .initialization()
                .classify(ByteRange::new(0, (offset + 1) * 8).unwrap()),
            InitializationClass::Initialized
        );
        for id in [COUNT, OTHER] {
            let mut changed = input.clone();
            *changed.value_mut(id).unwrap() = AbstractValue::U64(U64Interval::new(0, 1).unwrap());
            assert_eq!(
                changed.closed_predicate_checks(),
                vec![(PredicateHolder(0), id == OTHER)]
            );
        }
        let mut foreign = input.clone();
        foreign.seed_parameter_origins(crate::VirFunctionId::new(1), &[COUNT]);
        assert_eq!(
            foreign.closed_predicate_checks(),
            vec![(PredicateHolder(0), false)]
        );
        input
            .allocation_mut(ALLOCATION)
            .unwrap()
            .mark_uninitialized(ByteRange::new(0, 8).unwrap())
            .unwrap();
        assert_eq!(
            input.closed_predicate_checks(),
            vec![(PredicateHolder(0), false)]
        );
    }
}

#[test]
fn hidden_offset_import_preserves_authority_and_uses_logical_negative_offsets() {
    for mutation in 0..4 {
        let (mut input, mut def, args) = offset_setup(1, mutation != 0);
        match mutation {
            0 => {}
            1 => {
                input.values.remove(&binding(0).permission);
            }
            2 => {
                *input.value_mut(COUNT).unwrap() =
                    AbstractValue::U64(U64Interval::new(2, 3).unwrap());
            }
            _ => {
                // n == used+1 needs a negative endpoint offset, not n+1.
                let e = def.logic.constraints.last_mut().unwrap();
                e.nodes[3].kind = LogicNodeKind::Add(0, 2);
                e.nodes[4].kind = LogicNodeKind::Equal(1, 3);
                *input.value_mut(COUNT).unwrap() =
                    AbstractValue::U64(U64Interval::new(1, 2).unwrap());
            }
        }
        let before = input.clone();
        if mutation == 0 || mutation == 3 {
            import(&mut input, &def, &args).unwrap();
            assert_eq!(
                input.closed_predicate_checks(),
                vec![(PredicateHolder(0), true)]
            );
            assert!(
                input
                    .array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8)
                    .is_empty()
            );
        } else {
            assert!(
                import(&mut input, &def, &args).is_err(),
                "mutation {mutation}"
            );
            assert_eq!(input, before);
        }
    }
}

#[test]
fn hidden_offset_bounds_refine_only_the_proved_source_without_extra_input_constraints() {
    let (mut input, def, args) = offset_setup(2, true);
    *input.value_mut(COUNT).unwrap() = AbstractValue::U64(U64Interval::unknown());
    input.seed_parameter_origins(crate::VirFunctionId::new(0), &[COUNT]);
    let origin = input.word_origin(COUNT);
    let keys = input.values.keys().copied().collect::<Vec<_>>();
    let other = input.value(OTHER).copied();
    import(&mut input, &def, &args).unwrap();
    assert_eq!(
        input.value(COUNT),
        Some(&AbstractValue::U64(U64Interval::new(0, 1).unwrap()))
    );
    assert_eq!(input.word_origin(COUNT), origin);
    assert_eq!(input.value(OTHER).copied(), other);
    assert_eq!(input.values.keys().copied().collect::<Vec<_>>(), keys);
    assert_eq!(
        input.array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 3, 8),
        vec![
            AffineExpression::identity(COUNT)
                .checked_add_constant(2)
                .unwrap()
        ]
    );
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_ne!(
        input
            .allocation(ALLOCATION)
            .unwrap()
            .initialization()
            .classify(ByteRange::new(0, 24).unwrap()),
        InitializationClass::Initialized
    );
}

fn scaled_domain_setup() -> (
    ResourceState,
    PredicateDefinition,
    WitnessArguments<VirMemoryAccess, VirValueId>,
) {
    use LogicNodeKind::*;
    let (mut input, mut def, args) = offset_setup(4, true);
    *input.value_mut(COUNT).unwrap() = AbstractValue::U64(U64Interval::unknown());
    input.seed_parameter_origins(crate::VirFunctionId::new(0), &[COUNT]);
    let count = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (
            LogicType::Usize,
            Scale {
                operand: 0,
                factor: 2,
            },
        ),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(1, 2)),
    ]);
    def.logical_prefixes[0].count = crate::PredicatePrefixCount::Logical(count.clone());
    let mut constraint = count;
    constraint.nodes.push(LogicNode {
        ty: LogicType::Usize,
        kind: Word(5),
    });
    constraint.nodes.push(LogicNode {
        ty: LogicType::Bool,
        kind: LessEqual(3, 4),
    });
    constraint.root = 5;
    def.logic.constraints = vec![constraint];
    (input, def, args)
}

#[test]
fn scaled_count_bounds_admit_actual_arithmetic_after_inverse_domain_refinement() {
    let (mut input, def, args) = scaled_domain_setup();
    let origin = input.word_origin(COUNT);
    import(&mut input, &def, &args).unwrap();
    assert_eq!(
        input.value(COUNT),
        Some(&AbstractValue::U64(U64Interval::new(0, 2).unwrap()))
    );
    assert_eq!(input.word_origin(COUNT), origin);
    assert_eq!(
        input.array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 5, 8),
        vec![
            AffineExpression::identity(COUNT)
                .checked_scale(2)
                .unwrap()
                .checked_add_constant(1)
                .unwrap()
        ]
    );
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_ne!(
        input
            .allocation(ALLOCATION)
            .unwrap()
            .initialization()
            .classify(ByteRange::new(0, 40).unwrap()),
        InitializationClass::Initialized
    );
    *input.value_mut(COUNT).unwrap() = AbstractValue::U64(U64Interval::new(0, 2).unwrap());
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
}

#[test]
fn later_import_failure_rolls_back_source_bounds_and_prefix_facts() {
    let (mut input, mut def, args) = scaled_domain_setup();
    let index = def.logic.existentials.len() as u32;
    def.logic.existentials.push(Existential {
        name: "unrelated".into(),
        ty: LogicType::Usize,
        default: None,
    });
    let mut unsupported = def.logical_prefixes[0].clone();
    unsupported.count = crate::PredicatePrefixCount::Logical(expression(vec![(
        LogicType::Usize,
        LogicNodeKind::Binder(LogicBinder::Existential(index)),
    )]));
    // The second range extends outside the actual allocation; unlike a
    // hidden endpoint, this is not a valid checked contract premise.
    unsupported.array_offset = 8;
    def.logical_prefixes.push(unsupported);
    def.logic.constraints.push(expression(vec![
        (
            LogicType::Usize,
            LogicNodeKind::Binder(LogicBinder::Existential(index)),
        ),
        (LogicType::Usize, LogicNodeKind::Word(5)),
        (LogicType::Bool, LogicNodeKind::LessEqual(0, 1)),
    ]));
    let before = input.clone();
    assert!(import(&mut input, &def, &args).is_err());
    assert_eq!(input, before);
}

fn hidden_sum_setup(
    equal: bool,
) -> (
    ResourceState,
    PredicateDefinition,
    WitnessArguments<VirMemoryAccess, VirValueId>,
) {
    use LogicNodeKind::*;
    let (input, mut def, args) = composite_setup(true);
    def.logical_prefixes[0].count = crate::PredicatePrefixCount::Logical(expression(vec![(
        LogicType::Usize,
        Binder(LogicBinder::Existential(0)),
    )]));
    def.logic.constraints = vec![
        expression(vec![
            (LogicType::Usize, Binder(LogicBinder::Existential(0))),
            (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
            (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
            (LogicType::Usize, Add(1, 2)),
            (
                LogicType::Bool,
                if equal { Equal(0, 3) } else { LessEqual(0, 3) },
            ),
        ]),
        expression(vec![
            (LogicType::Usize, Binder(LogicBinder::Existential(0))),
            (LogicType::Usize, Word(2)),
            (LogicType::Bool, LessEqual(0, 1)),
        ]),
    ];
    (input, def, args)
}

#[test]
fn hidden_counts_can_select_a_proved_sum_of_two_actual_sources() {
    let (mut input, def, args) = hidden_sum_setup(true);
    let keys = input.values.keys().copied().collect::<Vec<_>>();
    import(&mut input, &def, &args).unwrap();
    assert_eq!(input.values.keys().copied().collect::<Vec<_>>(), keys);
    assert_eq!(
        input.array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8),
        vec![
            AffineExpression::identity(COUNT)
                .checked_add(AffineExpression::identity(OTHER))
                .unwrap()
        ]
    );
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    for id in [COUNT, OTHER] {
        let mut changed = input.clone();
        *changed.value_mut(id).unwrap() = AbstractValue::U64(U64Interval::new(0, 1).unwrap());
        assert_eq!(
            changed.closed_predicate_checks(),
            vec![(PredicateHolder(0), false)]
        );
    }
    let mut foreign = input.clone();
    foreign.seed_parameter_origins(crate::VirFunctionId::new(1), &[COUNT]);
    assert_eq!(
        foreign.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    input
        .allocation_mut(ALLOCATION)
        .unwrap()
        .mark_uninitialized(ByteRange::new(0, 8).unwrap())
        .unwrap();
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
}

#[test]
fn one_sided_sum_relation_keeps_the_declared_ghost_range_without_an_ssa_sum() {
    let (mut input, def, args) = hidden_sum_setup(false);
    let mut imported = input.clone();
    import(&mut imported, &def, &args).unwrap();
    assert_eq!(
        imported.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert!(
        imported
            .array_initialization_counts(ALLOCATION, 0, VirMemoryAccess::core_u64(), 2, 8)
            .is_empty()
    );
    assert!(
        input.bind_array_initialization_prefix(
            ALLOCATION,
            0,
            VirMemoryAccess::core_u64(),
            2,
            8,
            AffineExpression::identity(COUNT)
                .checked_add(AffineExpression::identity(OTHER))
                .unwrap()
        )
    );
    import(&mut input, &def, &args).unwrap();
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
}

#[test]
fn hidden_sum_relation_chain_uses_saved_facts_without_rebinding_hidden_names() {
    use LogicNodeKind::*;
    let (mut input, mut def, args) = hidden_sum_setup(true);
    def.logic.existentials.push(Existential {
        name: "middle".into(),
        ty: LogicType::Usize,
        default: None,
    });
    def.logic.constraints[0].nodes[0].kind = Binder(LogicBinder::Existential(1));
    def.logic.constraints.push(expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Existential(0))),
        (LogicType::Usize, Binder(LogicBinder::Existential(1))),
        (LogicType::Bool, Equal(0, 1)),
    ]));
    import(&mut input, &def, &args).unwrap();
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
}

#[test]
fn compound_candidates_cannot_replace_missing_authority_or_live_operands() {
    for mutation in 0..3 {
        let (mut input, def, args) = hidden_sum_setup(true);
        match mutation {
            0 => {
                input.values.remove(&binding(0).permission);
            }
            1 => {
                input.values.remove(&OTHER);
            }
            _ => {
                input
                    .allocation_mut(ALLOCATION)
                    .unwrap()
                    .set_liveness(LivenessState::Dead);
            }
        }
        let before = input.clone();
        assert!(import(&mut input, &def, &args).is_err());
        assert_eq!(input, before);
    }
}
