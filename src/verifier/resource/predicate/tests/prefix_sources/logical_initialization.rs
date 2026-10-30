use super::*;

fn hidden() -> (ResourceState, PredicateDefinition) {
    use LogicNodeKind::*;
    let (input, mut def, _) = setup(true);
    def.logic.parameters.clear();
    def.logic.constraints.pop();
    def.logic.constraints.push(expression(vec![
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Binder(LogicBinder::Existential(0))),
        (LogicType::Bool, LessEqual(0, 1)),
    ]));
    (input, def)
}

fn indexed() -> ResourceState {
    let (mut input, mut def, args) = setup(false);
    // The actual index is strictly below the hidden initialized count, not
    // equal to it. Thus importing the clause cannot find an SSA endpoint.
    let relation = def.logic.constraints.last_mut().unwrap();
    relation.nodes[2].kind = LogicNodeKind::Less(1, 0);
    for id in [COUNT, OTHER] {
        input
            .values
            .insert(id, AbstractValue::U64(U64Interval::new(0, 1).unwrap()));
    }
    input.seed_parameter_origins(crate::VirFunctionId::new(0), &[COUNT, OTHER]);
    import(&mut input, &def, &args).unwrap();
    input
}

fn indexed_range(index: VirValueId, width: u64) -> AbstractByteRange {
    let start = SymbolicRangeBound::new(
        AffineExpression::identity(index).checked_scale(8).unwrap(),
        U64Interval::new(0, 8).unwrap(),
    );
    AbstractByteRange::from_bounds(start, start.checked_add_constant(width).unwrap())
}

#[test]
fn logical_prefix_access_uses_actual_index_identity_and_leaves_storage_unchanged() {
    let input = indexed();
    let before = input.clone();
    for (index, width, expected) in [
        (COUNT, 8, true),
        (COUNT, 16, false),
        (OTHER, 8, false),
        (COUNT, 4, false),
    ] {
        let proven = input.logical_initialized_prefix_covers(
            ALLOCATION,
            VirMemoryAccess::core_u64(),
            indexed_range(index, width),
        );
        assert_eq!(proven, expected);
        if proven {
            for actual_index in 0..=1 {
                for count in 0..=2 {
                    if actual_index < count {
                        assert!(actual_index * 8 + width <= count * 8);
                    }
                }
            }
        }
    }
    assert_eq!(input, before);
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert_eq!(
        input.logical_prefix_access(
            ALLOCATION,
            VirMemoryAccess::core_u64(),
            indexed_range(COUNT, 8),
            &mut budget
        ),
        Err(PredicateError::Budget)
    );
    assert!(!input.logical_initialized_prefix_covers(
        AbstractAllocationId::new(99),
        VirMemoryAccess::core_u64(),
        indexed_range(COUNT, 8)
    ));
    assert!(!input.logical_initialized_prefix_covers(
        ALLOCATION,
        VirMemoryAccess::new(crate::VirTypeId::new(99), crate::VirLayoutId::new(99)),
        indexed_range(COUNT, 8)
    ));
}

#[test]
fn logical_prefix_access_rejects_stale_observations_and_storage_revisions() {
    let input = indexed();
    for mutation in 0..5 {
        let mut bad = input.clone();
        match mutation {
            0 => bad
                .allocation_mut(ALLOCATION)
                .unwrap()
                .forget_validity(ByteRange::new(8, 16).unwrap())
                .unwrap(),
            1 => bad.allocation_mut(ALLOCATION).unwrap().mark_dead(),
            2 => {
                *bad.value_mut(COUNT).unwrap() =
                    AbstractValue::U64(U64Interval::new(0, 1).unwrap());
            }
            3 => bad.seed_parameter_origins(crate::VirFunctionId::new(99), &[COUNT]),
            _ => bad.predicates.clear(),
        }
        assert!(
            !bad.logical_initialized_prefix_covers(
                ALLOCATION,
                VirMemoryAccess::core_u64(),
                indexed_range(COUNT, 8)
            ),
            "mutation {mutation}"
        );
    }
}

#[test]
fn hidden_prefix_abstraction_preserves_the_package_without_materializing_its_upper_bound() {
    let (mut input, def) = hidden();
    import(&mut input, &def, &WitnessArguments::default()).unwrap();
    let before = input.clone();
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    input.abstract_loop_predicates(&repacked).unwrap();
    assert_ne!(
        input.predicates[&PredicateHolder(0)].logic_scope,
        before.predicates[&PredicateHolder(0)].logic_scope
    );
    assert_eq!(input.values, before.values);
    assert_eq!(input.allocations, before.allocations);
    assert_eq!(input.loans, before.loans);
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert!(input.loop_resources_match_with_predicates(
        &before,
        &[binding(0).permission],
        &repacked
    ));
    let opened = transfer_predicate(
        &input,
        &def,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 41,
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        opened.opened_predicate_snapshot(41, 0, 0),
        Some((AbstractValue::U64(U64Interval::new(1, 2).unwrap()), None))
    );
    // The new endpoint is abstract: the larger allowed count is not a witness
    // that the second slot was initialized on this concrete path.
    assert_eq!(
        transfer_predicate(&opened, &def, 7, &explicit_effect(2)),
        Err(PredicateError::UnprovedRepresentation)
    );
}

#[test]
fn hidden_prefix_abstraction_cannot_revive_invalid_storage_or_missing_carriers() {
    let (mut input, def) = hidden();
    import(&mut input, &def, &WitnessArguments::default()).unwrap();
    for mutation in 0..7 {
        let mut bad = input.clone();
        match mutation {
            0 => {
                bad.values.remove(&binding(0).permission);
            }
            1 => bad
                .allocation_mut(ALLOCATION)
                .unwrap()
                .mark_uninitialized(ByteRange::new(8, 16).unwrap())
                .unwrap(),
            2 => bad
                .allocation_mut(ALLOCATION)
                .unwrap()
                .forget_validity(ByteRange::new(8, 16).unwrap())
                .unwrap(),
            3 => bad.allocation_mut(ALLOCATION).unwrap().mark_dead(),
            4 => {
                bad.allocation_mut(ALLOCATION)
                    .unwrap()
                    .initialization_revision = None
            }
            5 => {
                bad.predicates
                    .get_mut(&PredicateHolder(0))
                    .unwrap()
                    .definition
                    .logical_prefixes[0]
                    .array_offset = 8
            }
            _ => bad.next_predicate_scope = u64::MAX,
        }
        let before = bad.clone();
        assert!(
            bad.abstract_loop_predicates(&BTreeSet::from([PredicateHolder(0)]))
                .is_err(),
            "mutation {mutation}"
        );
        assert_eq!(bad, before, "failed abstraction must be atomic");
    }
}

#[test]
fn checked_ghost_prefix_keeps_storage_evidence_and_only_materializes_its_lower_bound() {
    let (mut input, def) = hidden();
    let keys = input.values.keys().copied().collect::<Vec<_>>();
    import(&mut input, &def, &WitnessArguments::default()).unwrap();
    assert_eq!(input.values.keys().copied().collect::<Vec<_>>(), keys);
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let allocation = input.allocation(ALLOCATION).unwrap();
    assert_eq!(
        allocation
            .initialization()
            .classify(ByteRange::new(0, 8).unwrap()),
        InitializationClass::Initialized
    );
    assert_ne!(
        allocation
            .initialization()
            .classify(ByteRange::new(8, 16).unwrap()),
        InitializationClass::Initialized
    );
    assert!(
        !allocation
            .valid_value_bytes()
            .contains(ByteRange::new(8, 16).unwrap())
    );
}

#[test]
fn logical_initialization_is_invalidated_by_storage_loss_or_retirement() {
    let (mut input, def) = hidden();
    import(&mut input, &def, &WitnessArguments::default()).unwrap();
    for mutation in 0..5 {
        let mut changed = input.clone();
        let allocation = changed.allocation_mut(ALLOCATION).unwrap();
        let range = ByteRange::new(8, 16).unwrap();
        match mutation {
            0 => allocation.mark_uninitialized(range).unwrap(),
            1 => allocation.forget_initialization(range).unwrap(),
            2 => allocation.forget_validity(range).unwrap(),
            3 => allocation.mark_dead(),
            _ => allocation.set_liveness(LivenessState::MaybeLive),
        }
        assert_eq!(
            changed.closed_predicate_checks(),
            vec![(PredicateHolder(0), false)],
            "mutation {mutation}"
        );
    }
}

#[test]
fn ghost_constraints_cannot_replace_initialization_or_authority_at_a_fold() {
    let (input, def) = hidden();
    assert_eq!(
        transfer_predicate(&input, &def, 7, &explicit_effect(2)),
        Err(PredicateError::UnprovedRepresentation)
    );
    let mut missing = input.clone();
    missing.values.remove(&binding(0).permission);
    let before = missing.clone();
    assert!(import(&mut missing, &def, &WitnessArguments::default()).is_err());
    assert_eq!(missing, before);
}

#[test]
fn ghost_endpoints_follow_the_same_scope_transport_as_their_package() {
    let (mut input, def) = hidden();
    import(&mut input, &def, &WitnessArguments::default()).unwrap();
    let holders = [PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(7),
    }];
    let (frame, callee) = enter_predicate_call(&input, &holders).unwrap();
    assert_eq!(
        callee.closed_predicate_checks(),
        vec![(PredicateHolder(7), true)]
    );
    let returned = frame.resume(&callee, &holders).unwrap();
    assert_eq!(
        returned.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_ne!(
        returned.predicates[&PredicateHolder(0)].logic_scope,
        input.predicates[&PredicateHolder(0)].logic_scope
    );
}

#[test]
fn ghost_storage_evidence_does_not_match_another_array_geometry() {
    let (mut input, def) = hidden();
    import(&mut input, &def, &WitnessArguments::default()).unwrap();
    input
        .predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .definition
        .logical_prefixes[0]
        .array_offset = 8;
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
}

#[test]
fn revision_exhaustion_cannot_revive_old_storage_evidence() {
    let (mut input, def) = hidden();
    input
        .allocation_mut(ALLOCATION)
        .unwrap()
        .initialization_revision = Some(u64::MAX);
    import(&mut input, &def, &WitnessArguments::default()).unwrap();
    let allocation = input.allocation_mut(ALLOCATION).unwrap();
    allocation
        .forget_validity(ByteRange::new(8, 16).unwrap())
        .unwrap();
    assert_eq!(allocation.initialization_revision, None);
    allocation
        .mark_valid(ByteRange::new(8, 16).unwrap())
        .unwrap();
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
}

#[test]
fn a_catalog_entry_does_not_require_an_unused_uninitialized_field() {
    let (mut input, mut def) = hidden();
    def.logic_observations
        .insert((0, 8, VirMemoryAccess::core_u64()), LogicType::U64);
    import(&mut input, &def, &WitnessArguments::default()).unwrap();
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert!(
        input
            .allocation(ALLOCATION)
            .unwrap()
            .scalar_content(ByteRange::new(8, 16).unwrap(), VirMemoryAccess::core_u64())
            .is_none()
    );
}
