use super::*;

fn frame(entry: &ResourceState) -> ResourceState {
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    let modified = BTreeSet::from([AbstractAllocationId::new(0)]);
    let mut head = ResourceState::new();
    assert!(head.inherit_loop_resources_with_predicates(entry, &modified, &repacked));
    for (id, value) in &entry.values {
        head.define_value(*id, *value).unwrap();
    }
    head.abstract_loop_predicates_after_havoc(entry, &modified, &repacked)
        .unwrap();
    head
}

#[test]
fn written_package_heads_keep_declared_bounds_not_entry_contents() {
    let entry = fold(&state(), 0, 0).unwrap().output;
    let head = frame(&entry);
    let id = AbstractAllocationId::new(0);
    let cell = ByteRange::new(0, 8).unwrap();
    let access = VirMemoryAccess::core_u64();
    assert_eq!(
        head.allocation(id).unwrap().scalar_content(cell, access),
        Some(AbstractValue::U64(U64Interval::new(0, 8).unwrap()))
    );
    assert_eq!(head.values, entry.values);
    assert_eq!(head.loans, entry.loans);
    assert_eq!(
        head.allocation(id).unwrap().scalar_origin(cell, access),
        None
    );
    let open = transfer_predicate(
        &head,
        &definition(),
        7,
        &PredicateEffect::UnfoldInPlace {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
        },
    )
    .unwrap()
    .output;
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    for value in [1, 8] {
        let mut updated = open.clone();
        updated.allocation_mut(id).unwrap().record_scalar_content(
            cell,
            access,
            AbstractValue::U64(U64Interval::exact(value)),
        );
        assert!(!updated.loop_resources_match_with_predicates(&entry, &[], &repacked));
        let closed = fold(&updated, 0, 0).unwrap().output;
        assert!(closed.loop_resources_match_with_predicates(
            &entry,
            &[binding(0).pointer, binding(0).permission],
            &repacked
        ));
    }
    let mut bad = open.clone();
    bad.allocation_mut(id).unwrap().record_scalar_content(
        cell,
        access,
        AbstractValue::U64(U64Interval::exact(9)),
    );
    assert!(fold(&bad, 0, 0).is_err());
    // A stale sealed record is not evidence for the changed representation.
    let mut stale = head.clone();
    stale.allocation_mut(id).unwrap().record_scalar_content(
        cell,
        access,
        AbstractValue::U64(U64Interval::exact(9)),
    );
    assert!(!stale.loop_resources_match_with_predicates(&entry, &[], &repacked));
}

#[test]
fn loop_representation_admission_requires_actual_entry_and_is_atomic() {
    let entry = fold(&state(), 0, 0).unwrap().output;
    let id = AbstractAllocationId::new(0);
    let modified = BTreeSet::from([id]);
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    for mutation in 0..6 {
        let mut bad = entry.clone();
        match mutation {
            0 => {
                bad.values.remove(&binding(0).permission);
            }
            1 => {
                let p = bad.predicates[&PredicateHolder(0)].resources[0].permission;
                *bad.value_mut(binding(0).permission).unwrap() = AbstractValue::Permission(p);
            }
            2 => bad.allocation_mut(id).unwrap().mark_dead(),
            3 => bad
                .allocation_mut(id)
                .unwrap()
                .mark_uninitialized(ByteRange::new(0, 8).unwrap())
                .unwrap(),
            4 => bad.allocation_mut(id).unwrap().record_scalar_content(
                ByteRange::new(0, 8).unwrap(),
                VirMemoryAccess::core_u64(),
                AbstractValue::U64(U64Interval::exact(9)),
            ),
            _ => {
                bad.predicates
                    .get_mut(&PredicateHolder(0))
                    .unwrap()
                    .resources[0]
                    .carrier = None
            }
        }
        let mut head = ResourceState::new();
        let original = head.clone();
        assert!(
            !head.inherit_loop_resources_with_predicates(&bad, &modified, &repacked),
            "mutation {mutation}"
        );
        assert_eq!(head, original);
    }
    let mut head = ResourceState::new();
    assert!(!head.inherit_loop_resources_with_predicates(&entry, &modified, &BTreeSet::new()));
    assert_eq!(head, ResourceState::new());
}

#[test]
fn induction_prefix_is_relative_to_the_current_count_not_its_upper_bound() {
    let mut def = definition();
    def.scalar_constraints[0].upper = 1;
    let prefix = HeapInitializationPrefix {
        array_offset: 8,
        element: VirMemoryAccess::core_u64(),
        length: 1,
        stride: 8,
        count_offset: 0,
        count_access: VirMemoryAccess::core_u64(),
    };
    def.initialized_prefixes.push((0, prefix));
    let effect = PredicateEffect::Fold {
        holder: PredicateHolder(0),
        bindings: vec![binding(0)],
    };
    let entry = transfer_predicate(&state(), &def, 7, &effect)
        .unwrap()
        .output;
    let head = frame(&entry);
    let id = AbstractAllocationId::new(0);
    let array = ByteRange::new(8, 16).unwrap();
    let count = ByteRange::new(0, 8).unwrap();
    assert!(head.allocation(id).unwrap().heap_prefix_valid(prefix));
    assert_ne!(
        head.allocation(id)
            .unwrap()
            .initialization()
            .classify(array),
        InitializationClass::Initialized
    );
    assert!(
        !head
            .allocation(id)
            .unwrap()
            .valid_value_bytes()
            .contains(array)
    );
    let mut opened = transfer_predicate(
        &head,
        &def,
        7,
        &PredicateEffect::UnfoldInPlace {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
        },
    )
    .unwrap()
    .output;
    opened.allocation_mut(id).unwrap().record_scalar_content(
        count,
        prefix.count_access,
        AbstractValue::U64(U64Interval::exact(1)),
    );
    assert!(!opened.allocation(id).unwrap().heap_prefix_valid(prefix));
    assert!(transfer_predicate(&opened, &def, 7, &effect).is_err());
    opened
        .allocation_mut(id)
        .unwrap()
        .mark_initialized(array)
        .unwrap();
    opened
        .allocation_mut(id)
        .unwrap()
        .mark_valid(array)
        .unwrap();
    let closed = transfer_predicate(&opened, &def, 7, &effect)
        .unwrap()
        .output;
    assert!(closed.loop_resources_match_with_predicates(
        &entry,
        &[],
        &BTreeSet::from([PredicateHolder(0)])
    ));
}

#[test]
fn post_havoc_abstraction_cannot_import_from_a_different_package() {
    let entry = fold(&state(), 0, 0).unwrap().output;
    let mut head = frame(&entry);
    head.predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .definition
        .scalar_constraints[0]
        .upper = 9;
    let original = head.clone();
    assert!(
        head.abstract_loop_predicates_after_havoc(
            &entry,
            &BTreeSet::from([AbstractAllocationId::new(0)]),
            &BTreeSet::from([PredicateHolder(0)])
        )
        .is_err()
    );
    assert_eq!(head, original);
}

#[test]
fn written_projected_witnesses_observe_the_arbitrary_head_not_entry_memory() {
    use crate::predicate_logic::LogicValue;
    let mut def = snapshot_equality_definition();
    // No asserted relation between the snapshot and subsequent observations.
    // Such a relation needs an actual stable origin, not just the same address.
    def.logic.constraints.clear();
    def.projected_witnesses.insert(0);
    let fold = PredicateEffect::Fold {
        holder: PredicateHolder(0),
        bindings: vec![binding(0)],
    };
    let entry = transfer_predicate(&state(), &def, 7, &fold).unwrap().output;
    let head = frame(&entry);
    let LogicValue::Word(word) = &head.predicates[&PredicateHolder(0)].logical_witnesses[0].value
    else {
        panic!("word witness");
    };
    assert_eq!((word.lower, word.upper), (0, u64::MAX));
    assert_eq!(
        head.allocation(AbstractAllocationId::new(0))
            .unwrap()
            .scalar_content(ByteRange::new(0, 8).unwrap(), VirMemoryAccess::core_u64()),
        Some(AbstractValue::U64(U64Interval::unknown()))
    );
    let mut opened = transfer_predicate(
        &head,
        &def,
        7,
        &PredicateEffect::UnfoldInPlace {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
        },
    )
    .unwrap()
    .output;
    opened
        .allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .record_scalar_content(
            ByteRange::new(0, 8).unwrap(),
            VirMemoryAccess::core_u64(),
            AbstractValue::U64(U64Interval::exact(5)),
        );
    let closed = transfer_predicate(&opened, &def, 7, &fold).unwrap().output;
    assert!(closed.loop_resources_match_with_predicates(
        &entry,
        &[],
        &BTreeSet::from([PredicateHolder(0)])
    ));
}

#[test]
fn arbitrary_field_snapshots_do_not_gain_identity_from_an_address() {
    let mut def = snapshot_equality_definition();
    def.projected_witnesses.insert(0);
    let mut input = state();
    input
        .allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .record_scalar_content(
            ByteRange::new(0, 8).unwrap(),
            VirMemoryAccess::core_u64(),
            AbstractValue::U64(U64Interval::unknown()),
        );
    input.seed_scalar_origins();
    let entry = transfer_predicate(
        &input,
        &def,
        7,
        &PredicateEffect::Fold {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
        },
    )
    .unwrap()
    .output;
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    let modified = BTreeSet::from([AbstractAllocationId::new(0)]);
    let mut head = ResourceState::new();
    assert!(head.inherit_loop_resources_with_predicates(&entry, &modified, &repacked));
    for (id, value) in &entry.values {
        head.define_value(*id, *value).unwrap();
    }
    let mut exhausted = head.clone();
    exhausted.next_predicate_scope = u64::MAX;
    let original = exhausted.clone();
    assert!(
        exhausted
            .abstract_loop_predicates_after_havoc(&entry, &modified, &repacked)
            .is_err()
    );
    assert_eq!(
        exhausted, original,
        "failed abstraction cannot leave cell origins"
    );
    head.abstract_loop_predicates_after_havoc(&entry, &modified, &repacked)
        .unwrap();
    let cell = ByteRange::new(0, 8).unwrap();
    let id = AbstractAllocationId::new(0);
    let access = VirMemoryAccess::core_u64();
    let origin = head
        .allocation(id)
        .unwrap()
        .scalar_origin(cell, access)
        .unwrap();
    assert!(matches!(origin.first.root, ScalarOriginRoot::Snapshot(_)));
    assert_ne!(
        Some(origin),
        entry.allocation(id).unwrap().scalar_origin(cell, access),
        "induction values cannot become entry memory coordinates"
    );
    assert!(head.predicate_representation_valid(&head.predicates[&PredicateHolder(0)]));
    // The same unknown interval at the same address after a write has no
    // relation to the immutable captured value. The write retires the origin.
    head.allocation_mut(id).unwrap().record_scalar_content(
        cell,
        access,
        AbstractValue::U64(U64Interval::unknown()),
    );
    assert_eq!(
        head.allocation(id).unwrap().scalar_origin(cell, access),
        None
    );
    assert!(!head.predicate_representation_valid(&head.predicates[&PredicateHolder(0)]));
    // A real copy of the saved value may restore that precise identity.
    head.allocation_mut(id)
        .unwrap()
        .set_scalar_origin(cell, access, origin);
    assert!(head.predicate_representation_valid(&head.predicates[&PredicateHolder(0)]));
}

#[test]
fn hidden_defaults_are_not_observed_at_the_induction_head() {
    use crate::predicate_logic::*;
    let mut def = logical_definition();
    def.logic_observations
        .insert((0, 8, VirMemoryAccess::core_u64()), LogicType::Usize);
    def.logic.existentials[0].default = Some(LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Usize,
            kind: LogicNodeKind::Observe {
                resource: 0,
                offset: 8,
                access: VirMemoryAccess::core_u64(),
                time: ObservationTime::Current,
            },
        }],
        root: 0,
    });
    let entry = transfer_predicate(&state(), &def, 7, &explicit_effect(6))
        .unwrap()
        .output;
    let head = frame(&entry);
    let allocation = head.allocation(AbstractAllocationId::new(0)).unwrap();
    let cell = ByteRange::new(8, 16).unwrap();
    assert_ne!(
        allocation.initialization().classify(cell),
        InitializationClass::Initialized
    );
    assert!(
        allocation
            .scalar_content(cell, VirMemoryAccess::core_u64())
            .is_none()
    );
    assert!(head.predicate_representation_valid(&head.predicates[&PredicateHolder(0)]));
}
