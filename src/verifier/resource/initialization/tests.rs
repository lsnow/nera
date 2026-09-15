use super::*;

fn key() -> ArrayKey {
    ArrayKey {
        base: 8,
        stride: 8,
        length: 4,
        element: VirMemoryAccess::core_u64(),
        begin: AffineExpression::constant(0),
    }
}

#[test]
fn relational_prefix_queries_match_a_concrete_byte_oracle_without_mutating_state() {
    let n = VirValueId::new(0);
    let j = VirValueId::new(1);
    let id = AbstractAllocationId::new(0);
    for predicate in [
        VirIntegerPredicate::LessThan,
        VirIntegerPredicate::LessOrEqual,
        VirIntegerPredicate::NotEqual,
    ] {
        let mut state = ResourceState::new();
        state
            .define_value(n, AbstractValue::U64(U64Interval::new(1, 4).unwrap()))
            .unwrap();
        state
            .define_value(j, AbstractValue::U64(U64Interval::new(0, 3).unwrap()))
            .unwrap();
        state.conjoin_path_fact(PathFact::comparison(predicate, j, n));
        let mut allocation = AbstractAllocation::new_local(40, 8).unwrap();
        allocation.initialization_prefixes = prefixes([AffineExpression::identity(n)]);
        state.define_allocation(id, allocation).unwrap();
        for width in [0, 8, 16] {
            let start = SymbolicRangeBound::new(
                AffineExpression::identity(j)
                    .checked_scale(8)
                    .unwrap()
                    .checked_add_constant(8)
                    .unwrap(),
                U64Interval::new(8, 32).unwrap(),
            );
            let range =
                AbstractByteRange::from_bounds(start, start.checked_add_constant(width).unwrap());
            let before = state.clone();
            let proven = state.initialized_prefix_covers(
                id,
                key().element,
                range,
                Default::default(),
                &Default::default(),
            );
            assert_eq!(state, before);
            if predicate == VirIntegerPredicate::LessThan && width <= 8 {
                assert!(proven);
            }
            for count in 1..=4 {
                for index in 0..4 {
                    let premise = match predicate {
                        VirIntegerPredicate::LessThan => index < count,
                        VirIntegerPredicate::LessOrEqual => index <= count,
                        _ => index != count,
                    };
                    if premise && proven {
                        assert!(8 + 8 * index + width <= 8 + 8 * count);
                    }
                }
            }
        }
        let range = AbstractByteRange::Exact(ByteRange::new(8, 16).unwrap());
        assert!(state.initialized_prefix_covers(
            id,
            key().element,
            range,
            Default::default(),
            &Default::default()
        ));
        state
            .allocation_mut(id)
            .unwrap()
            .forget_validity(ByteRange::new(8, 16).unwrap())
            .unwrap();
        assert!(!state.initialized_prefix_covers(
            id,
            key().element,
            range,
            Default::default(),
            &Default::default()
        ));
    }
}

#[test]
fn edge_prefix_export_requires_a_relation_on_that_predecessor() {
    let i = VirValueId::new(0);
    let n = VirValueId::new(1);
    let target = VirValueId::new(2);
    let id = AbstractAllocationId::new(0);
    let mut state = ResourceState::new();
    for value in [i, n] {
        state
            .define_value(value, AbstractValue::U64(U64Interval::new(0, 4).unwrap()))
            .unwrap();
    }
    let mut allocation = AbstractAllocation::new_local(40, 8).unwrap();
    allocation.initialization_prefixes = prefixes([AffineExpression::identity(i)]);
    state.define_allocation(id, allocation).unwrap();
    let renames = [(n, target)];
    let project = |state: &ResourceState| {
        let mut projected = state.project_cfg_edge(&renames);
        state.project_initialization_prefix_relations(
            &renames,
            &mut projected,
            Default::default(),
            &Default::default(),
            false,
        );
        projected
    };
    let missing = project(&state);
    assert!(
        !missing.allocations[&id].initialization_prefixes.facts[&key()]
            .contains(&AffineExpression::identity(target))
    );
    state.conjoin_path_fact(PathFact::comparison(VirIntegerPredicate::LessOrEqual, n, i));
    let proved = project(&state);
    assert!(
        proved.allocations[&id].initialization_prefixes.facts[&key()]
            .contains(&AffineExpression::identity(target))
    );
    let joined = proved.join(&missing).unwrap();
    assert!(
        !joined.allocations[&id].initialization_prefixes.facts[&key()]
            .contains(&AffineExpression::identity(target))
    );
}

fn prefixes(counts: impl IntoIterator<Item = AffineExpression>) -> InitializationPrefixes {
    InitializationPrefixes {
        facts: BTreeMap::from([(key(), counts.into_iter().collect())]),
    }
}

#[test]
fn joins_keep_only_predecessor_independent_facts() {
    for a in 0..=4 {
        for b in 0..=4 {
            let left = prefixes((0..=a).map(AffineExpression::constant));
            let right = prefixes((0..=b).map(AffineExpression::constant));
            let joined = left.join(&right);
            assert_eq!(joined, right.join(&left));
            assert_eq!(left.join(&left), left);
            assert_eq!(
                joined.facts[&key()]
                    .iter()
                    .map(|count| count.addend())
                    .max(),
                Some(a.min(b))
            );
        }
    }
}

#[test]
fn projection_preserves_latch_equalities_without_trusting_loop_metadata() {
    let source = VirValueId::new(1);
    let target = VirValueId::new(2);
    for value in 0..4 {
        let mut state = ResourceState::default();
        state
            .define_value(source, AbstractValue::U64(U64Interval::exact(value)))
            .unwrap();
        let remapper = ExpressionRemapper::new(&state, &[(source, target)]);
        let fact = prefixes([AffineExpression::constant(value + 1)]);
        let projected = fact.project(&remapper, &state.values);
        assert!(
            projected.facts[&key()].contains(
                &AffineExpression::identity(target)
                    .checked_add_constant(1)
                    .unwrap()
            )
        );
        let values = BTreeMap::from([(target, AbstractValue::U64(U64Interval::exact(value)))]);
        for count in &projected.facts[&key()] {
            assert!(interval(*count, &values).unwrap().lower() <= value + 1);
        }
    }
}

#[test]
fn invalidation_cannot_resurrect_valid_or_initialized_bytes() {
    for kind in 0..4 {
        let mut allocation = AbstractAllocation::new_local(40, 8).unwrap();
        allocation.initialization_prefixes = prefixes([AffineExpression::constant(4)]);
        allocation.reduce_initialization_prefixes(&BTreeMap::new());
        let range = ByteRange::new(16, 24).unwrap();
        match kind {
            0 => allocation.mark_uninitialized(range).unwrap(),
            1 => allocation.forget_initialization(range).unwrap(),
            2 => allocation.forget_validity(range).unwrap(),
            _ => allocation.forget_uninitialized(range).unwrap(),
        }
        assert_eq!(
            allocation.initialization_prefixes.facts[&key()],
            empty_prefix()
        );
        let before = allocation.clone();
        allocation.reduce_initialization_prefixes(&BTreeMap::new());
        assert_eq!(allocation, before);
    }
    let mut facts = prefixes([AffineExpression::constant(4)]);
    facts.invalidate(ByteRange::new(0, 8).unwrap());
    assert!(facts.facts[&key()].contains(&AffineExpression::constant(4)));
}

#[test]
fn overflow_and_alias_budget_only_lose_precision() {
    let root = VirValueId::new(1);
    let count = AffineExpression::identity(root)
        .checked_add_constant(1)
        .unwrap();
    let values = BTreeMap::from([(root, AbstractValue::U64(U64Interval::exact(u64::MAX)))]);
    assert!(interval(count, &values).is_none());
    let mut counts = (0..=MAX_EQUIVALENT_COUNTS as u64)
        .map(AffineExpression::constant)
        .collect();
    limit_counts(&mut counts);
    assert_eq!(counts, empty_prefix());
}

#[test]
fn prefix_key_budget_does_not_initialize_untracked_arrays() {
    let length = MAX_PREFIXES + 1;
    let output = crate::analyze(&crate::SourceFile::from_text(
        "prefix-budget.nera",
        format!("fn main() -> u64 {{ let mut arrays: [[u64; 1]; {length}]; return 0; }}"),
    ));
    let unit = output.vir().unwrap().as_unit();
    let access = unit.runtime.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .find_map(|i| match i.instruction {
            crate::VirInstruction::StorageReset { access, .. } => Some(access),
            _ => None,
        })
        .unwrap();
    let shape = unit.memory.object_shape(access).unwrap();
    let mut allocation =
        AbstractAllocation::new_local(shape.size_bytes(), shape.alignment()).unwrap();
    allocation.seed_initialization_prefixes(&unit.memory, &shape);
    assert_eq!(allocation.initialization_prefixes.facts.len(), MAX_PREFIXES);
    for counts in allocation.initialization_prefixes.facts.values_mut() {
        *counts = BTreeSet::from([AffineExpression::constant(1)]);
    }
    allocation.reduce_initialization_prefixes(&BTreeMap::new());
    assert_eq!(
        allocation
            .initialization()
            .classify(ByteRange::new(0, (MAX_PREFIXES * 8) as u64).unwrap()),
        InitializationClass::Initialized
    );
    let untracked = ByteRange::new((MAX_PREFIXES * 8) as u64, (length * 8) as u64).unwrap();
    assert_eq!(
        allocation.initialization().classify(untracked),
        InitializationClass::Uninitialized
    );
    assert!(!allocation.valid_value_bytes().contains(untracked));
}
