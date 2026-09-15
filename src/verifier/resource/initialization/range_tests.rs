use super::*;
use crate::{ByteSpan, SpannedVirInstruction, VirInstruction, transfer_instruction};

const ID: AbstractAllocationId = AbstractAllocationId::new(0);
const BEGIN: VirValueId = VirValueId::new(0);
const CURSOR: VirValueId = VirValueId::new(1);
const INDEX: VirValueId = VirValueId::new(2);
const POINTER: VirValueId = VirValueId::new(10);
const PERMISSION: VirValueId = VirValueId::new(11);
const VALUE: VirValueId = VirValueId::new(12);

fn key(begin: AffineExpression) -> ArrayKey {
    ArrayKey {
        base: 8,
        stride: 8,
        length: 8,
        element: VirMemoryAccess::core_u64(),
        begin,
    }
}

fn state(begin: AffineExpression, cursor: AffineExpression) -> ResourceState {
    let mut state = ResourceState::new();
    for (id, lower, upper) in [(BEGIN, 1, 2), (CURSOR, 3, 4), (INDEX, 3, 4)] {
        state
            .define_value(
                id,
                AbstractValue::U64(U64Interval::new(lower, upper).unwrap()),
            )
            .unwrap();
    }
    let mut allocation = AbstractAllocation::new_local(72, 8).unwrap();
    allocation
        .initialization_prefixes
        .facts
        .insert(key(begin), BTreeSet::from([begin, cursor]));
    state.define_allocation(ID, allocation).unwrap();
    state
}

fn dynamic() -> ResourceState {
    state(
        AffineExpression::identity(BEGIN),
        AffineExpression::identity(CURSOR),
    )
}

#[test]
fn loop_head_does_not_reinterpret_first_entry_prefix_using_havoced_roots() {
    let entry = dynamic();
    assert!(
        !entry.allocations[&ID]
            .initialization_prefixes
            .facts
            .is_empty()
    );
    for modified in [BTreeSet::new(), BTreeSet::from([ID])] {
        let mut head = ResourceState::new();
        assert!(head.inherit_loop_resources(&entry, &modified));
        assert!(
            head.allocations[&ID]
                .initialization_prefixes
                .facts
                .is_empty()
        );
    }
}

#[test]
fn inner_loop_retains_only_initialization_facts_with_unchanged_roots() {
    let entry = dynamic();
    for retained in [
        BTreeSet::new(),
        BTreeSet::from([BEGIN]),
        BTreeSet::from([BEGIN, CURSOR]),
    ] {
        let mut head = ResourceState::new();
        assert!(head.inherit_loop_resources(&entry, &BTreeSet::from([ID])));
        head.inherit_loop_initialization_frame(&entry, &retained);
        let facts = &head.allocations[&ID].initialization_prefixes.facts;
        if !retained.contains(&BEGIN) {
            assert!(facts.is_empty());
        } else {
            let counts = &facts[&key(AffineExpression::identity(BEGIN))];
            assert_eq!(
                counts.contains(&AffineExpression::identity(CURSOR)),
                retained.contains(&CURSOR)
            );
        }
    }
}

fn write(
    mut state: ResourceState,
    index: AffineExpression,
    mutate: impl FnOnce(&mut ResourceState),
) -> crate::InstructionTransfer {
    let expression = index
        .checked_scale(8)
        .unwrap()
        .checked_add_constant(8)
        .unwrap();
    let offset = expression
        .interval(|id| match state.value(id)? {
            AbstractValue::U64(value) => Some(*value),
            _ => None,
        })
        .unwrap();
    state
        .define_value(
            POINTER,
            AbstractValue::Pointer(
                AbstractPointer::new(
                    AbstractProvenance::Known(ID),
                    offset,
                    GuaranteedAlignment::new(8).unwrap(),
                )
                .with_offset_expression(Some(expression))
                .with_memory_access(Some(key(index).element)),
            ),
        )
        .unwrap();
    state
        .define_value(
            PERMISSION,
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(ID),
                AbstractByteRange::Exact(ByteRange::new(0, 72).unwrap()),
                AccessPermission::Write,
                FreeCapability::No,
            )),
        )
        .unwrap();
    state
        .define_value(VALUE, AbstractValue::U64(U64Interval::exact(42)))
        .unwrap();
    mutate(&mut state);
    transfer_instruction(
        &state,
        &SpannedVirInstruction {
            instruction: VirInstruction::Write {
                pointer: POINTER,
                permission: PERMISSION,
                value: VALUE,
                access: VirMemoryAccess::core_u64(),
            },
            source_span: ByteSpan::new(0, 1).unwrap(),
        },
    )
    .unwrap()
}

fn covers(state: &ResourceState, begin: AffineExpression, cursor: AffineExpression) -> bool {
    let Some(partition) = key(begin).partition(ID, cursor, &state.values) else {
        return false;
    };
    let range = partition.initialized;
    state.initialized_prefix_covers(
        ID,
        VirMemoryAccess::core_u64(),
        range,
        Default::default(),
        &Default::default(),
    )
}

#[test]
fn dynamic_origin_and_cursor_advance_only_after_proved_adjacent_canonical_write() {
    for equal in [false, true] {
        let mut input = dynamic();
        if equal {
            input.conjoin_path_fact(PathFact::comparison(
                VirIntegerPredicate::Equal,
                INDEX,
                CURSOR,
            ));
        }
        let out = write(input, AffineExpression::identity(INDEX), |_| {});
        assert!(out.all_obligations_proven(), "{:?}", out.obligations());
        let begin = AffineExpression::identity(BEGIN);
        let next = AffineExpression::identity(INDEX)
            .checked_add_constant(1)
            .unwrap();
        assert_eq!(covers(out.state(), begin, next), equal);
        assert!(covers(out.state(), AffineExpression::identity(INDEX), next));
        assert!(!covers(out.state(), AffineExpression::constant(0), next));
        let view = out
            .state()
            .initialization_partitions(ID, key(begin).element);
        let expected = key(begin).partition(ID, next, &out.state().values).unwrap();
        assert_eq!(view.contains(&expected), equal);
        assert_eq!(
            expected.initialized.bounds().unwrap().1,
            expected.remaining.bounds().unwrap().0
        );
        assert_eq!(
            expected.remaining.bounds().unwrap().1,
            SymbolicRangeBound::constant(72)
        );
    }
}

#[test]
fn concrete_write_sequences_preserve_updates_without_filling_skipped_elements() {
    for sequence in [[2, 3, 4, 3], [2, 4, 5, 2], [6, 5, 4, 3]] {
        let mut input = state(AffineExpression::constant(0), AffineExpression::constant(0));
        let mut initialized = [false; 8];
        for index in sequence {
            for value in [POINTER, PERMISSION, VALUE] {
                input.values.remove(&value);
            }
            let out = write(input, AffineExpression::constant(index), |_| {});
            assert!(out.all_obligations_proven());
            initialized[index as usize] = true;
            input = out.state().clone();
            for partition in input.initialization_partitions(ID, VirMemoryAccess::core_u64()) {
                let (begin, end) = partition.initialized.bounds().unwrap();
                let begin = (begin.interval().exact_value().unwrap() - 8) / 8;
                let end = (end.interval().exact_value().unwrap() - 8) / 8;
                assert!(
                    initialized[begin as usize..end as usize]
                        .iter()
                        .all(|value| *value)
                );
            }
        }
        assert!(!covers(
            &input,
            AffineExpression::constant(0),
            AffineExpression::constant(7)
        ));
    }
}

#[test]
fn storage_geometry_does_not_grant_authority_or_revive_a_different_allocation() {
    for mutation in 0..7 {
        let input = dynamic();
        assert!(
            !input
                .initialization_partitions(ID, key(AffineExpression::constant(0)).element)
                .is_empty()
        );
        let out = write(
            input,
            AffineExpression::identity(CURSOR),
            |state| match mutation {
                0..=3 => {
                    let AbstractValue::Permission(mut permission) = state.values[&PERMISSION]
                    else {
                        unreachable!()
                    };
                    match mutation {
                        0 => permission.availability = PermissionAvailability::Consumed,
                        1 => permission.access = AccessPermission::Read,
                        2 => permission.authority = PermissionAuthority::Unknown,
                        _ => {
                            permission.provenance =
                                AbstractProvenance::Known(AbstractAllocationId::new(1))
                        }
                    }
                    state
                        .values
                        .insert(PERMISSION, AbstractValue::Permission(permission));
                }
                4 => state.allocation_mut(ID).unwrap().mark_dead(),
                _ => {
                    let AbstractValue::Pointer(mut pointer) = state.values[&POINTER] else {
                        unreachable!()
                    };
                    pointer.provenance = if mutation == 5 {
                        AbstractProvenance::Unknown
                    } else {
                        AbstractProvenance::Known(AbstractAllocationId::new(1))
                    };
                    state
                        .values
                        .insert(POINTER, AbstractValue::Pointer(pointer));
                }
            },
        );
        assert!(!out.all_obligations_proven());
        let begin = AffineExpression::identity(BEGIN);
        let next = AffineExpression::identity(CURSOR)
            .checked_add_constant(1)
            .unwrap();
        assert!(!covers(out.state(), begin, next), "mutation {mutation}");
    }
}

#[test]
fn empty_one_past_and_overflow_do_not_imply_an_element_exists() {
    let empty = state(AffineExpression::constant(8), AffineExpression::constant(8));
    let view = empty.initialization_partitions(ID, VirMemoryAccess::core_u64());
    assert_eq!(view.len(), 1);
    assert_eq!(
        view[0].initialized,
        AbstractByteRange::Exact(ByteRange::new(72, 72).unwrap())
    );
    assert_eq!(view[0].remaining, view[0].initialized);
    let out = write(empty, AffineExpression::constant(8), |_| {});
    assert!(!out.all_obligations_proven());
    assert!(!covers(
        out.state(),
        AffineExpression::constant(7),
        AffineExpression::constant(8)
    ));
    let mut overflow = key(AffineExpression::constant(0));
    overflow.length = u64::MAX;
    assert!(
        overflow
            .partition(ID, AffineExpression::constant(0), &BTreeMap::new())
            .is_none()
    );
    overflow.length = 8;
    overflow.base = u64::MAX - 4;
    assert!(
        overflow
            .partition(ID, AffineExpression::constant(1), &BTreeMap::new())
            .is_none()
    );
    assert!(
        key(AffineExpression::identity(BEGIN))
            .partition(
                ID,
                AffineExpression::identity(CURSOR)
                    .checked_scale(u64::MAX)
                    .unwrap(),
                &dynamic().values
            )
            .is_none()
    );
}

#[test]
fn join_and_widen_intersect_both_origin_and_cursor_without_unioning_holes() {
    for a in 1..8 {
        for b in 1..8 {
            let left = state(AffineExpression::constant(1), AffineExpression::constant(a));
            let right = state(AffineExpression::constant(1), AffineExpression::constant(b));
            let joined = left.join(&right).unwrap();
            let widened = left.widen(&joined).unwrap();
            for result in [&joined, &widened] {
                for end in 2..=8 {
                    if covers(
                        result,
                        AffineExpression::constant(1),
                        AffineExpression::constant(end),
                    ) {
                        assert!(end <= a.min(b));
                    }
                }
            }
        }
    }
    let left = state(AffineExpression::constant(1), AffineExpression::constant(3));
    let right = state(AffineExpression::constant(4), AffineExpression::constant(6));
    assert!(
        left.join(&right)
            .unwrap()
            .initialization_partitions(ID, VirMemoryAccess::core_u64())
            .is_empty()
    );
    let mut other = dynamic();
    let allocation = other.allocations.remove(&ID).unwrap();
    other
        .allocations
        .insert(AbstractAllocationId::new(1), allocation);
    let joined = dynamic().join(&other).unwrap();
    assert!(
        joined
            .initialization_partitions(ID, VirMemoryAccess::core_u64())
            .is_empty()
    );
}

#[test]
fn ssa_projection_requires_the_origin_and_never_exports_before_begin() {
    let input = dynamic();
    let b = VirValueId::new(20);
    let c = VirValueId::new(21);
    let rename = [(BEGIN, b), (CURSOR, c)];
    let projected = input.project_cfg_edge(&rename);
    let facts = &projected.allocations[&ID].initialization_prefixes.facts;
    assert!(facts[&key(AffineExpression::identity(b))].contains(&AffineExpression::identity(c)));
    let missing = input.project_cfg_edge(&[(CURSOR, c)]);
    assert!(
        missing.allocations[&ID]
            .initialization_prefixes
            .facts
            .is_empty()
    );
    let mut below = state(AffineExpression::constant(3), AffineExpression::constant(5));
    below
        .values
        .insert(INDEX, AbstractValue::U64(U64Interval::exact(2)));
    let mut destination = below.project_cfg_edge(&[(INDEX, c)]);
    below.project_initialization_prefix_relations(
        &[(INDEX, c)],
        &mut destination,
        Default::default(),
        &Default::default(),
        false,
    );
    assert!(
        !destination.allocations[&ID].initialization_prefixes.facts
            [&key(AffineExpression::constant(3))]
            .contains(&AffineExpression::identity(c))
    );
}

#[test]
fn cyclic_edge_empty_candidates_preserve_duplicate_arguments_but_initialize_nothing() {
    let mut input = state(AffineExpression::constant(0), AffineExpression::constant(0));
    input
        .values
        .insert(INDEX, AbstractValue::U64(U64Interval::exact(2)));
    let start = VirValueId::new(20);
    let current = VirValueId::new(21);
    let renames = [(INDEX, start), (INDEX, current)];
    for seed_empty in [false, true] {
        let mut projected = input.project_cfg_edge(&renames);
        input.project_initialization_prefix_relations(
            &renames,
            &mut projected,
            Default::default(),
            &Default::default(),
            seed_empty,
        );
        let facts = &projected.allocations[&ID].initialization_prefixes.facts;
        let nonzero = key(AffineExpression::constant(2));
        assert_eq!(facts.contains_key(&nonzero), seed_empty);
        if seed_empty {
            assert!(facts[&nonzero].contains(&AffineExpression::identity(start)));
            assert!(facts[&nonzero].contains(&AffineExpression::identity(current)));
        }
        projected.reduce_initialization_prefixes();
        assert_eq!(
            projected.allocations[&ID]
                .initialization()
                .classify(ByteRange::new(0, 72).unwrap()),
            InitializationClass::Uninitialized
        );
    }
}

#[test]
fn invalidation_and_budget_forget_dynamic_facts_instead_of_fabricating_zero_origin() {
    for mutation in 0..6 {
        let mut input = dynamic();
        let allocation = input.allocation_mut(ID).unwrap();
        let overlap = ByteRange::new(24, 32).unwrap();
        match mutation {
            0 => allocation.mark_uninitialized(overlap).unwrap(),
            1 => allocation.forget_initialization(overlap).unwrap(),
            2 => allocation.forget_validity(overlap).unwrap(),
            3 => allocation.forget_uninitialized(overlap).unwrap(),
            4 => allocation.mark_dead(),
            _ => allocation.set_liveness(LivenessState::MaybeLive),
        }
        input.reduce_initialization_prefixes();
        assert!(!covers(
            &input,
            AffineExpression::identity(BEGIN),
            AffineExpression::identity(CURSOR)
        ));
        if mutation >= 4 {
            assert!(
                input.allocations[&ID]
                    .initialization_prefixes
                    .facts
                    .is_empty()
            );
        }
    }
    let begin = AffineExpression::identity(BEGIN);
    let mut counts = (0..=MAX_EQUIVALENT_COUNTS as u64)
        .map(AffineExpression::constant)
        .collect();
    limit_counts_from(&mut counts, begin);
    assert_eq!(counts, BTreeSet::from([begin]));
}
