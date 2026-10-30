use super::*;

#[test]
fn checked_call_imports_match_loop_packages_by_actual_carriers() {
    let def = definition();
    let entry = fold(&state(), 0, 0).unwrap().output;
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    let mut returned = entry.clone();
    returned
        .export_predicate_interface(&def, &[binding(0)])
        .unwrap();
    returned
        .import_predicate_interface(&def, &[binding(0)], PredicateHolder(19))
        .unwrap();
    assert!(!returned.loop_resources_match(&entry, &[]));
    assert!(returned.loop_resources_match_with_predicates(
        &entry,
        &[binding(0).pointer, binding(0).permission],
        &repacked,
    ));
    let original = returned.clone();
    for mutation in 0..9 {
        let mut bad = returned.clone();
        let instance = bad.predicates.get_mut(&PredicateHolder(19)).unwrap();
        match mutation {
            0 => instance.resources[0].carrier = None,
            1 => instance.resources[0].carrier = Some(VirValueId::new(99)),
            2 => instance.resources[0].allocation = AbstractAllocationId::new(99),
            3 => {
                instance.resources[0].storage = Some((
                    AbstractAllocationId::new(0),
                    ResourcePayloadKey::new(0, VirMemoryAccess::core_u64()),
                ))
            }
            4 => instance.folded = false,
            5 => instance.definition.module += 1,
            6 => {
                bad.allocation_mut(AbstractAllocationId::new(0))
                    .unwrap()
                    .record_scalar_content(
                        ByteRange::new(0, 8).unwrap(),
                        VirMemoryAccess::core_u64(),
                        AbstractValue::U64(U64Interval::exact(9)),
                    );
            }
            7 => instance.opening_action = Some(7),
            _ => {
                let copy = instance.clone();
                bad.predicates.insert(PredicateHolder(20), copy);
            }
        }
        assert!(
            !bad.loop_resources_match_with_predicates(&entry, &[], &repacked),
            "mutation {mutation}"
        );
    }
    assert_eq!(returned, original, "matching must not alter either world");
}

#[test]
fn repacked_groups_match_bijectively_even_when_return_holder_numbers_swap() {
    let first = fold(&state(), 0, 0).unwrap().output;
    let mut entry = first.clone();
    let other_id = AbstractAllocationId::new(1);
    let mut other = state();
    let allocation = other
        .allocations
        .remove(&AbstractAllocationId::new(0))
        .unwrap();
    entry.define_allocation(other_id, allocation).unwrap();
    let old = entry.predicates[&PredicateHolder(0)].resources[0].clone();
    let pointer = AbstractPointer::new(
        AbstractProvenance::Known(other_id),
        U64Interval::exact(0),
        GuaranteedAlignment::new(8).unwrap(),
    )
    .with_memory_access(old.pointer.memory_access());
    let permission = AbstractPermission::new(
        AbstractProvenance::Known(other_id),
        old.permission.range(),
        AccessPermission::Write,
        FreeCapability::Yes,
    );
    entry
        .define_value(binding(10).pointer, AbstractValue::Pointer(pointer))
        .unwrap();
    entry
        .define_value(
            binding(10).permission,
            AbstractValue::Permission(permission),
        )
        .unwrap();
    entry = fold(&entry, 1, 10).unwrap().output;
    let mut returned = entry.clone();
    let a = returned.predicates.remove(&PredicateHolder(0)).unwrap();
    let b = returned.predicates.remove(&PredicateHolder(1)).unwrap();
    returned.predicates.insert(PredicateHolder(0), b);
    returned.predicates.insert(PredicateHolder(1), a);
    let repacked = BTreeSet::from([PredicateHolder(0), PredicateHolder(1)]);
    assert!(returned.loop_resources_match_with_predicates(&entry, &[], &repacked));
    assert!(!returned.loop_resources_match_with_predicates(
        &entry,
        &[],
        &BTreeSet::from([PredicateHolder(0)]),
    ));
    // Keep the number of packages unchanged while duplicating one real group.
    let duplicate = returned.predicates[&PredicateHolder(1)].clone();
    returned.predicates.insert(PredicateHolder(0), duplicate);
    assert!(!returned.loop_resources_match_with_predicates(&entry, &[], &repacked));
}
