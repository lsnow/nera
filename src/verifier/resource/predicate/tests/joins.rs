use super::*;
use crate::predicate_logic::*;

fn imported(def: &PredicateDefinition, epoch: u64, value: u64) -> ResourceState {
    let mut s = state();
    s.next_predicate_scope = epoch;
    s.allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .record_scalar_content(
            ByteRange::new(0, 8).unwrap(),
            VirMemoryAccess::core_u64(),
            AbstractValue::U64(U64Interval::exact(value)),
        );
    s.import_predicate_interface(def, &[binding(0)], PredicateHolder(0))
        .unwrap();
    s
}

fn imported_pair(epoch: u64, reverse: bool, holders: [u32; 2]) -> ResourceState {
    let mut s = state();
    s.next_predicate_scope = epoch;
    let id = AbstractAllocationId::new(1);
    s.define_allocation(
        id,
        s.allocation(AbstractAllocationId::new(0)).unwrap().clone(),
    )
    .unwrap();
    s.define_value(
        binding(10).pointer,
        AbstractValue::Pointer(
            AbstractPointer::new(
                AbstractProvenance::Known(id),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            )
            .with_memory_access(Some(VirMemoryAccess::core_u64())),
        ),
    )
    .unwrap();
    s.define_value(
        binding(10).permission,
        AbstractValue::Permission(AbstractPermission::new(
            AbstractProvenance::Known(id),
            AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
            AccessPermission::Write,
            FreeCapability::Yes,
        )),
    )
    .unwrap();
    for index in if reverse { [1, 0] } else { [0, 1] } {
        s.import_predicate_interface(
            &logical_definition(),
            &[binding(index as u32 * 10)],
            PredicateHolder(holders[index]),
        )
        .unwrap();
    }
    s
}

#[test]
fn joins_choose_one_whole_labeling_when_holders_and_binder_scopes_swap() {
    let a = imported_pair(0, false, [0, 1]);
    let b = imported_pair(0, true, [1, 0]);
    let c = imported_pair(20, true, [17, 9]);
    let before = (a.clone(), b.clone(), c.clone());
    let joined = a.join(&b).unwrap();
    assert_eq!(joined, b.join(&a).unwrap());
    assert_eq!(joined.predicates, a.predicates);
    assert_eq!(joined.predicates.len(), 2);
    assert_ne!(
        joined.predicates[&PredicateHolder(0)].logic_scope,
        joined.predicates[&PredicateHolder(1)].logic_scope
    );
    assert_eq!(joined.values, a.values);
    assert_eq!(joined.allocations, a.allocations);
    assert_eq!(joined.join(&b).unwrap(), joined);
    assert_eq!(joined.widen(&b).unwrap(), joined);
    assert_eq!(
        joined.join(&c).unwrap(),
        a.join(&b.join(&c).unwrap()).unwrap()
    );
    assert!(a.same_resource_facts(&b));
    assert!(a.same_loop_partition(&b));
    assert!(joined.covers_cfg_case(&a));
    assert!(joined.covers_cfg_case(&b));
    assert!(
        joined
            .closed_predicate_checks()
            .iter()
            .all(|(_, valid)| *valid)
    );
    assert_eq!((a, b, c), before);

    // Binder scopes alone may swap even when holder coordinates stay fixed.
    let swapped_scopes = imported_pair(0, true, [0, 1]);
    let result = before.0.join(&swapped_scopes).unwrap();
    assert_eq!(result, swapped_scopes.join(&before.0).unwrap());
    assert_ne!(
        result.predicates[&PredicateHolder(0)].logic_scope,
        result.predicates[&PredicateHolder(1)].logic_scope
    );

    use crate::verifier::guarded::{
        ConditionalResourceState, GuardedReduction, GuardedStateLimits,
    };
    let guarded = ConditionalResourceState::singleton(before.0)
        .join(
            &ConditionalResourceState::singleton(before.1),
            GuardedStateLimits {
                max_cases: 1,
                max_guard_atoms: 8,
            },
            GuardedReduction::Selective,
        )
        .unwrap();
    assert_eq!(guarded.cases().len(), 1);
    assert_eq!(guarded.cases()[0].predicate_instances().len(), 2);
}

#[test]
fn relabeling_never_changes_actual_resource_identity_or_restoration_obligations() {
    let a = imported_pair(0, false, [0, 1]);
    let b = imported_pair(9, true, [17, 9]);
    for mutation in 0..8 {
        let mut bad = b.clone();
        let instance = bad.predicates.get_mut(&PredicateHolder(17)).unwrap();
        match mutation {
            0 => instance.resources[0].carrier = Some(binding(10).permission),
            1 => instance.resources[0].carrier = None,
            2 => {
                instance.resources[0].pointer =
                    instance.resources[0].pointer.with_memory_access(None)
            }
            3 => {
                instance.resources[0].permission = AbstractPermission::new(
                    AbstractProvenance::Known(AbstractAllocationId::new(0)),
                    AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap()),
                    AccessPermission::Read,
                    FreeCapability::No,
                )
            }
            4 => instance.definition.module += 1,
            5 => instance.opening_action = Some(7),
            6 => instance.folded = false,
            _ => {
                let duplicate = bad.predicates[&PredicateHolder(9)].clone();
                bad.predicates.insert(PredicateHolder(17), duplicate);
            }
        }
        let before = bad.clone();
        assert_eq!(
            a.join(&bad),
            Err(ResourceJoinError::PredicateStateMismatch),
            "mutation {mutation}"
        );
        assert_eq!(
            bad.join(&a),
            Err(ResourceJoinError::PredicateStateMismatch),
            "mutation {mutation}"
        );
        assert_eq!(bad, before);
    }
    let open = unfold(&fold(&state(), 0, 0).unwrap().output, 0, 2)
        .unwrap()
        .output;
    assert_eq!(open.join(&open).unwrap(), open);
    let mut relabeled = open.clone();
    let instance = relabeled.predicates.remove(&PredicateHolder(0)).unwrap();
    relabeled.predicates.insert(PredicateHolder(9), instance);
    assert_eq!(
        open.join(&relabeled),
        Err(ResourceJoinError::PredicateStateMismatch)
    );
}

#[test]
fn stored_carriers_can_change_holder_but_must_keep_exact_typed_payload() {
    let mut a = imported(&logical_definition(), 0, 0);
    let storage = AbstractAllocationId::new(1);
    let key = ResourcePayloadKey::new(0, VirMemoryAccess::core_u64());
    let resource = a.predicates[&PredicateHolder(0)].resources[0].clone();
    a.define_allocation(storage, AbstractAllocation::new_local(16, 8).unwrap())
        .unwrap();
    assert!(a.store_predicate_carrier(binding(0).permission, storage, key));
    a.allocation_mut(storage)
        .unwrap()
        .set_resource_payload(
            key,
            MovePathState::available(TypedResourcePayload::new(
                resource.pointer,
                resource
                    .permission
                    .with_availability(PermissionAvailability::Consumed),
            )),
        )
        .unwrap();
    let mut b = a.clone();
    let instance = b.predicates.remove(&PredicateHolder(0)).unwrap();
    b.predicates.insert(PredicateHolder(19), instance);
    let joined = a.join(&b).unwrap();
    assert_eq!(joined, b.join(&a).unwrap());
    assert_eq!(joined.predicates, a.predicates);
    assert_eq!(
        joined.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_eq!(joined.allocations, a.allocations);
    for wrong_key in [
        ResourcePayloadKey::new(8, VirMemoryAccess::core_u64()),
        ResourcePayloadKey::new(
            0,
            VirMemoryAccess::new(crate::VirTypeId::new(1), crate::VirLayoutId::new(1)),
        ),
    ] {
        let mut bad = b.clone();
        bad.predicates
            .get_mut(&PredicateHolder(19))
            .unwrap()
            .resources[0]
            .storage = Some((storage, wrong_key));
        assert_eq!(a.join(&bad), Err(ResourceJoinError::PredicateStateMismatch));
    }
    b.allocation_mut(storage).unwrap().mark_dead();
    assert_eq!(a.join(&b), Err(ResourceJoinError::PredicateStateMismatch));
}

#[test]
fn closed_abstract_binders_join_by_alpha_equivalence_without_epoch_churn() {
    let mut def = logical_definition();
    def.logic.existentials.push(Existential {
        name: "enabled".into(),
        ty: LogicType::Bool,
        default: None,
    });
    def.logic.constraints.push(LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Bool,
            kind: LogicNodeKind::Binder(LogicBinder::Existential(1)),
        }],
        root: 0,
    });
    let a = imported(&def, 0, 0);
    let b = imported(&def, 17, 0);
    let before = (a.clone(), b.clone());
    assert_ne!(a.predicates, b.predicates);
    let joined = a.join(&b).unwrap();
    assert_eq!(joined, b.join(&a).unwrap());
    assert_eq!(joined.join(&a).unwrap(), joined);
    assert_eq!(joined.join(&b).unwrap(), joined);
    assert_eq!(joined.widen(&b).unwrap(), joined);
    assert_eq!(joined.next_predicate_scope, b.next_predicate_scope);
    assert_eq!(joined.allocations, a.allocations);
    assert_eq!(joined.values, a.values);
    assert_eq!(
        joined.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert!(joined.same_resource_facts(&b));
    assert!(joined.same_loop_partition(&b));
    assert!(joined.covers_cfg_case(&a));
    assert!(joined.covers_cfg_case(&b));
    assert_eq!((a, b), before);

    use crate::verifier::guarded::{
        ConditionalResourceState, GuardedReduction, GuardedStateLimits,
    };
    let limits = GuardedStateLimits {
        max_cases: 1,
        max_guard_atoms: 8,
    };
    let a = ConditionalResourceState::singleton(before.0);
    let b = ConditionalResourceState::singleton(before.1);
    let guarded = a.join(&b, limits, GuardedReduction::Selective).unwrap();
    assert_eq!(guarded.cases().len(), 1);
    assert_eq!(
        guarded.cases()[0].closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
}

#[test]
fn normalized_packages_are_rechecked_after_memory_join_and_widening() {
    let def = logical_definition();
    let a = imported(&def, 0, 0);
    let b = imported(&def, 9, 1);
    let joined = a.join(&b).unwrap();
    assert_eq!(
        joined.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    // Widening the stored word to u64::MAX loses the representation's <=8
    // guarantee. Bound-name equality is not permission to reinstall that fact.
    assert_eq!(
        a.widen(&joined),
        Err(ResourceJoinError::PredicateStateMismatch)
    );
    for change in 0..5 {
        let mut bad = b.clone();
        match change {
            0 => {
                bad.predicates
                    .get_mut(&PredicateHolder(0))
                    .unwrap()
                    .resources[0]
                    .carrier = None
            }
            1 => {
                bad.predicates
                    .get_mut(&PredicateHolder(0))
                    .unwrap()
                    .opening_action = Some(7)
            }
            2 => bad
                .allocation_mut(AbstractAllocationId::new(0))
                .unwrap()
                .mark_dead(),
            3 => {
                bad.values.remove(&binding(0).permission);
            }
            _ => bad.predicates.get_mut(&PredicateHolder(0)).unwrap().folded = false,
        }
        assert_eq!(
            a.join(&bad),
            Err(ResourceJoinError::PredicateStateMismatch),
            "change {change}"
        );
    }
}

#[test]
fn concrete_witnesses_foreign_captures_and_public_arguments_are_not_alpha_binders() {
    let def = logical_definition();
    let a = transfer_predicate(&state(), &def, 7, &explicit_effect(1))
        .unwrap()
        .output;
    let b = transfer_predicate(&state(), &def, 7, &explicit_effect(2))
        .unwrap()
        .output;
    let scope = a.predicates[&PredicateHolder(0)].logic_scope.unwrap();
    assert_ne!(
        logic::normalize_closed_scope(
            &a.predicates[&PredicateHolder(0)],
            scope,
            &mut LogicBudget::default()
        )
        .unwrap(),
        logic::normalize_closed_scope(
            &b.predicates[&PredicateHolder(0)],
            scope,
            &mut LogicBudget::default()
        )
        .unwrap(),
        "alpha-renaming alone does not forget concrete witnesses",
    );
    let a = imported(&def, 0, 0);
    let b = imported(&def, 9, 0);
    for atom in [
        logic::ObservationAtom::Captured {
            scope: b.predicates[&PredicateHolder(0)].logic_scope.unwrap(),
            value: VirValueId::new(99),
        },
        logic::ObservationAtom::Current {
            scope: b.predicates[&PredicateHolder(0)].logic_scope.unwrap(),
            value: VirValueId::new(99),
        },
    ] {
        let mut bad = b.clone();
        bad.predicates
            .get_mut(&PredicateHolder(0))
            .unwrap()
            .logical_witnesses[0]
            .value = LogicValue::Word(AffineValue::variable(atom, 0, 7).unwrap());
        assert!(
            logic::normalize_closed_scope(
                &bad.predicates[&PredicateHolder(0)],
                scope,
                &mut LogicBudget::default(),
            )
            .is_err(),
            "captured values cannot be identified by alpha-renaming"
        );
        // Their private values can instead be forgotten once the original
        // package's guarantee and real resources have been checked.
        assert_eq!(
            a.join(&bad).unwrap().closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
    }
    // Even a well-formed bound atom cannot serve as a public argument whose
    // identity is quietly changed by alpha-renaming the private binder.
    let mut instance = a.predicates[&PredicateHolder(0)].clone();
    instance
        .logical_parameters
        .push(instance.logical_witnesses[0].clone());
    let target = b.predicates[&PredicateHolder(0)].logic_scope.unwrap();
    assert!(logic::normalize_closed_scope(&instance, target, &mut LogicBudget::default()).is_err());
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert_eq!(
        logic::normalize_closed_scope(&a.predicates[&PredicateHolder(0)], target, &mut budget),
        Err(PredicateError::Budget)
    );
}

#[test]
fn scopes_cannot_be_renamed_when_another_package_retains_them() {
    let def = logical_definition();
    let mut a = imported(&def, 0, 0);
    let mut b = imported(&def, 9, 0);
    let mut observer = a.predicates[&PredicateHolder(0)].clone();
    observer.logic_scope = Some(InstanceScope {
        declaration: def.id.get(),
        instance: 20,
        opening: 0,
    });
    // Give the observing package genuinely separate storage and authority.
    // Its witness/facts deliberately retain the first package's old scope.
    let id = AbstractAllocationId::new(1);
    let pointer = AbstractPointer::new(
        AbstractProvenance::Known(id),
        U64Interval::exact(0),
        GuaranteedAlignment::new(8).unwrap(),
    )
    .with_memory_access(Some(VirMemoryAccess::core_u64()));
    let permission = AbstractPermission::new(
        AbstractProvenance::Known(id),
        AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
        AccessPermission::Write,
        FreeCapability::Yes,
    );
    observer.resources[0].allocation = id;
    observer.resources[0].pointer = pointer;
    observer.resources[0].permission = permission;
    observer.resources[0].carrier = Some(binding(10).permission);
    for input in [&mut a, &mut b] {
        input
            .define_allocation(
                id,
                state()
                    .allocation(AbstractAllocationId::new(0))
                    .unwrap()
                    .clone(),
            )
            .unwrap();
        input
            .define_value(binding(10).pointer, AbstractValue::Pointer(pointer))
            .unwrap();
        input
            .define_value(
                binding(10).permission,
                AbstractValue::Permission(
                    permission.with_availability(PermissionAvailability::Consumed),
                ),
            )
            .unwrap();
        input.next_predicate_scope = 21;
        input
            .predicates
            .insert(PredicateHolder(1), observer.clone());
        assert!(
            input
                .closed_predicate_checks()
                .iter()
                .all(|(_, valid)| *valid)
        );
    }
    assert_eq!(a.join(&b), Err(ResourceJoinError::PredicateStateMismatch));
    // The reference must be checked in each predecessor's own namespace,
    // excluding its matched holder, not the left predecessor's holder number.
    let selected = b.predicates.remove(&PredicateHolder(0)).unwrap();
    b.predicates.insert(PredicateHolder(7), selected);
    let observer = b.predicates.remove(&PredicateHolder(1)).unwrap();
    b.predicates.insert(PredicateHolder(9), observer);
    assert_eq!(a.join(&b), Err(ResourceJoinError::PredicateStateMismatch));
    assert_eq!(b.join(&a), Err(ResourceJoinError::PredicateStateMismatch));
}
