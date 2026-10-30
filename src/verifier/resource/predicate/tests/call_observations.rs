use super::*;

fn observed_package(
    boolean: bool,
) -> (
    ResourceState,
    PredicateDefinition,
    VirMemoryAccess,
    ByteRange,
) {
    use crate::predicate_logic::*;
    let mut def = snapshot_equality_definition();
    let access = if boolean {
        VirMemoryAccess::new(crate::VirTypeId::new(90), crate::VirLayoutId::new(90))
    } else {
        VirMemoryAccess::core_u64()
    };
    let ty = if boolean {
        LogicType::Bool
    } else {
        LogicType::U64
    };
    def.logic_observations.clear();
    def.logic_observations.insert((0, 0, access), ty);
    def.logic.existentials[0].ty = ty;
    for expression in def.logic.existentials[0]
        .default
        .iter_mut()
        .chain(&mut def.logic.constraints)
    {
        for node in &mut expression.nodes {
            if !matches!(node.kind, LogicNodeKind::Equal(..)) {
                node.ty = ty;
            }
            if let LogicNodeKind::Observe { access: old, .. } = &mut node.kind {
                *old = access;
            }
        }
    }
    let bytes = ByteRange::new(0, if boolean { 1 } else { 8 }).unwrap();
    let mut input = state();
    input
        .allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .record_scalar_content(
            bytes,
            access,
            if boolean {
                AbstractValue::Bool(AbstractBool::Unknown)
            } else {
                AbstractValue::U64(U64Interval::new(0, 8).unwrap())
            },
        );
    input.seed_scalar_origins();
    let sealed = transfer_predicate(
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
    (sealed, def, access, bytes)
}

#[test]
fn alpha_join_requires_shared_word_and_bool_histories_not_equal_intervals() {
    for boolean in [false, true] {
        let (mut available, def, access, bytes) = observed_package(boolean);
        available
            .export_predicate_interface(&def, &[binding(0)])
            .unwrap();
        let mut left = available.clone();
        let mut right = available.clone();
        left.next_predicate_scope = 10;
        right.next_predicate_scope = 20;
        left.import_predicate_interface(&def, &[binding(0)], PredicateHolder(0))
            .unwrap();
        right
            .import_predicate_interface(&def, &[binding(0)], PredicateHolder(0))
            .unwrap();
        let joined = left.join(&right).unwrap();
        assert_eq!(joined, right.join(&left).unwrap());
        assert_eq!(
            joined.closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
        let unknown = if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::new(0, 8).unwrap())
        };
        available
            .allocation_mut(AbstractAllocationId::new(0))
            .unwrap()
            .record_scalar_content(bytes, access, unknown);
        available.next_predicate_scope = 20;
        available
            .import_predicate_interface(&def, &[binding(0)], PredicateHolder(0))
            .unwrap();
        assert_eq!(
            available.closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
        assert_eq!(
            left.join(&available),
            Err(ResourceJoinError::PredicateStateMismatch)
        );
        assert_eq!(
            left.widen(&available),
            Err(ResourceJoinError::PredicateStateMismatch)
        );
    }
}

#[test]
fn ordinary_checked_postconditions_bind_unknown_current_cells_to_fresh_snapshots() {
    for boolean in [false, true] {
        let (entry, def, access, bytes) = observed_package(boolean);
        let id = AbstractAllocationId::new(0);
        let unknown = if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::new(0, 8).unwrap())
        };
        let mut returned = entry.clone();
        returned
            .export_predicate_interface(&def, &[binding(0)])
            .unwrap();
        // A checked body has changed the field. Its old numeric interval is
        // retained, but its old contents/origin cannot be reused at the caller.
        returned
            .allocation_mut(id)
            .unwrap()
            .record_scalar_content(bytes, access, unknown);
        let actual_memory = returned.allocation(id).unwrap().clone();
        assert_eq!(actual_memory.scalar_origin(bytes, access), None);
        assert_eq!(actual_memory.bool_origin(bytes, access), None);
        returned
            .import_predicate_interface(&def, &[binding(0)], PredicateHolder(19))
            .unwrap();
        assert_eq!(
            returned.closed_predicate_checks(),
            vec![(PredicateHolder(19), true)]
        );
        let allocation = returned.allocation(id).unwrap();
        assert_eq!(allocation.scalar_content(bytes, access), Some(unknown));
        assert_eq!(allocation.initialization(), actual_memory.initialization());
        if boolean {
            assert!(matches!(
                allocation.bool_origin(bytes, access),
                Some(BoolOrigin::Snapshot(_))
            ));
        } else {
            assert!(matches!(
                allocation.scalar_origin(bytes, access).unwrap().first.root,
                ScalarOriginRoot::Snapshot(_)
            ));
        }
        let repacked = BTreeSet::from([PredicateHolder(0)]);
        assert!(returned.loop_resources_match_with_predicates(&entry, &[], &repacked));
        let mut changed = returned.clone();
        changed
            .allocation_mut(id)
            .unwrap()
            .record_scalar_content(bytes, access, unknown);
        assert_eq!(
            changed.closed_predicate_checks(),
            vec![(PredicateHolder(19), false)]
        );
        assert!(!changed.loop_resources_match_with_predicates(&entry, &[], &repacked));

        let mut exported = returned.clone();
        exported
            .export_predicate_interface(&def, &[binding(0)])
            .unwrap();
        exported.next_predicate_scope = u64::MAX;
        let original = exported.clone();
        assert!(
            exported
                .import_predicate_interface(&def, &[binding(0)], PredicateHolder(20))
                .is_err()
        );
        assert_eq!(exported, original);
    }
}

#[test]
fn actual_word_and_bool_histories_survive_repeated_call_roundtrips() {
    for boolean in [false, true] {
        let (mut caller, def, access, bytes) = observed_package(boolean);
        let mapping = PredicateCallBinding {
            caller: PredicateHolder(0),
            callee: PredicateHolder(7),
        };
        let id = AbstractAllocationId::new(0);
        let origin = |s: &ResourceState| {
            let a = s.allocation(id).unwrap();
            (a.scalar_origin(bytes, access), a.bool_origin(bytes, access))
        };
        for _ in 0..2 {
            let before = caller.clone();
            let old = origin(&caller);
            let (frame, callee) = enter_predicate_call(&caller, &[mapping]).unwrap();
            assert_eq!(caller, before);
            assert!(callee.values().is_empty());
            assert_ne!(origin(&callee), old);
            assert_eq!(
                callee.closed_predicate_checks(),
                vec![(PredicateHolder(7), true)]
            );
            let opened = transfer_predicate(
                &callee,
                &def,
                7,
                &PredicateEffect::Unfold {
                    holder: PredicateHolder(7),
                    outputs: vec![binding(10)],
                },
            )
            .unwrap()
            .output;
            let closed = transfer_predicate(
                &opened,
                &def,
                7,
                &PredicateEffect::Fold {
                    holder: PredicateHolder(7),
                    bindings: vec![binding(10)],
                },
            )
            .unwrap()
            .output;
            caller = frame.resume(&closed, &[mapping]).unwrap();
            assert_ne!(origin(&caller), origin(&callee));
            assert_ne!(origin(&caller), old);
            assert_eq!(
                caller.closed_predicate_checks(),
                vec![(PredicateHolder(0), true)]
            );
            assert_eq!(caller.values(), before.values());
            assert_eq!(
                caller.allocation(id).unwrap().initialization(),
                before.allocation(id).unwrap().initialization()
            );
            assert_eq!(
                caller.allocation(id).unwrap().scalar_content(bytes, access),
                before.allocation(id).unwrap().scalar_content(bytes, access)
            );
        }
    }
}

#[test]
fn same_interval_writes_and_missing_permissions_cannot_be_hidden_by_transport() {
    for boolean in [false, true] {
        let (caller, _, access, bytes) = observed_package(boolean);
        let mapping = PredicateCallBinding {
            caller: PredicateHolder(0),
            callee: PredicateHolder(7),
        };
        let id = AbstractAllocationId::new(0);
        let (frame, mut callee) = enter_predicate_call(&caller, &[mapping]).unwrap();
        let value = callee
            .allocation(id)
            .unwrap()
            .scalar_content(bytes, access)
            .unwrap();
        callee
            .allocation_mut(id)
            .unwrap()
            .record_scalar_content(bytes, access, value);
        assert_eq!(
            callee.closed_predicate_checks(),
            vec![(PredicateHolder(7), false)]
        );
        let before = callee.clone();
        assert!(frame.resume(&callee, &[mapping]).is_err());
        assert_eq!(callee, before);
        let mut bad = caller.clone();
        bad.allocation_mut(id)
            .unwrap()
            .set_ownership(OwnershipState::Unowned);
        assert!(enter_predicate_call(&bad, &[mapping]).is_err());
        let mut exhausted = caller.clone();
        exhausted.next_predicate_scope = u64::MAX;
        let before = exhausted.clone();
        assert!(matches!(
            enter_predicate_call(&exhausted, &[mapping]),
            Err(PredicateError::Budget)
        ));
        assert_eq!(exhausted, before);
    }
}

#[test]
fn induction_observations_can_cross_an_internal_call_without_becoming_entry_values() {
    for boolean in [false, true] {
        let (entry, _, access, bytes) = observed_package(boolean);
        let modified = BTreeSet::from([AbstractAllocationId::new(0)]);
        let repacked = BTreeSet::from([PredicateHolder(0)]);
        let mut head = ResourceState::new();
        assert!(head.inherit_loop_resources_with_predicates(&entry, &modified, &repacked));
        for (id, value) in &entry.values {
            head.define_value(*id, *value).unwrap();
        }
        head.abstract_loop_predicates_after_havoc(&entry, &modified, &repacked)
            .unwrap();
        let allocation = head.allocation(AbstractAllocationId::new(0)).unwrap();
        if boolean {
            assert!(matches!(
                allocation.bool_origin(bytes, access),
                Some(BoolOrigin::Snapshot(_))
            ));
        } else {
            assert!(matches!(
                allocation.scalar_origin(bytes, access).unwrap().first.root,
                ScalarOriginRoot::Snapshot(_)
            ));
        }
        let mapping = PredicateCallBinding {
            caller: PredicateHolder(0),
            callee: PredicateHolder(7),
        };
        let (frame, callee) = enter_predicate_call(&head, &[mapping]).unwrap();
        let returned = frame.resume(&callee, &[mapping]).unwrap();
        assert_eq!(
            returned.closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
        let allocation = returned.allocation(AbstractAllocationId::new(0)).unwrap();
        if boolean {
            assert!(matches!(
                allocation.bool_origin(bytes, access),
                Some(BoolOrigin::Transported(_))
            ));
        } else {
            assert!(matches!(
                allocation.scalar_origin(bytes, access).unwrap().first.root,
                ScalarOriginRoot::Transported(_)
            ));
        }
    }
}

#[test]
fn already_foreign_histories_are_not_recaptured_by_matching_root_numbers() {
    use super::super::logic::ObservationAtom;
    use crate::predicate_logic::LogicValue;
    for boolean in [false, true] {
        let (mut caller, _, _, _) = observed_package(boolean);
        let instance = caller.predicates.get_mut(&PredicateHolder(0)).unwrap();
        // An opaque retained history need not constrain the current cell.
        // Its old root can coincide with a local root without identifying it.
        instance.definition.logic.constraints.clear();
        instance.logical_facts.clear();
        let original = instance.logical_witnesses[0].value.clone();
        match &mut instance.logical_witnesses[0].value {
            LogicValue::Word(word) => {
                word.terms = std::mem::take(&mut word.terms)
                    .into_iter()
                    .map(|(mut atom, c)| {
                        let ObservationAtom::Historical { local, .. } = &mut atom else {
                            panic!("history");
                        };
                        *local = false;
                        (atom, c)
                    })
                    .collect();
            }
            LogicValue::BoolAtom {
                atom: ObservationAtom::HistoricalBool { local, .. },
                ..
            } => *local = false,
            _ => panic!("historical witness"),
        }
        let mapping = PredicateCallBinding {
            caller: PredicateHolder(0),
            callee: PredicateHolder(7),
        };
        let (_, callee) = enter_predicate_call(&caller, &[mapping]).unwrap();
        match (
            &original,
            &callee.predicates[&PredicateHolder(7)].logical_witnesses[0].value,
        ) {
            (LogicValue::Word(before), LogicValue::Word(after)) => {
                let ObservationAtom::Historical { cell: expected, .. } =
                    before.terms.keys().next().unwrap()
                else {
                    panic!("history");
                };
                assert!(
                    matches!(after.terms.keys().next(), Some(ObservationAtom::Historical { cell, local: false, .. }) if cell == expected)
                );
            }
            (
                LogicValue::BoolAtom {
                    atom:
                        ObservationAtom::HistoricalBool {
                            origin: expected, ..
                        },
                    ..
                },
                LogicValue::BoolAtom {
                    atom:
                        ObservationAtom::HistoricalBool {
                            origin,
                            local: false,
                            ..
                        },
                    ..
                },
            ) => assert_eq!(origin, expected),
            _ => panic!("foreign status lost"),
        }
    }
}

#[test]
fn unrelated_capture_collisions_still_fail_during_memory_transport() {
    use super::super::logic::ObservationAtom;
    use crate::predicate_logic::LogicValue;
    let (mut caller, _, _, _) = observed_package(false);
    let instance = caller.predicates.get_mut(&PredicateHolder(0)).unwrap();
    instance.definition.logic.constraints.clear();
    instance.logical_facts.clear();
    let scope = instance.logic_scope.unwrap();
    let LogicValue::Word(word) = &mut instance.logical_witnesses[0].value else {
        panic!("word");
    };
    word.terms = BTreeMap::from([
        (
            ObservationAtom::Local {
                scope,
                value: VirValueId::new(90),
            },
            1,
        ),
        (
            ObservationAtom::Captured {
                scope,
                value: VirValueId::new(90),
            },
            1,
        ),
    ]);
    let before = caller.clone();
    assert!(matches!(
        enter_predicate_call(
            &caller,
            &[PredicateCallBinding {
                caller: PredicateHolder(0),
                callee: PredicateHolder(7),
            }]
        ),
        Err(PredicateError::InvalidBinding)
    ));
    assert_eq!(caller, before);
}
