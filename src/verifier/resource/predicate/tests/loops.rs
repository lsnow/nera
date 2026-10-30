use super::*;
use crate::predicate_logic::*;

fn open(input: &ResourceState, def: &PredicateDefinition, action: u32) -> ResourceState {
    transfer_predicate(
        input,
        def,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action,
        },
    )
    .unwrap()
    .output
}

#[test]
fn sealed_loop_packages_forget_entry_witnesses_and_recheck_changed_refolds() {
    let def = logical_definition();
    let entry = transfer_predicate(&state(), &def, 7, &explicit_effect(6))
        .unwrap()
        .output;
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    let mut untouched = entry.clone();
    untouched
        .abstract_loop_predicates(&BTreeSet::new())
        .unwrap();
    assert_eq!(untouched, entry);
    let mut head = entry.clone();
    head.abstract_loop_predicates(&repacked).unwrap();
    assert_eq!(head.values, entry.values);
    assert_eq!(head.allocations, entry.allocations);
    assert_eq!(head.loans, entry.loans);
    assert_eq!(
        head.predicates[&PredicateHolder(0)].resources,
        entry.predicates[&PredicateHolder(0)].resources
    );
    assert_ne!(
        head.predicates[&PredicateHolder(0)].logic_scope,
        entry.predicates[&PredicateHolder(0)].logic_scope
    );
    assert!(head.loop_resources_match_with_predicates(&entry, &[binding(0).permission], &repacked));
    assert!(!head.loop_resources_match(&entry, &[]));
    let opened = open(&head, &def, 21);
    assert_eq!(
        opened.opened_predicate_snapshot(21, 0, 0),
        Some((AbstractValue::U64(U64Interval::new(0, 7).unwrap()), None))
    );
    assert!(!opened.loop_resources_match_with_predicates(&entry, &[], &repacked));
    let before = opened.clone();
    for value in [0, 7] {
        let closed = transfer_predicate(&opened, &def, 7, &explicit_effect(value))
            .unwrap()
            .output;
        assert!(closed.loop_resources_match_with_predicates(
            &entry,
            &[binding(0).permission],
            &repacked
        ));
        assert!(!closed.loop_resources_match(&entry, &[]));
        assert!(closed.opened_predicate_snapshot(21, 0, 0).is_none());
        let reopened = open(&closed, &def, 22);
        assert!(!reopened.loop_resources_match_with_predicates(&entry, &[], &repacked));
        assert!(reopened.opened_predicate_snapshot(21, 0, 0).is_none());
    }
    assert!(transfer_predicate(&opened, &def, 7, &explicit_effect(8)).is_err());
    assert_eq!(opened, before);

    // An open invariant is not existentially abstracted. Reopening with the
    // same static action number cannot replace its prior immutable instance.
    let mut open_head = opened.clone();
    open_head.abstract_loop_predicates(&repacked).unwrap();
    assert_eq!(open_head, opened);
    let refolded = transfer_predicate(&opened, &def, 7, &explicit_effect(6))
        .unwrap()
        .output;
    let reopened = open(&refolded, &def, 21);
    assert!(!reopened.loop_resources_match_with_predicates(&opened, &[], &repacked));
}

#[test]
fn loop_abstraction_never_supplies_missing_authority_or_initialization() {
    let def = logical_definition();
    let entry = transfer_predicate(&state(), &def, 7, &explicit_effect(6))
        .unwrap()
        .output;
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    for mutation in 0..6 {
        let mut bad = entry.clone();
        match mutation {
            0 => {
                bad.values.remove(&binding(0).permission);
            }
            1 => {
                let permission = bad.predicates[&PredicateHolder(0)].resources[0].permission;
                *bad.value_mut(binding(0).permission).unwrap() =
                    AbstractValue::Permission(permission);
            }
            2 => {
                bad.allocations.remove(&AbstractAllocationId::new(0));
            }
            3 => {
                bad.allocation_mut(AbstractAllocationId::new(0))
                    .unwrap()
                    .mark_uninitialized(ByteRange::new(0, 8).unwrap())
                    .unwrap();
            }
            4 => {
                bad.predicates
                    .get_mut(&PredicateHolder(0))
                    .unwrap()
                    .resources[0]
                    .carrier = None;
            }
            _ => {
                bad.next_predicate_scope = u64::MAX;
            }
        }
        let before = bad.clone();
        assert!(
            bad.abstract_loop_predicates(&repacked).is_err(),
            "mutation {mutation}"
        );
        assert_eq!(bad, before);
        if mutation != 5 {
            assert!(
                !bad.loop_resources_match_with_predicates(&entry, &[], &repacked),
                "mutation {mutation}"
            );
        }
    }
    let mut missing = entry.clone();
    missing.predicates.clear();
    assert!(!missing.loop_resources_match_with_predicates(&entry, &[], &repacked));
}

#[test]
fn loop_abstraction_does_not_initialize_a_hidden_counts_upper_envelope() {
    let mut def = logical_definition();
    def.logic.constraints[0].nodes[1].kind = LogicNodeKind::Word(2);
    def.logical_prefixes
        .push(crate::PredicateInitializedPrefix {
            resource: 0,
            array_offset: 0,
            element: VirMemoryAccess::core_u64(),
            length: 2,
            stride: 8,
            count: crate::PredicatePrefixCount::Logical(LogicExpression {
                nodes: vec![LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
                }],
                root: 0,
            }),
        });
    let mut entry = transfer_predicate(&state(), &def, 7, &explicit_effect(1))
        .unwrap()
        .output;
    let before = entry.clone();
    entry
        .abstract_loop_predicates(&BTreeSet::from([PredicateHolder(0)]))
        .unwrap();
    assert_eq!(entry.allocations, before.allocations);
    assert_eq!(entry.values, before.values);
    assert!(
        entry
            .closed_predicate_checks()
            .iter()
            .all(|(_, valid)| *valid)
    );
    assert!(!entry.logical_initialized_prefix_covers(
        AbstractAllocationId::new(0),
        VirMemoryAccess::core_u64(),
        AbstractByteRange::Exact(ByteRange::new(8, 16).unwrap()),
    ));
    assert_ne!(
        entry
            .allocation(AbstractAllocationId::new(0))
            .unwrap()
            .initialization()
            .classify(ByteRange::new(0, 16).unwrap()),
        InitializationClass::Initialized
    );
}

#[test]
fn refolded_loop_parameters_require_the_same_scalar_value() {
    for boolean in [false, true] {
        let ty = if boolean {
            LogicType::Bool
        } else {
            LogicType::Usize
        };
        let unknown = if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::new(2, 6).unwrap())
        };
        let mut def = logical_definition();
        def.logic.parameters.push(LogicParameter {
            position: 1,
            name: "limit".into(),
            ty,
        });
        let input_id = VirValueId::new(90);
        let mut input = state();
        input.define_value(input_id, unknown).unwrap();
        let effect = |value: u64| {
            let mut effect = explicit_effect(value);
            let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
                unreachable!()
            };
            witnesses.inputs.push((ty, WitnessInput::Scalar(input_id)));
            witnesses.arguments.push(LogicExpression {
                nodes: vec![LogicNode {
                    ty,
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                }],
                root: 0,
            });
            effect
        };
        let entry = transfer_predicate(&input, &def, 7, &effect(6))
            .unwrap()
            .output;
        let repacked = BTreeSet::from([PredicateHolder(0)]);
        let mut head = entry.clone();
        head.abstract_loop_predicates(&repacked).unwrap();
        let opened = open(&head, &def, 21);
        let good = transfer_predicate(&opened, &def, 7, &effect(0))
            .unwrap()
            .output;
        assert!(good.loop_resources_match_with_predicates(&entry, &[], &repacked));
        let mut overwritten = opened.clone();
        *overwritten.value_mut(input_id).unwrap() = unknown;
        let bad = transfer_predicate(&overwritten, &def, 7, &effect(0))
            .unwrap()
            .output;
        assert!(!bad.loop_resources_match_with_predicates(&entry, &[], &repacked));
        for (mut returned, expected) in [(good.clone(), true), (bad.clone(), false)] {
            let instance = returned.predicates.remove(&PredicateHolder(0)).unwrap();
            returned.predicates.insert(PredicateHolder(99), instance);
            assert_eq!(
                returned.loop_resources_match_with_predicates(&entry, &[], &repacked),
                expected
            );
        }
    }
}
