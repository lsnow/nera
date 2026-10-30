use super::*;
use crate::predicate_logic::*;

fn closed(def: &PredicateDefinition, value: u64) -> ResourceState {
    transfer_predicate(&state(), def, 7, &explicit_effect(value))
        .unwrap()
        .output
}

#[test]
fn different_concrete_witnesses_join_as_one_existential_guarantee() {
    let mut def = logical_definition();
    // A fold default chooses an initial witness, not a post-join guarantee.
    def.logic.existentials[0].default = Some(LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Usize,
            kind: LogicNodeKind::Word(6),
        }],
        root: 0,
    });
    let a = closed(&def, 1);
    let b = closed(&def, 2);
    let c = closed(&def, 7);
    let before = (a.clone(), b.clone(), c.clone());
    let joined = a.join(&b).unwrap();
    assert_eq!(joined, b.join(&a).unwrap());
    assert_eq!(joined.join(&a).unwrap(), joined);
    assert_eq!(joined.join(&b).unwrap(), joined);
    assert_eq!(joined.widen(&b).unwrap(), joined);
    assert_eq!(
        joined.join(&c).unwrap(),
        a.join(&b.join(&c).unwrap()).unwrap()
    );
    assert_eq!(a.join(&a).unwrap(), a, "exact joins retain precision");
    assert_eq!(joined.values, a.values);
    assert_eq!(joined.allocations, a.allocations);
    assert_eq!(joined.loans, a.loans);
    assert_eq!(joined.next_predicate_scope, a.next_predicate_scope);
    assert!(joined.covers_cfg_case(&a));
    assert!(joined.covers_cfg_case(&b));
    assert_eq!(
        joined.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let opened = transfer_predicate(
        &joined,
        &def,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 23,
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        opened.opened_predicate_snapshot(23, 0, 0),
        Some((AbstractValue::U64(U64Interval::new(0, 7).unwrap()), None))
    );
    assert!(transfer_predicate(&opened, &def, 7, &explicit_effect(7)).is_ok());
    assert!(transfer_predicate(&opened, &def, 7, &explicit_effect(8)).is_err());
    assert_eq!((a, b, c), before);

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
    assert_eq!(
        guarded.cases()[0].closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
}

#[test]
fn boolean_witnesses_are_hidden_without_proving_either_branch_value() {
    let mut def = logical_definition();
    def.logic.existentials.push(Existential {
        name: "flag".into(),
        ty: LogicType::Bool,
        default: None,
    });
    let make = |flag| {
        let mut effect = explicit_effect(3);
        let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
            unreachable!()
        };
        witnesses.values.push((
            1,
            LogicExpression {
                nodes: vec![LogicNode {
                    ty: LogicType::Bool,
                    kind: LogicNodeKind::Bool(flag),
                }],
                root: 0,
            },
        ));
        transfer_predicate(&state(), &def, 7, &effect)
            .unwrap()
            .output
    };
    let a = make(true);
    let b = make(false);
    let joined = a.join(&b).unwrap();
    assert_eq!(joined, b.join(&a).unwrap());
    let opened = transfer_predicate(
        &joined,
        &def,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 24,
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        opened.opened_predicate_snapshot(24, 0, 1),
        Some((AbstractValue::Bool(AbstractBool::Unknown), None))
    );
}

#[test]
fn public_parameters_are_not_existentially_weakened() {
    let mut def = logical_definition();
    def.logic.parameters.push(LogicParameter {
        position: 1,
        name: "limit".into(),
        ty: LogicType::Usize,
    });
    let make = |parameter, witness| {
        let mut effect = explicit_effect(witness);
        let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
            unreachable!()
        };
        witnesses.arguments.push(LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Word(parameter),
            }],
            root: 0,
        });
        transfer_predicate(&state(), &def, 7, &effect)
            .unwrap()
            .output
    };
    let a = make(4, 1);
    assert!(a.join(&make(4, 2)).is_ok());
    assert_eq!(
        a.join(&make(5, 2)),
        Err(ResourceJoinError::PredicateStateMismatch)
    );
}

#[test]
fn hidden_initialization_counts_cannot_create_an_initialized_envelope() {
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
    let a = closed(&def, 0);
    let b = closed(&def, 1);
    let before = (a.clone(), b.clone());
    let joined = a.join(&b).unwrap();
    assert_eq!(joined, b.join(&a).unwrap());
    assert!(
        joined
            .closed_predicate_checks()
            .iter()
            .all(|(_, valid)| *valid)
    );
    let allocation = joined.allocation(AbstractAllocationId::new(0)).unwrap();
    let missing = ByteRange::new(8, 16).unwrap();
    assert_ne!(
        allocation.initialization().classify(missing),
        InitializationClass::Initialized
    );
    assert!(!allocation.valid_value_bytes().contains(missing));
    assert!(!joined.logical_initialized_prefix_covers(
        AbstractAllocationId::new(0),
        VirMemoryAccess::core_u64(),
        AbstractByteRange::Exact(missing),
    ));
    // Existential join keeps the clause, but its maximum permitted witness
    // cannot be selected without real bytes for that particular endpoint.
    let opened = transfer_predicate(
        &joined,
        &def,
        7,
        &PredicateEffect::UnfoldInPlace {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        transfer_predicate(&opened, &def, 7, &explicit_effect(2)),
        Err(PredicateError::UnprovedRepresentation)
    );
    assert_eq!((a, b), before);
}

#[test]
fn abstraction_is_read_only_and_budget_failure_does_not_advance_loop_epoch() {
    let def = logical_definition();
    let s = closed(&def, 1);
    let p = &s.predicates[&PredicateHolder(0)];
    let before = s.clone();
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert_eq!(
        s.abstract_predicate_logic_at_scope(p, p.logic_scope.unwrap(), &mut budget),
        Err(PredicateError::Budget)
    );
    let mut copy = p.clone();
    let mut next = s.next_predicate_scope;
    assert_eq!(
        s.abstract_loop_predicate_logic(&mut copy, &mut next, &mut budget),
        Err(PredicateError::Budget)
    );
    assert_eq!(next, s.next_predicate_scope);
    assert_eq!(&copy, p);
    assert_eq!(s, before);
}
