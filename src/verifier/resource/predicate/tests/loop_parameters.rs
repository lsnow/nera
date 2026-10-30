use super::*;
use crate::predicate_logic::*;

const SLOT: VirValueId = VirValueId::new(90);
const NEXT: VirValueId = VirValueId::new(91);

fn args(boolean: bool, id: VirValueId) -> WitnessArguments<VirMemoryAccess, VirValueId> {
    let ty = if boolean {
        LogicType::Bool
    } else {
        LogicType::Usize
    };
    WitnessArguments {
        inputs: vec![(ty, WitnessInput::Scalar(id))],
        arguments: vec![LogicExpression {
            nodes: vec![LogicNode {
                ty,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            }],
            root: 0,
        }],
        values: vec![],
    }
}

fn head(entry: &ResourceState, plan: &LoopPredicateParameters, boolean: bool) -> ResourceState {
    let mut head = ResourceState::new();
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    assert!(head.inherit_loop_resources_with_predicates(entry, &BTreeSet::new(), &repacked));
    head.inherit_loop_scalar_frame(entry, &BTreeSet::new());
    for id in [VirValueId::new(0), VirValueId::new(1)] {
        head.define_value(id, *entry.value(id).unwrap()).unwrap();
    }
    head.define_value(
        SLOT,
        if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::unknown())
        },
    )
    .unwrap();
    head.abstract_loop_predicates_after_havoc_with_parameters(
        entry,
        &BTreeSet::new(),
        &repacked,
        plan,
    )
    .unwrap();
    head
}

fn iteration(
    head: &ResourceState,
    def: &PredicateDefinition,
    boolean: bool,
    stale: bool,
) -> ResourceState {
    let opened = transfer_predicate(
        head,
        def,
        7,
        &PredicateEffect::WithArguments {
            holder: PredicateHolder(0),
            arguments: args(boolean, SLOT),
            effect: Box::new(PredicateEffect::UnfoldNamed {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
                action: 50,
            }),
        },
    )
    .unwrap()
    .output;
    let mut changed = opened;
    changed
        .define_value(
            NEXT,
            if boolean {
                AbstractValue::Bool(AbstractBool::Unknown)
            } else {
                AbstractValue::U64(U64Interval::new(2, 7).unwrap())
            },
        )
        .unwrap();
    let mut witnesses = args(boolean, if stale { SLOT } else { NEXT });
    let ty = witnesses.inputs[0].0;
    if stale {
        witnesses.inputs.push((ty, WitnessInput::Scalar(NEXT)));
    }
    witnesses.values.push((
        0,
        LogicExpression {
            nodes: vec![LogicNode {
                ty,
                kind: if boolean {
                    LogicNodeKind::Bool(false)
                } else {
                    LogicNodeKind::Word(0)
                },
            }],
            root: 0,
        },
    ));
    let evidence = transfer_predicate(
        &changed,
        def,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses,
        },
    )
    .unwrap();
    check_predicate_evidence(&changed, &evidence).unwrap();
    let folded = evidence.output;
    let renames = [
        (VirValueId::new(0), VirValueId::new(0)),
        (VirValueId::new(1), VirValueId::new(1)),
        (NEXT, SLOT),
    ];
    let mut projected = folded.project_cfg_edge(&renames);
    for (a, b) in renames {
        projected
            .define_value(b, *folded.value(a).unwrap())
            .unwrap();
    }
    projected
}

#[test]
fn changing_public_parameters_require_the_current_header_actual_on_every_backedge() {
    for boolean in [false, true] {
        let (entry, def) = super::join_captures::captured(boolean, 90, true);
        let repacked = BTreeSet::from([PredicateHolder(0)]);
        let plan = entry
            .loop_predicate_parameters(&BTreeSet::from([SLOT]), &BTreeSet::new(), &repacked)
            .unwrap();
        assert!(plan.expression(PredicateHolder(0), 0).is_some());
        let arbitrary = head(&entry, &plan, boolean);
        assert_eq!(arbitrary.allocations, entry.allocations);
        assert_eq!(arbitrary.loans, entry.loans);
        assert_eq!(
            arbitrary.value(binding(0).permission),
            entry.value(binding(0).permission)
        );
        if !boolean {
            assert_eq!(
                arbitrary.value(SLOT),
                Some(&AbstractValue::U64(U64Interval::unknown()))
            );
        }
        arbitrary
            .check_predicate_arguments(&def, PredicateHolder(0), &args(boolean, SLOT))
            .unwrap();
        let good = iteration(&arbitrary, &def, boolean, false);
        assert!(good.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan));
        assert!(!good.loop_resources_match_with_predicates(&entry, &[], &repacked));
        let stale = iteration(&arbitrary, &def, boolean, true);
        assert!(!stale.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan));
        let mut overwritten = good.clone();
        let value = *overwritten.value(SLOT).unwrap();
        *overwritten.value_mut(SLOT).unwrap() = value;
        assert!(!overwritten.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan));
        let mut relabeled = good;
        let package = relabeled.predicates.remove(&PredicateHolder(0)).unwrap();
        relabeled.predicates.insert(PredicateHolder(99), package);
        assert!(relabeled.loop_resources_match_with_parameters(&entry, &[], &repacked, &plan));
    }
}

#[test]
fn induction_parameter_binding_never_recovers_missing_resources_or_commits_partial_havoc() {
    let (entry, _) = super::join_captures::captured(false, 90, true);
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    let plan = entry
        .loop_predicate_parameters(&BTreeSet::from([SLOT]), &BTreeSet::new(), &repacked)
        .unwrap();
    for mutation in 0..3 {
        let mut candidate = entry.clone();
        match mutation {
            0 => {
                candidate.values.remove(&binding(0).permission);
            }
            1 => {
                candidate.values.remove(&SLOT);
            }
            _ => {
                candidate.next_predicate_scope = u64::MAX;
            }
        }
        let before = candidate.clone();
        assert!(
            candidate
                .abstract_loop_predicates_after_havoc_with_parameters(
                    &entry,
                    &BTreeSet::new(),
                    &repacked,
                    &plan
                )
                .is_err()
        );
        assert_eq!(candidate, before);
    }
}

#[test]
fn only_unique_live_direct_captures_select_inductive_slots() {
    let (entry, _) = super::join_captures::captured(false, 90, true);
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    assert_eq!(
        entry
            .loop_predicate_parameters(&BTreeSet::new(), &BTreeSet::new(), &repacked)
            .unwrap(),
        LoopPredicateParameters::default()
    );
    let renames = [
        (VirValueId::new(0), VirValueId::new(0)),
        (VirValueId::new(1), VirValueId::new(1)),
        (SLOT, SLOT),
        (SLOT, NEXT),
    ];
    let mut fanout = entry.project_cfg_edge(&renames);
    for (a, b) in renames {
        fanout.define_value(b, *entry.value(a).unwrap()).unwrap();
    }
    assert_eq!(
        fanout
            .loop_predicate_parameters(&BTreeSet::from([SLOT, NEXT]), &BTreeSet::new(), &repacked)
            .unwrap(),
        LoopPredicateParameters::default()
    );
    let mut overwritten = entry;
    let same = *overwritten.value(SLOT).unwrap();
    *overwritten.value_mut(SLOT).unwrap() = same;
    assert_eq!(
        overwritten
            .loop_predicate_parameters(&BTreeSet::from([SLOT]), &BTreeSet::new(), &repacked)
            .unwrap(),
        LoopPredicateParameters::default()
    );
}

#[test]
fn affine_captures_select_templates_but_foreign_captures_do_not() {
    let (entry, _) = super::join_captures::captured(false, 90, true);
    let repacked = BTreeSet::from([PredicateHolder(0)]);
    let changing = BTreeSet::from([SLOT]);
    let mut affine = entry.clone();
    let parameter = &mut affine
        .predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .logical_parameters[0];
    let LogicValue::Word(value) = &mut parameter.value else {
        unreachable!()
    };
    *value = value.add(&AffineValue::exact(1)).unwrap();
    assert_ne!(
        affine
            .loop_predicate_parameters(&changing, &BTreeSet::new(), &repacked)
            .unwrap(),
        LoopPredicateParameters::default()
    );
    let bindings = [PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(7),
    }];
    let (frame, callee) = enter_predicate_call(&entry, &bindings).unwrap();
    let returned = frame.resume(&callee, &bindings).unwrap();
    assert_eq!(
        returned.loop_predicate_parameters(&changing, &BTreeSet::new(), &repacked),
        Err(PredicateError::UnprovedRepresentation),
        "an internal return without an SSA carrier is not a valid loop package"
    );
    let foreign = super::join_captures::foreign_capture(entry);
    assert_eq!(
        foreign
            .loop_predicate_parameters(&changing, &BTreeSet::new(), &repacked)
            .unwrap(),
        LoopPredicateParameters::default()
    );
}
