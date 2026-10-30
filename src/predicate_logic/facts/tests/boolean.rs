use super::*;

type BoolValue = LogicValue<u32, u32>;
pub(super) fn atom(id: u32) -> BoolValue {
    BoolValue::BoolAtom {
        atom: id,
        negated: false,
        known: None,
    }
}
pub(super) fn typed(value: BoolValue) -> Value {
    Value {
        ty: LogicType::Bool,
        value,
    }
}
pub(super) fn binary(operation: BooleanOperation, left: BoolValue, right: BoolValue) -> BoolValue {
    BoolValue::boolean_binary(operation, left, right, false, &mut LogicBudget::default()).unwrap()
}
fn binder() -> LogicExpression<u32> {
    expression(vec![(
        LogicType::Bool,
        LogicNodeKind::Binder(LogicBinder::Parameter(0)),
    )])
}
pub(super) fn import(facts: &mut Facts, value: BoolValue, truth: bool) -> Result<(), LogicError> {
    facts.extend(
        &binder(),
        &[(0, Some(typed(if truth { value } else { value.bool_not() })))],
        &mut LogicBudget::default(),
    )
}

#[test]
fn equality_queries_recognize_distributivity_without_assuming_either_result() {
    use BooleanOperation::*;
    let left = typed(binary(And, atom(1), binary(Or, atom(2), atom(3))));
    let right = typed(binary(
        Or,
        binary(And, atom(1), atom(2)),
        binary(And, atom(1), atom(3)),
    ));
    let facts = Facts::new();
    assert!(
        facts
            .entails(
                Comparison::Equal,
                &left,
                &right,
                &mut LogicBudget::default()
            )
            .unwrap()
    );
    for other in [
        typed(binary(Or, atom(1), binary(And, atom(2), atom(3)))),
        typed(binary(And, atom(4), binary(Or, atom(2), atom(3)))),
        typed(BoolValue::Bool(Some(true))),
    ] {
        assert!(
            !facts
                .entails(
                    Comparison::Equal,
                    &left,
                    &other,
                    &mut LogicBudget::default()
                )
                .unwrap()
        );
    }
    assert_eq!(known(&facts, left.value).unwrap(), None);
    assert_eq!(known(&facts, right.value).unwrap(), None);
}

#[test]
fn joint_saved_disjunctions_refine_and_prove_without_selecting_a_branch() {
    use BooleanOperation::Or;
    let mut facts = Facts::new();
    import(&mut facts, binary(Or, atom(1), atom(2)), true).unwrap();
    import(&mut facts, binary(Or, atom(1), atom(2).bool_not()), true).unwrap();
    assert_eq!(known(&facts, atom(1)).unwrap(), Some(true));
    assert_eq!(known(&facts, atom(2)).unwrap(), None);
    assert!(
        facts
            .entails(
                Comparison::Equal,
                &typed(atom(1)),
                &typed(BoolValue::Bool(Some(true))),
                &mut LogicBudget::default()
            )
            .unwrap()
    );
    assert!(
        facts
            .proves(
                &binder(),
                &[(0, Some(typed(atom(1))))],
                &mut LogicBudget::default()
            )
            .unwrap()
    );
    assert!(
        !facts
            .proves(
                &binder(),
                &[(0, Some(typed(atom(2))))],
                &mut LogicBudget::default()
            )
            .unwrap()
    );
    let mut weak = Facts::new();
    import(&mut weak, binary(Or, atom(1), atom(2)), true).unwrap();
    assert!(
        !weak
            .proves(
                &binder(),
                &[(0, Some(typed(atom(1))))],
                &mut LogicBudget::default()
            )
            .unwrap()
    );
    // The query was never installed as an assumption.
    assert_eq!(known(&weak, atom(1)).unwrap(), None);
    import(&mut facts, binary(Or, atom(1).bool_not(), atom(2)), true).unwrap();
    import(
        &mut facts,
        binary(Or, atom(1).bool_not(), atom(2).bool_not()),
        true,
    )
    .unwrap();
    assert_eq!(known(&facts, atom(1)), Err(LogicError::Unproved));
}
pub(super) fn known(facts: &Facts, value: BoolValue) -> Result<Option<bool>, LogicError> {
    Ok(facts
        .refine(typed(value), &mut LogicBudget::default())?
        .value
        .known_boolean())
}

#[test]
fn captured_gate_consequences_match_all_truth_table_rows_without_branch_guessing() {
    for operation in [
        BooleanOperation::And,
        BooleanOperation::Or,
        BooleanOperation::Equal,
    ] {
        for truth in [false, true] {
            for a in [None, Some(false), Some(true)] {
                for b in [None, Some(false), Some(true)] {
                    let mut facts = Facts::new();
                    if let Some(a) = a {
                        import(&mut facts, atom(1), a).unwrap();
                    }
                    if let Some(b) = b {
                        import(&mut facts, atom(2), b).unwrap();
                    }
                    let rows: Vec<_> = [false, true]
                        .into_iter()
                        .flat_map(|a| [false, true].map(|b| (a, b)))
                        .filter(|(x, y)| {
                            a.is_none_or(|a| a == *x)
                                && b.is_none_or(|b| b == *y)
                                && operation.evaluate(Some(*x), Some(*y)) == Some(truth)
                        })
                        .collect();
                    let result = import(&mut facts, binary(operation, atom(1), atom(2)), truth);
                    if rows.is_empty() {
                        assert_eq!(result, Err(LogicError::Unproved));
                        // Failed import cannot publish even a partial consequence.
                        assert_eq!(known(&facts, atom(1)), Ok(a));
                        assert_eq!(known(&facts, atom(2)), Ok(b));
                    } else {
                        result.unwrap();
                        for (id, first) in [(1, rows[0].0), (2, rows[0].1)] {
                            let expected = rows
                                .iter()
                                .all(|(a, b)| (if id == 1 { *a } else { *b }) == first)
                                .then_some(first);
                            assert_eq!(known(&facts, atom(id)), Ok(expected));
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn nested_premises_propagate_in_both_directions_and_preserve_foreign_identity() {
    let mut facts = Facts::new();
    // (a || b) && (b == c), with !a, establishes b and c.
    let nested = binary(
        BooleanOperation::And,
        binary(BooleanOperation::Or, atom(1), atom(2)),
        binary(BooleanOperation::Equal, atom(2), atom(3)),
    );
    import(&mut facts, nested, true).unwrap();
    assert_eq!(known(&facts, atom(2)), Ok(None));
    import(&mut facts, atom(1), false).unwrap();
    assert_eq!(known(&facts, atom(2)), Ok(Some(true)));
    assert_eq!(known(&facts, atom(3)), Ok(Some(true)));
    assert_eq!(known(&facts, atom(4)), Ok(None));
    let query = expression(vec![
        (
            LogicType::Bool,
            LogicNodeKind::Binder(LogicBinder::Parameter(0)),
        ),
        (
            LogicType::Bool,
            LogicNodeKind::Binder(LogicBinder::Parameter(1)),
        ),
        (LogicType::Bool, LogicNodeKind::And(0, 1)),
    ]);
    assert_eq!(
        facts.proves(
            &query,
            &[(0, Some(typed(atom(2)))), (1, Some(typed(atom(3))))],
            &mut LogicBudget::default()
        ),
        Ok(true)
    );
    assert_eq!(
        facts.proves(
            &binder(),
            &[(0, Some(typed(atom(3))))],
            &mut LogicBudget::default()
        ),
        Ok(true)
    );
}

#[test]
fn source_boolean_nodes_and_captured_binders_share_the_same_consequences() {
    let or = expression(vec![
        (
            LogicType::Bool,
            LogicNodeKind::Binder(LogicBinder::Parameter(0)),
        ),
        (
            LogicType::Bool,
            LogicNodeKind::Binder(LogicBinder::Parameter(1)),
        ),
        (LogicType::Bool, LogicNodeKind::Or(0, 1)),
    ]);
    let leaves = [(0, Some(typed(atom(1)))), (1, Some(typed(atom(2))))];
    let mut facts = Facts::new();
    facts
        .extend(&or, &leaves, &mut LogicBudget::default())
        .unwrap();
    assert_eq!(
        facts.proves(&or, &leaves, &mut LogicBudget::default()),
        Ok(true)
    );
    assert_eq!(known(&facts, atom(1)), Ok(None));
    import(&mut facts, atom(1), false).unwrap();
    assert_eq!(known(&facts, atom(2)), Ok(Some(true)));
    // Missing/stale dependent leaves cannot establish the other disjunct.
    let mut missing = Facts::new();
    missing
        .extend(
            &or,
            &[(0, None), (1, Some(typed(atom(2))))],
            &mut LogicBudget::default(),
        )
        .unwrap();
    assert_eq!(known(&missing, atom(2)), Ok(None));
    assert_eq!(
        missing.proves(
            &or,
            &[(0, None), (1, Some(typed(atom(2))))],
            &mut LogicBudget::default()
        ),
        Ok(false)
    );
    // Anonymous inputs remain distinct even after a premise is imported.
    import(&mut missing, BoolValue::Bool(None), true).unwrap();
    assert_eq!(known(&missing, BoolValue::Bool(None)), Ok(None));
}

#[test]
fn repeated_identities_negation_and_conflicting_captures_fail_closed() {
    for op in [
        BooleanOperation::And,
        BooleanOperation::Or,
        BooleanOperation::Equal,
    ] {
        let facts = Facts::new();
        let formula = binary(op, atom(1), atom(1).bool_not());
        let expected = op.evaluate(Some(true), Some(false));
        assert_eq!(known(&facts, formula), Ok(expected));
    }
    let mut facts = Facts::new();
    import(&mut facts, atom(1), true).unwrap();
    let conflicting = BoolValue::BoolAtom {
        atom: 1,
        negated: false,
        known: Some(false),
    };
    // A true outer disjunction cannot hide a conflicting nested snapshot.
    let formula = binary(
        BooleanOperation::Or,
        BoolValue::Bool(Some(true)),
        conflicting,
    );
    assert_eq!(known(&facts, formula.clone()), Err(LogicError::Unproved));
    assert_eq!(import(&mut facts, formula, true), Err(LogicError::Unproved));
    assert_eq!(known(&facts, atom(1)), Ok(Some(true)));
}

#[test]
fn shared_budget_failure_does_not_commit_new_facts() {
    let mut facts = Facts::new();
    import(&mut facts, atom(1), true).unwrap();
    let before = facts.facts.len();
    let value = binary(BooleanOperation::And, atom(2), atom(3));
    assert_eq!(
        facts.extend(
            &binder(),
            &[(0, Some(typed(value)))],
            &mut LogicBudget { remaining: 32 }
        ),
        Err(LogicError::Budget)
    );
    assert_eq!(facts.facts.len(), before);
    assert_eq!(known(&facts, atom(2)), Ok(None));
    assert_eq!(known(&facts, atom(1)), Ok(Some(true)));
}

#[test]
fn equality_queries_use_nested_guarantees_even_when_both_sides_stay_unknown() {
    let mut facts = Facts::new();
    import(
        &mut facts,
        binary(
            BooleanOperation::And,
            binary(BooleanOperation::Equal, atom(1), atom(2)),
            binary(BooleanOperation::Or, atom(3), atom(4)),
        ),
        true,
    )
    .unwrap();
    assert_eq!(known(&facts, atom(1)), Ok(None));
    for (a, b) in [(1, 2), (2, 1)] {
        assert_eq!(
            facts.entails(
                Comparison::Equal,
                &typed(atom(a)),
                &typed(atom(b)),
                &mut LogicBudget::default()
            ),
            Ok(true)
        );
    }
    assert_eq!(
        facts.entails(
            Comparison::Equal,
            &typed(atom(1)),
            &typed(atom(3)),
            &mut LogicBudget::default()
        ),
        Ok(false)
    );
    assert_eq!(
        facts.entails(
            Comparison::Equal,
            &typed(atom(1)),
            &typed(atom(2).bool_not()),
            &mut LogicBudget::default()
        ),
        Ok(false)
    );
}
