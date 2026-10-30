use super::boolean::{atom, binary, known, typed};
use super::*;

#[test]
fn explicit_truths_preserve_gate_identity_and_polarity() {
    let mut facts = Facts::new();
    let gate = binary(BooleanOperation::Or, atom(1), atom(2));
    facts
        .extend_booleans(
            &[
                (typed(gate.clone()), true),
                (typed(atom(1).bool_not()), true),
            ],
            &mut LogicBudget::default(),
        )
        .unwrap();
    assert_eq!(known(&facts, atom(1)), Ok(Some(false)));
    assert_eq!(known(&facts, atom(2)), Ok(Some(true)));
    assert_eq!(known(&facts, gate), Ok(Some(true)));
    assert_eq!(known(&facts, atom(3)), Ok(None));
}

#[test]
fn captured_runtime_comparison_truth_becomes_a_typed_numeric_premise() {
    for ty in [LogicType::U64, LogicType::Usize] {
        let capture = super::typed_captures::captured(ty, LogicNodeKind::LessEqual(0, 1));
        let mut facts = Facts::new();
        facts
            .extend_booleans(&[(capture, false)], &mut LogicBudget::default())
            .unwrap();
        for query_type in [LogicType::U64, LogicType::Usize] {
            let mut a = word(1, 0, 20);
            let mut b = word(2, 0, 20);
            a.ty = query_type;
            b.ty = query_type;
            assert_eq!(
                facts.entails(Comparison::Less, &b, &a, &mut LogicBudget::default()),
                Ok(query_type == ty)
            );
        }
    }
}

#[test]
fn observation_batches_are_atomic_on_conflict_wrong_type_and_budget_exhaustion() {
    let mut facts = Facts::new();
    facts
        .extend_booleans(&[(typed(atom(1)), true)], &mut LogicBudget::default())
        .unwrap();
    let before = facts.facts.len();
    for (batch, expected) in [
        (
            vec![(typed(atom(2)), true), (typed(atom(1)), false)],
            LogicError::Unproved,
        ),
        (
            vec![(typed(atom(2)), true), (word(3, 0, 20), true)],
            LogicError::TypeMismatch,
        ),
    ] {
        assert_eq!(
            facts.extend_booleans(&batch, &mut LogicBudget::default()),
            Err(expected)
        );
        assert_eq!(facts.facts.len(), before);
        assert_eq!(known(&facts, atom(2)), Ok(None));
    }
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES - 3).unwrap();
    assert_eq!(
        facts.extend_booleans(&[(typed(atom(2)), true)], &mut budget),
        Err(LogicError::Budget)
    );
    assert_eq!(facts.facts.len(), before);
    assert_eq!(known(&facts, atom(1)), Ok(Some(true)));
    assert_eq!(known(&facts, atom(2)), Ok(None));
}

#[test]
fn anonymous_observations_cannot_name_a_later_query() {
    let mut facts = Facts::new();
    facts
        .extend_booleans(
            &[(typed(LogicValue::Bool(None)), true)],
            &mut LogicBudget::default(),
        )
        .unwrap();
    assert_eq!(known(&facts, LogicValue::Bool(None)), Ok(None));
}

#[test]
fn mixed_observation_transaction_checks_numeric_only_cycles_before_publication() {
    let mut facts = Facts::new();
    let x = word(1, 0, 20);
    let y = word(2, 0, 20);
    let cycle = [(x.clone(), y.clone(), -1), (y.clone(), x.clone(), 0)];
    assert_eq!(
        facts.extend_observations(
            &[(typed(atom(3)), true)],
            &cycle,
            &mut LogicBudget::default()
        ),
        Err(LogicError::Unproved)
    );
    assert!(facts.facts.is_empty());
    assert_eq!(known(&facts, atom(3)), Ok(None));
    facts
        .extend_observations(&[], &cycle[..1], &mut LogicBudget::default())
        .unwrap();
    let before = facts.facts.len();
    facts
        .extend_observations(&[], &cycle[..1], &mut LogicBudget::default())
        .unwrap();
    assert_eq!(facts.facts.len(), before);
    let mut wrong = y.clone();
    wrong.ty = LogicType::U64;
    assert_eq!(
        facts.extend_observations(
            &[(typed(atom(3)), true)],
            &[(x.clone(), wrong, 0)],
            &mut LogicBudget::default()
        ),
        Err(LogicError::TypeMismatch)
    );
    assert_eq!(facts.facts.len(), before);
    assert_eq!(known(&facts, atom(3)), Ok(None));
    assert_eq!(
        facts.entails(Comparison::Less, &x, &y, &mut LogicBudget::default()),
        Ok(true)
    );
}

#[test]
fn numeric_batch_conflicts_with_saved_boolean_guarantee_without_poisoning_it() {
    let capture = super::typed_captures::captured(LogicType::Usize, LogicNodeKind::LessEqual(0, 1));
    let mut facts = Facts::new();
    facts
        .extend_booleans(&[(capture.clone(), false)], &mut LogicBudget::default())
        .unwrap();
    let before = facts.facts.len();
    assert_eq!(
        facts.extend_observations(
            &[],
            &[(word(1, 0, 20), word(2, 0, 20), 0)],
            &mut LogicBudget::default()
        ),
        Err(LogicError::Unproved)
    );
    assert_eq!(facts.facts.len(), before);
    assert_eq!(
        facts
            .refine(capture, &mut LogicBudget::default())
            .unwrap()
            .value
            .known_boolean(),
        Some(false)
    );
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES - 4).unwrap();
    assert_eq!(
        facts.extend_observations(&[], &[(word(2, 0, 20), word(1, 0, 20), -1)], &mut budget),
        Err(LogicError::Budget)
    );
    assert_eq!(facts.facts.len(), before);
}
