use super::*;

fn sum_facts(equal: bool, missing: bool) -> (Facts, Value, Value) {
    use LogicNodeKind::*;
    let total = word(10, 0, 2);
    let a = word(20, 0, 1);
    let b = word(30, 0, 1);
    let e = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Existential(0))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
        (LogicType::Usize, Add(1, 2)),
        (
            LogicType::Bool,
            if equal { Equal(0, 3) } else { LessEqual(0, 3) },
        ),
    ]);
    let mut facts = Facts::new();
    facts
        .extend(
            &e,
            &[
                (0, Some(total.clone())),
                (1, Some(a.clone())),
                (2, (!missing).then_some(b.clone())),
            ],
            &mut LogicBudget::default(),
        )
        .unwrap();
    let (LogicValue::Word(a), LogicValue::Word(b)) = (a.value, b.value) else {
        unreachable!()
    };
    (
        facts,
        total,
        Value {
            ty: LogicType::Usize,
            value: LogicValue::Word(a.add(&b).unwrap()),
        },
    )
}

#[test]
fn premise_forms_require_a_separate_equality_proof() {
    for equal in [false, true] {
        let (facts, total, sum) = sum_facts(equal, false);
        let candidates = facts
            .symbolic_word_candidates(LogicType::Usize, &mut LogicBudget::default())
            .unwrap();
        assert!(candidates.iter().any(|v| v == &sum));
        assert_eq!(
            facts.entails(Comparison::Equal, &total, &sum, &mut LogicBudget::default()),
            Ok(equal)
        );
        assert!(
            facts
                .symbolic_word_candidates(LogicType::U64, &mut LogicBudget::default())
                .unwrap()
                .is_empty()
        );
    }
}

#[test]
fn unavailable_inputs_wrong_types_and_exhausted_budget_supply_no_candidates() {
    let (facts, _, _) = sum_facts(true, true);
    assert!(
        facts
            .symbolic_word_candidates(LogicType::Usize, &mut LogicBudget::default())
            .unwrap()
            .is_empty()
    );
    assert!(matches!(
        facts.symbolic_word_candidates(LogicType::Bool, &mut LogicBudget::default()),
        Err(LogicError::TypeMismatch)
    ));
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert!(matches!(
        facts.symbolic_word_candidates(LogicType::Usize, &mut budget),
        Err(LogicError::Budget)
    ));
}

#[test]
fn mathematical_premises_do_not_publish_undefined_word_forms() {
    let mut facts = Facts::new();
    let x = word(10, 0, 1);
    facts
        .extend_difference(&x, &x, i128::from(u64::MAX), &mut LogicBudget::default())
        .unwrap();
    let candidates = facts
        .symbolic_word_candidates(LogicType::Usize, &mut LogicBudget::default())
        .unwrap();
    assert!(
        candidates
            .iter()
            .all(|value| matches!(&value.value,LogicValue::Word(word) if word.constant==0))
    );
}
