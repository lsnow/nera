use super::*;

fn exact_successor() -> LogicExpression<u32> {
    let mut e = successor();
    e.nodes.last_mut().unwrap().kind = LogicNodeKind::Equal(2, 3);
    e
}

#[test]
fn exact_differences_follow_relations_in_both_directions_and_across_paths() {
    let x = word(10, 0, 8);
    let y = word(20, 0, 8);
    let z = word(30, 0, 8);
    let e = exact_successor();
    let mut facts = facts(&e, Some(x.clone()), Some(y.clone()));
    facts
        .extend(
            &e,
            &[(0, Some(y.clone())), (3, Some(z.clone()))],
            &mut LogicBudget::default(),
        )
        .unwrap();
    for (a, b, expected) in [(&y, &x, 1), (&x, &y, -1), (&z, &x, 2), (&x, &x, 0)] {
        assert_eq!(
            facts.exact_word_difference(a, b, &mut LogicBudget::default()),
            Ok(Some(expected))
        );
    }
    assert_eq!(
        facts.exact_word_difference(&z, &word(40, 0, 8), &mut LogicBudget::default()),
        Ok(None)
    );
}

#[test]
fn one_sided_bounds_and_equal_ranges_are_not_exact_offsets() {
    let x = word(10, 0, 8);
    let y = word(20, 0, 8);
    let facts = facts(&successor(), Some(x.clone()), Some(y.clone()));
    assert_eq!(
        facts.exact_word_difference(&y, &x, &mut LogicBudget::default()),
        Ok(None)
    );
    assert_eq!(
        Facts::new().exact_word_difference(&y, &x, &mut LogicBudget::default()),
        Ok(None)
    );
}

#[test]
fn offset_query_checks_types_and_does_not_claim_machine_subtraction() {
    let x = word(10, 0, 8);
    let y = word(20, 0, 8);
    let facts = facts(&exact_successor(), Some(x.clone()), Some(y.clone()));
    let mut a = x.clone();
    a.ty = LogicType::U64;
    assert_eq!(
        facts.exact_word_difference(&a, &y, &mut LogicBudget::default()),
        Err(LogicError::TypeMismatch)
    );
    let mut b = y;
    b.ty = LogicType::U64;
    assert_eq!(
        facts.exact_word_difference(&b, &a, &mut LogicBudget::default()),
        Ok(None)
    );
    assert_eq!(
        Facts::new().exact_word_difference(
            &constant(0),
            &constant(u64::MAX),
            &mut LogicBudget::default()
        ),
        Ok(Some(-i128::from(u64::MAX)))
    );
}

#[test]
fn cancelled_query_atoms_cannot_hide_conflicting_copies_or_exhausted_budget() {
    let a = word(10, 0, 1);
    let b = word(10, 2, 3);
    assert_eq!(
        Facts::new().exact_word_difference(&a, &b, &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert_eq!(
        Facts::new().exact_word_difference(&a, &a, &mut budget),
        Err(LogicError::Budget)
    );
}
