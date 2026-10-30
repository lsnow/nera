use super::*;
use LogicNodeKind::*;

fn at_most_five() -> LogicExpression<u32> {
    expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(5)),
        (LogicType::Bool, LessEqual(0, 1)),
    ])
}

#[test]
fn constraint_import_is_atomic_on_joint_conflict_and_exhaustion() {
    let mut facts = Facts::new();
    let limit = at_most_five();
    let mut opposite = limit.clone();
    opposite.nodes[2].kind = Less(1, 0);
    let leaves = [(0, Some(word(1, 0, u64::MAX)))];
    let batch = [(&limit, leaves.as_slice()), (&opposite, leaves.as_slice())];
    assert_eq!(
        facts.extend_batch(&batch, &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
    assert!(facts.facts.is_empty());
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES - 1).unwrap();
    assert_eq!(
        facts.extend_batch(&batch, &mut budget),
        Err(LogicError::Budget)
    );
    assert!(facts.facts.is_empty());
    assert_eq!(
        facts.proves(&limit, &leaves, &mut LogicBudget::default()),
        Ok(false)
    );
}

#[test]
fn observations_and_guarantees_publish_as_one_consistent_batch() {
    let mut facts = Facts::new();
    let limit = at_most_five();
    let input = word(1, 0, u64::MAX);
    let leaves = [(0, Some(input.clone()))];
    let batch = [(&limit, leaves.as_slice())];
    // Each family is consistent alone, but x >= 6 and x <= 5 conflict.
    let differences = [(constant(0), input.clone(), -6)];
    assert_eq!(
        facts.extend_inputs(&[], &differences, &batch, &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
    assert!(facts.facts.is_empty());
    assert_eq!(
        facts.proves(&limit, &leaves, &mut LogicBudget::default()),
        Ok(false)
    );
    assert_eq!(
        facts.entails(
            Comparison::LessEqual,
            &constant(6),
            &input,
            &mut LogicBudget::default()
        ),
        Ok(false)
    );
    let differences = [(input, constant(0), 7)];
    let mut budget = LogicBudget { remaining: 1 };
    assert_eq!(
        facts.extend_inputs(&[], &differences, &batch, &mut budget),
        Err(LogicError::Budget)
    );
    assert!(facts.facts.is_empty());
    facts
        .extend_inputs(&[], &differences, &batch, &mut LogicBudget::default())
        .unwrap();
    assert_eq!(
        facts.proves(&limit, &leaves, &mut LogicBudget::default()),
        Ok(true)
    );
}

#[test]
fn prepared_graph_tracks_extensions_but_never_query_domains() {
    let mut facts = Facts::new();
    let mut limit = at_most_five();
    let leaves = [(0, Some(word(1, 0, u64::MAX)))];
    facts
        .extend(&limit, &leaves, &mut LogicBudget::default())
        .unwrap();
    limit.nodes[1].kind = Word(3);
    assert_eq!(
        facts.proves(&limit, &leaves, &mut LogicBudget::default()),
        Ok(false)
    );
    facts
        .extend(&limit, &leaves, &mut LogicBudget::default())
        .unwrap();
    assert_eq!(
        facts.proves(&limit, &leaves, &mut LogicBudget::default()),
        Ok(true)
    );
    // A failed extension must preserve both the catalog and prepared graph.
    let mut opposite = limit.clone();
    opposite.nodes[2].kind = Less(1, 0);
    assert_eq!(
        facts.extend(&opposite, &leaves, &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
    assert_eq!(
        facts.proves(&limit, &leaves, &mut LogicBudget::default()),
        Ok(true)
    );
    limit.nodes[1].kind = Word(2);
    assert_eq!(
        facts.proves(
            &limit,
            &[(0, Some(word(1, 0, 2)))],
            &mut LogicBudget::default()
        ),
        Ok(true)
    );
    assert_eq!(
        facts.proves(&limit, &leaves, &mut LogicBudget::default()),
        Ok(false)
    );
    assert_eq!(
        facts.proves(
            &limit,
            &[(0, Some(word(1, 4, 5)))],
            &mut LogicBudget::default()
        ),
        Err(LogicError::Unproved)
    );
    assert_eq!(
        facts.proves(&limit, &leaves, &mut LogicBudget::default()),
        Ok(false)
    );
}

#[test]
fn pending_queries_never_supply_each_others_truth_or_arithmetic_domain() {
    let mut facts = Facts::new();
    let limit = at_most_five();
    let next = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(0, 1)),
        (LogicType::Usize, Word(6)),
        (LogicType::Bool, LessEqual(2, 3)),
    ]);
    let leaves = [(0, Some(word(1, 0, u64::MAX)))];
    for batch in [
        [(&limit, leaves.as_slice()), (&next, leaves.as_slice())],
        [(&next, leaves.as_slice()), (&limit, leaves.as_slice())],
    ] {
        assert_eq!(
            facts.proves_batch(&batch, &mut LogicBudget::default()),
            Ok(vec![false, false])
        );
    }
    assert!(facts.facts.is_empty());
    facts
        .extend(&limit, &leaves, &mut LogicBudget::default())
        .unwrap();
    assert_eq!(
        facts.proves_batch(
            &[(&limit, &leaves), (&next, &leaves)],
            &mut LogicBudget::default()
        ),
        Ok(vec![true, true])
    );
}

#[test]
fn cancelling_operands_still_checks_their_domains_against_saved_facts() {
    let mut facts = Facts::new();
    let limit = at_most_five();
    facts
        .extend(
            &limit,
            &[(0, Some(word(1, 0, u64::MAX)))],
            &mut LogicBudget::default(),
        )
        .unwrap();
    let cancellation = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Sub(0, 0)),
    ]);
    assert_eq!(
        facts.evaluate_scalar(
            &cancellation,
            &[(0, Some(word(1, 6, 10)))],
            &mut LogicBudget::default()
        ),
        Err(LogicError::Unproved)
    );
    assert_eq!(
        facts.evaluate_scalar(
            &cancellation,
            &[(0, Some(word(1, 0, 5)))],
            &mut LogicBudget::default()
        ),
        Ok(Some(constant(0)))
    );

    // A range request must refine even a leaf with no arithmetic operations.
    let leaf = expression(vec![(LogicType::Usize, Binder(LogicBinder::Parameter(0)))]);
    let result = facts
        .evaluate_word(
            &leaf,
            &[(0, Some(word(1, 0, u64::MAX)))],
            &mut LogicBudget::default(),
        )
        .unwrap()
        .unwrap();
    assert_eq!(result, word(1, 0, 5));
}
