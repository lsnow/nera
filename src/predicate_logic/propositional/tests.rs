use super::*;
fn lit(node: usize) -> Literal {
    Literal::positive(node)
}

#[test]
fn model_admission_is_read_only_and_errors_discard_partial_results() {
    let nodes = [Node::Input(0), Node::Input(1)];
    let queries = [lit(0), lit(1)];
    let observations = [not(0), lit(1)];
    assert_eq!(
        forced_many_with_models(
            &nodes,
            &[None; 2],
            &queries,
            &observations,
            &mut LogicBudget::default(),
            &mut |values, budget| {
                budget.charge(1)?;
                Ok(!values[0])
            },
        ),
        Ok(vec![Some(true), None])
    );
    assert_eq!(
        forced_many_with_models(
            &nodes,
            &[None; 2],
            &queries,
            &observations,
            &mut LogicBudget::default(),
            &mut |_, _| Ok(false),
        ),
        Err(LogicError::Unproved)
    );
    let mut visited = 0;
    assert_eq!(
        forced_many_with_models(
            &nodes,
            &[None; 2],
            &queries,
            &observations,
            &mut LogicBudget::default(),
            &mut |_, budget| {
                visited += 1;
                if visited == 2 {
                    budget.charge(crate::predicate_logic::MAX_SUBSTITUTION_NODES)?;
                }
                Ok(true)
            },
        ),
        Err(LogicError::Budget)
    );
    assert_eq!(visited, 2);
    assert_eq!(
        forced_many_with_models(
            &nodes,
            &[None; 2],
            &queries,
            &[lit(9)],
            &mut LogicBudget::default(),
            &mut |_, _| panic!("invalid projection"),
        ),
        Err(LogicError::InvalidNode)
    );
}
fn not(node: usize) -> Literal {
    Literal {
        node,
        negated: true,
    }
}

#[test]
fn joint_guarantees_force_only_results_shared_by_all_models() {
    use BooleanOperation::Or;
    let nodes = [
        Node::Input(10),
        Node::Input(20),
        Node::Gate(Or, lit(0), lit(1)),
        Node::Gate(Or, lit(0), not(1)),
    ];
    let known = [None, None, Some(true), Some(true)];
    assert_eq!(
        forced(&nodes, &known, lit(0), &mut LogicBudget::default()),
        Ok(Some(true))
    );
    assert_eq!(
        forced(&nodes, &known, not(0), &mut LogicBudget::default()),
        Ok(Some(false))
    );
    assert_eq!(
        forced(&nodes, &known, lit(1), &mut LogicBudget::default()),
        Ok(None)
    );
    let weak = [None, None, Some(true), None];
    assert_eq!(
        forced(&nodes, &weak, lit(0), &mut LogicBudget::default()),
        Ok(None)
    );
    assert_eq!(known, [None, None, Some(true), Some(true)]);
}

#[test]
fn inconsistent_global_guarantees_are_not_vacuous_proofs() {
    use BooleanOperation::Or;
    let nodes = [
        Node::Input(0),
        Node::Input(1),
        Node::Gate(Or, lit(0), lit(1)),
        Node::Gate(Or, lit(0), not(1)),
        Node::Gate(Or, not(0), lit(1)),
        Node::Gate(Or, not(0), not(1)),
    ];
    let known = [None, None, Some(true), Some(true), Some(true), Some(true)];
    assert_eq!(
        forced(&nodes, &known, lit(0), &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
    assert_eq!(
        forced(
            &[Node::Constant(true)],
            &[Some(false)],
            lit(0),
            &mut LogicBudget::default()
        ),
        Err(LogicError::Unproved)
    );
}

#[test]
fn input_identity_is_explicit_and_fixed_inputs_do_not_expand_the_search() {
    use BooleanOperation::Equal;
    let shared = [
        Node::Input(100),
        Node::Input(100),
        Node::Gate(Equal, lit(0), lit(1)),
    ];
    assert_eq!(
        forced(&shared, &[None; 3], lit(2), &mut LogicBudget::default()),
        Ok(Some(true))
    );
    let distinct = [
        Node::Input(100),
        Node::Input(101),
        Node::Gate(Equal, lit(0), lit(1)),
    ];
    assert_eq!(
        forced(&distinct, &[None; 3], lit(2), &mut LogicBudget::default()),
        Ok(None)
    );
    assert_eq!(
        forced(
            &shared,
            &[Some(true), Some(false), None],
            lit(2),
            &mut LogicBudget::default()
        ),
        Err(LogicError::Unproved)
    );
    let nodes = (0..64).map(Node::Input).collect::<Vec<_>>();
    assert_eq!(
        forced(
            &nodes,
            &[Some(true); 64],
            lit(63),
            &mut LogicBudget::default()
        ),
        Ok(Some(true))
    );
    assert_eq!(
        forced(&nodes, &[None; 64], lit(63), &mut LogicBudget::default()),
        Err(LogicError::Budget)
    );
}

#[test]
fn malformed_graphs_and_incomplete_enumeration_fail_closed() {
    assert_eq!(
        forced(&[Node::Input(0)], &[], lit(0), &mut LogicBudget::default()),
        Err(LogicError::InvalidNode)
    );
    assert_eq!(
        forced(
            &[Node::Gate(BooleanOperation::And, lit(0), lit(0))],
            &[None],
            lit(0),
            &mut LogicBudget::default()
        ),
        Err(LogicError::InvalidNode)
    );
    let mut budget = LogicBudget::default();
    budget
        .charge(super::super::MAX_SUBSTITUTION_NODES - 2)
        .unwrap();
    assert_eq!(
        forced(&[Node::Input(0)], &[None], lit(0), &mut budget),
        Err(LogicError::Budget)
    );
}

#[test]
fn batch_queries_share_models_without_treating_results_as_assumptions() {
    use BooleanOperation::Or;
    let nodes = [
        Node::Input(0),
        Node::Input(1),
        Node::Gate(Or, lit(0), lit(1)),
        Node::Gate(Or, lit(0), not(1)),
    ];
    let known = [None, None, Some(true), Some(true)];
    let queries = [lit(0), not(0), lit(1), not(1)];
    assert_eq!(
        forced_many(&nodes, &known, &queries, &mut LogicBudget::default()),
        Ok(vec![Some(true), Some(false), None, None])
    );
    let weak = [None, None, Some(true), None];
    assert_eq!(
        forced_many(&nodes, &weak, &queries, &mut LogicBudget::default()),
        Ok(vec![None; 4])
    );
    assert_eq!(
        forced_many(&nodes, &known, &[], &mut LogicBudget::default()),
        Err(LogicError::InvalidNode)
    );
    assert_eq!(
        forced_many(&nodes, &known, &[lit(4)], &mut LogicBudget::default()),
        Err(LogicError::InvalidNode)
    );
    let mut budget = LogicBudget::default();
    budget
        .charge(super::super::MAX_SUBSTITUTION_NODES - 12)
        .unwrap();
    assert_eq!(
        forced_many(&nodes, &known, &queries, &mut budget),
        Err(LogicError::Budget)
    );
}
