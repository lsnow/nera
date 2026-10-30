use super::*;

#[test]
fn shared_word_syntax_is_instantiated_per_nominal_domain() {
    let terms = [
        Term::Operand(()), // usize
        Term::Operand(()), // u64
        Term::Operand(()), // shared word literal
        Term::Scale(2, 2),
        Term::LessEqual(0, 3),
        Term::LessEqual(1, 3),
        Term::And(4, 5),
        Term::Operand(()), // bool
        Term::Or(6, 7),
    ];
    let inputs = BTreeMap::from([
        (0, InputType::Usize),
        (1, InputType::U64),
        (2, InputType::Word),
        (7, InputType::Bool),
    ]);
    let query = elaborate::<(), _>(&terms, 8, &inputs, &mut LogicBudget::default()).unwrap();
    let types = query
        .operands
        .iter()
        .filter(|(_, source)| *source == 2)
        .map(|(id, _)| query.expression.nodes[*id as usize].ty)
        .collect::<BTreeSet<_>>();
    assert_eq!(types, BTreeSet::from([LogicType::Usize, LogicType::U64]));
    assert_eq!(
        query.expression.nodes[query.expression.root as usize].ty,
        LogicType::Bool
    );
}

#[test]
fn malformed_and_cross_domain_queries_do_not_acquire_a_type() {
    for (terms, inputs, error) in [
        (
            vec![Term::Operand(()), Term::Operand(()), Term::Equal(0, 1)],
            BTreeMap::from([(0, InputType::U64), (1, InputType::Usize)]),
            LogicError::TypeMismatch,
        ),
        (
            vec![Term::Operand(()), Term::Less(0, 0)],
            BTreeMap::from([(0, InputType::Bool)]),
            LogicError::TypeMismatch,
        ),
        (
            vec![Term::Operand(()), Term::Not(0)],
            BTreeMap::from([(0, InputType::Word)]),
            LogicError::TypeMismatch,
        ),
        (vec![Term::Not(0)], BTreeMap::new(), LogicError::InvalidNode),
        (
            vec![Term::Operand(()), Term::Not(0)],
            BTreeMap::new(),
            LogicError::Unbound,
        ),
    ] {
        assert!(matches!(
            elaborate::<(), _>(&terms,terms.len() as u32-1,&inputs,&mut LogicBudget::default()),
            Err(actual) if actual == error
        ));
    }
}

#[test]
fn shared_queries_have_bounded_depth_and_work() {
    let mut terms = vec![Term::Operand(())];
    for i in 0..MAX_EXPRESSION_DEPTH as u32 {
        terms.push(Term::Not(i));
    }
    let inputs = BTreeMap::from([(0, InputType::Bool)]);
    assert!(matches!(
        elaborate::<(), _>(
            &terms,
            terms.len() as u32 - 1,
            &inputs,
            &mut LogicBudget::default()
        ),
        Err(LogicError::Budget)
    ));
    let mut budget = LogicBudget::default();
    budget.charge(MAX_SUBSTITUTION_NODES - 1).unwrap();
    assert!(matches!(
        elaborate::<(), _>(&terms[..2], 1, &inputs, &mut budget),
        Err(LogicError::Budget)
    ));
}

#[test]
fn unreachable_syntax_is_preserved_and_the_root_remains_last() {
    let terms = [
        Term::Operand(()),
        Term::Not(0),
        Term::Operand(()),
        Term::Scale(2, u64::MAX),
    ];
    let inputs = BTreeMap::from([(0, InputType::Bool), (2, InputType::Word)]);
    for root in [0, 1] {
        let query = elaborate::<(), _>(&terms, root, &inputs, &mut LogicBudget::default()).unwrap();
        assert_eq!(
            query.expression.root as usize + 1,
            query.expression.nodes.len()
        );
        assert!(
            query
                .expression
                .nodes
                .iter()
                .any(|node| matches!(node.kind, LogicNodeKind::Scale { .. }))
        );
        let mut expression = query.expression;
        let mut types = vec![];
        for (id, _) in query.operands {
            let node = &mut expression.nodes[id as usize];
            node.kind = LogicNodeKind::Binder(LogicBinder::Parameter(types.len() as u32));
            types.push(node.ty);
        }
        assert_eq!(
            expression.validate(
                &types,
                &[],
                &|_, _, _, _| None,
                &|_, _| None,
                &mut LogicBudget::default()
            ),
            Ok(LogicType::Bool)
        );
    }
}
