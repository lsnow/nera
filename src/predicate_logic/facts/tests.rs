use super::*;

type Value = TypedLogicValue<u32, u32, u32>;
type Facts = EstablishedFacts<u32, u32, u32>;
mod batch;
mod boolean;
mod candidates;
mod evaluation;
mod mixed;
mod observations;
mod offsets;
mod typed_captures;

fn word(atom: u32, lower: u64, upper: u64) -> Value {
    Value {
        ty: LogicType::Usize,
        value: LogicValue::Word(AffineValue::variable(atom, lower, upper).unwrap()),
    }
}

fn constant(value: u64) -> Value {
    Value {
        ty: LogicType::Usize,
        value: LogicValue::Word(AffineValue::exact(value)),
    }
}

fn expression(nodes: Vec<(LogicType<u32>, LogicNodeKind<u32>)>) -> LogicExpression<u32> {
    LogicExpression {
        root: nodes.len() as u32 - 1,
        nodes: nodes
            .into_iter()
            .map(|(ty, kind)| LogicNode { ty, kind })
            .collect(),
    }
}

// x + 1 <= y. These are established snapshots, not arbitrary assumptions at a
// source program point. The resource adapter is tested separately.
fn successor() -> LogicExpression<u32> {
    use LogicNodeKind::*;
    expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Existential(0))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(0, 1)),
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Bool, LessEqual(2, 3)),
    ])
}

fn facts(e: &LogicExpression<u32>, x: Option<Value>, y: Option<Value>) -> Facts {
    let mut facts = Facts::new();
    facts
        .extend(
            e,
            &[(0, x), (1, Some(constant(1))), (3, y)],
            &mut LogicBudget::default(),
        )
        .unwrap();
    facts
}

#[test]
fn affine_premise_implies_strict_relation_without_runtime_or_resource_types() {
    let x = word(10, 0, u64::MAX);
    let y = word(20, 0, u64::MAX);
    let facts = facts(&successor(), Some(x.clone()), Some(y.clone()));
    for op in [Comparison::Less, Comparison::LessEqual] {
        assert_eq!(
            facts.entails(op, &x, &y, &mut LogicBudget::default()),
            Ok(true)
        );
    }
    assert_eq!(
        facts.entails(Comparison::Equal, &x, &y, &mut LogicBudget::default()),
        Ok(false)
    );
    assert_eq!(
        facts.entails(Comparison::LessEqual, &y, &x, &mut LogicBudget::default()),
        Ok(false)
    );
    // Equal abstract ranges and different identities are not interchangeable.
    assert_eq!(
        facts.entails(
            Comparison::Less,
            &word(11, 0, u64::MAX),
            &y,
            &mut LogicBudget::default()
        ),
        Ok(false)
    );
    let mut wrong_type = x.clone();
    wrong_type.ty = LogicType::U64;
    assert_eq!(
        facts.entails(
            Comparison::Less,
            &wrong_type,
            &y,
            &mut LogicBudget::default()
        ),
        Err(LogicError::TypeMismatch)
    );
    let mut other_y = y.clone();
    other_y.ty = LogicType::U64;
    assert_eq!(
        facts.entails(
            Comparison::Less,
            &wrong_type,
            &other_y,
            &mut LogicBudget::default()
        ),
        Ok(false)
    );
}

#[test]
fn hidden_arithmetic_yields_bounds_without_claiming_fresh_arithmetic_is_defined() {
    let x = word(10, 0, u64::MAX);
    let facts = facts(&successor(), Some(x.clone()), Some(constant(7)));
    let refined = facts
        .refine(x.clone(), &mut LogicBudget::default())
        .unwrap();
    let LogicValue::Word(value) = refined.value else {
        panic!()
    };
    assert_eq!((value.lower, value.upper), (0, 6));
    let LogicValue::Word(original) = &x.value else {
        panic!()
    };
    assert_eq!(
        original.add(&AffineValue::exact(1)),
        Err(LogicError::Overflow)
    );
    assert!(value.add(&AffineValue::exact(1)).is_ok());
}

#[test]
fn signed_projection_rounds_bounds_in_the_safe_direction() {
    use LogicNodeKind::*;
    let x = word(10, 0, u64::MAX);
    for (op, lower, upper) in [(LessEqual(3, 4), 0, 7), (Less(4, 3), 8, u64::MAX)] {
        let e = expression(vec![
            (LogicType::Usize, Binder(LogicBinder::Existential(0))),
            (
                LogicType::Usize,
                Scale {
                    operand: 0,
                    factor: 2,
                },
            ),
            (LogicType::Usize, Word(1)),
            (LogicType::Usize, Add(1, 2)),
            (LogicType::Usize, Word(16)),
            (LogicType::Bool, op),
        ]);
        let mut facts = Facts::new();
        facts
            .extend(&e, &[(0, Some(x.clone()))], &mut LogicBudget::default())
            .unwrap();
        let LogicValue::Word(refined) = facts
            .refine(x.clone(), &mut LogicBudget::default())
            .unwrap()
            .value
        else {
            panic!()
        };
        assert_eq!((refined.lower, refined.upper), (lower, upper));
    }
    let e = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Existential(0))),
        (LogicType::Usize, Word(2)),
        (LogicType::Usize, Sub(0, 1)),
        (LogicType::Usize, Word(5)),
        (LogicType::Bool, LessEqual(3, 2)),
    ]);
    let mut facts = Facts::new();
    facts
        .extend(&e, &[(0, Some(x.clone()))], &mut LogicBudget::default())
        .unwrap();
    let LogicValue::Word(refined) = facts.refine(x, &mut LogicBudget::default()).unwrap().value
    else {
        panic!()
    };
    assert_eq!(refined.lower, 7);
}

#[test]
fn unavailable_leaves_and_disjunctions_never_become_premises() {
    let x = word(10, 0, u64::MAX);
    let y = word(20, 0, u64::MAX);
    let missing = facts(&successor(), None, Some(y.clone()));
    assert_eq!(
        missing.entails(Comparison::Less, &x, &y, &mut LogicBudget::default()),
        Ok(false)
    );
    for disjunction in [true, false] {
        let mut e = successor();
        if disjunction {
            e.nodes.push(LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Bool(true),
            });
            e.nodes.push(LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Or(4, 5),
            });
            e.root = 6;
        } else {
            e.nodes.push(LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Not(4),
            });
            e.root = 5;
        }
        assert_eq!(
            facts(&e, Some(x.clone()), Some(y.clone())).entails(
                Comparison::Less,
                &x,
                &y,
                &mut LogicBudget::default()
            ),
            Ok(false)
        );
    }
}

#[test]
fn boolean_facts_keep_identity_and_negation() {
    let hidden = Value {
        ty: LogicType::Bool,
        value: LogicValue::BoolAtom {
            atom: 1,
            negated: false,
            known: None,
        },
    };
    let e = expression(vec![
        (
            LogicType::Bool,
            LogicNodeKind::Binder(LogicBinder::Existential(0)),
        ),
        (LogicType::Bool, LogicNodeKind::Not(0)),
    ]);
    let mut facts = Facts::new();
    facts
        .extend(
            &e,
            &[(0, Some(hidden.clone()))],
            &mut LogicBudget::default(),
        )
        .unwrap();
    assert_eq!(
        facts
            .refine(hidden, &mut LogicBudget::default())
            .unwrap()
            .value,
        LogicValue::Bool(Some(false))
    );
    let foreign = Value {
        ty: LogicType::Bool,
        value: LogicValue::BoolAtom {
            atom: 2,
            negated: false,
            known: None,
        },
    };
    assert_eq!(
        facts.refine(foreign.clone(), &mut LogicBudget::default()),
        Ok(foreign)
    );
}

#[test]
fn malformed_snapshots_and_exhausted_shared_budget_fail_closed() {
    let x = word(10, 0, u64::MAX);
    let y = word(20, 0, u64::MAX);
    let mut e = successor();
    e.nodes[2].kind = LogicNodeKind::Add(2, 1);
    assert_eq!(
        Facts::new().extend(
            &e,
            &[(0, Some(x.clone())), (3, Some(y.clone()))],
            &mut LogicBudget::default()
        ),
        Err(LogicError::InvalidNode)
    );
    let mut facts = Facts::new();
    let mut budget = LogicBudget::default();
    facts
        .extend(
            &successor(),
            &[(0, Some(x.clone())), (3, Some(y.clone()))],
            &mut budget,
        )
        .unwrap();
    budget.remaining = 0;
    assert_eq!(
        facts.entails(Comparison::Less, &x, &y, &mut budget),
        Err(LogicError::Budget)
    );
    assert_eq!(
        facts.refine(x.clone(), &mut budget),
        Err(LogicError::Budget)
    );
    assert_eq!(
        facts.extend(&successor(), &[(0, Some(x)), (3, Some(y))], &mut budget),
        Err(LogicError::Budget)
    );
}

#[test]
fn mathematical_coefficient_overflow_is_not_wrapped_into_a_proof() {
    use LogicNodeKind::*;
    let e = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Existential(0))),
        (
            LogicType::Usize,
            Scale {
                operand: 0,
                factor: u64::MAX,
            },
        ),
        (
            LogicType::Usize,
            Scale {
                operand: 1,
                factor: u64::MAX,
            },
        ),
        (LogicType::Usize, Word(1)),
        (LogicType::Bool, LessEqual(2, 3)),
    ]);
    assert_eq!(
        Facts::new().extend(&e, &[(0, Some(word(1, 0, 1)))], &mut LogicBudget::default()),
        Err(LogicError::Overflow)
    );
}

#[test]
fn impossible_affine_premise_is_rejected_without_publishing_partial_facts() {
    let x = word(10, 0, u64::MAX);
    let mut facts = Facts::new();
    assert_eq!(
        facts.extend(
            &successor(),
            &[(0, Some(x.clone())), (3, Some(x.clone()))],
            &mut LogicBudget::default()
        ),
        Err(LogicError::Unproved)
    );
    assert_eq!(
        facts.entails(Comparison::Less, &x, &x, &mut LogicBudget::default()),
        Ok(false)
    );
    let e = expression(vec![
        (
            LogicType::Bool,
            LogicNodeKind::Binder(LogicBinder::Existential(0)),
        ),
        (LogicType::Bool, LogicNodeKind::Bool(false)),
        (LogicType::Bool, LogicNodeKind::And(0, 1)),
    ]);
    let b = Value {
        ty: LogicType::Bool,
        value: LogicValue::BoolAtom {
            atom: 3,
            negated: false,
            known: None,
        },
    };
    assert_eq!(
        facts.extend(&e, &[(0, Some(b.clone()))], &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
    assert_eq!(facts.refine(b.clone(), &mut LogicBudget::default()), Ok(b));
}

fn add_relation(facts: &mut Facts, a: Value, b: Value, op: Comparison) {
    let comparison = match op {
        Comparison::Equal => LogicNodeKind::Equal(0, 1),
        Comparison::Less => LogicNodeKind::Less(0, 1),
        Comparison::LessEqual => LogicNodeKind::LessEqual(0, 1),
    };
    let e = expression(vec![
        (a.ty, LogicNodeKind::Binder(LogicBinder::Parameter(0))),
        (b.ty, LogicNodeKind::Binder(LogicBinder::Parameter(1))),
        (LogicType::Bool, comparison),
    ]);
    facts
        .extend(
            &e,
            &[(0, Some(a)), (1, Some(b))],
            &mut LogicBudget::default(),
        )
        .unwrap();
}

#[test]
fn transitive_guarantees_preserve_strictness_types_and_atom_identity() {
    let x = word(10, 0, u64::MAX);
    let y = word(20, 0, u64::MAX);
    let z = word(30, 0, u64::MAX);
    let mut facts = Facts::new();
    add_relation(&mut facts, x.clone(), y.clone(), Comparison::LessEqual);
    add_relation(&mut facts, y.clone(), z.clone(), Comparison::Less);
    assert_eq!(
        facts.entails(Comparison::Less, &x, &z, &mut LogicBudget::default()),
        Ok(true)
    );
    assert_eq!(
        facts.entails(Comparison::Equal, &x, &z, &mut LogicBudget::default()),
        Ok(false)
    );
    assert_eq!(
        facts.entails(Comparison::LessEqual, &z, &x, &mut LogicBudget::default()),
        Ok(false)
    );
    assert_eq!(
        facts.entails(
            Comparison::Less,
            &word(11, 0, u64::MAX),
            &z,
            &mut LogicBudget::default()
        ),
        Ok(false)
    );
    let mut a = x.clone();
    let mut b = z.clone();
    a.ty = LogicType::U64;
    b.ty = LogicType::U64;
    assert_eq!(
        facts.entails(Comparison::Less, &a, &b, &mut LogicBudget::default()),
        Ok(false)
    );
    let mut weak = Facts::new();
    add_relation(&mut weak, x.clone(), y.clone(), Comparison::LessEqual);
    add_relation(&mut weak, y, z.clone(), Comparison::LessEqual);
    assert_eq!(
        weak.entails(Comparison::Less, &x, &z, &mut LogicBudget::default()),
        Ok(false)
    );
    assert_eq!(
        weak.entails(Comparison::LessEqual, &x, &z, &mut LogicBudget::default()),
        Ok(true)
    );
}

#[test]
fn transitive_bounds_refine_only_the_queried_snapshot() {
    let x = word(10, 0, u64::MAX);
    let y = word(20, 0, u64::MAX);
    let mut facts = Facts::new();
    add_relation(&mut facts, x.clone(), y.clone(), Comparison::LessEqual);
    add_relation(&mut facts, y, constant(7), Comparison::Less);
    let LogicValue::Word(refined) = facts
        .refine(x.clone(), &mut LogicBudget::default())
        .unwrap()
        .value
    else {
        panic!()
    };
    assert_eq!((refined.lower, refined.upper), (0, 6));
    assert_eq!(x, word(10, 0, u64::MAX));
    let foreign = word(11, 0, u64::MAX);
    assert_eq!(
        facts.refine(foreign.clone(), &mut LogicBudget::default()),
        Ok(foreign)
    );
}

#[test]
fn inconsistent_cycles_fail_without_ex_falso_or_budget_fallback() {
    let x = word(10, 0, u64::MAX);
    let y = word(20, 0, u64::MAX);
    let mut facts = Facts::new();
    add_relation(&mut facts, x.clone(), y.clone(), Comparison::Less);
    assert_eq!(
        facts.extend_difference(&y, &x, 0, &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
    // The rejected cycle cannot poison the original established strict order.
    assert_eq!(
        facts.entails(Comparison::Less, &x, &y, &mut LogicBudget::default()),
        Ok(true)
    );
    let mut weak_cycle = Facts::new();
    add_relation(&mut weak_cycle, x.clone(), y.clone(), Comparison::LessEqual);
    add_relation(&mut weak_cycle, y.clone(), x.clone(), Comparison::LessEqual);
    assert_eq!(
        weak_cycle.entails(Comparison::Equal, &x, &y, &mut LogicBudget::default()),
        Ok(true)
    );
    let mut budget = LogicBudget { remaining: 30 };
    assert_eq!(
        weak_cycle.entails(Comparison::Equal, &x, &y, &mut budget),
        Err(LogicError::Budget)
    );
}

#[test]
fn composite_queries_check_every_machine_intermediate_before_cancellation() {
    use LogicNodeKind::*;
    let x = word(10, 0, u64::MAX);
    let y = word(20, 0, u64::MAX);
    let e = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Word(1)),
        (LogicType::Usize, Add(0, 1)),
        (LogicType::Usize, Sub(2, 0)),
        (LogicType::Bool, Equal(3, 1)),
    ]);
    let mut facts = Facts::new();
    assert_eq!(
        facts.proves(&e, &[(0, Some(x.clone()))], &mut LogicBudget::default()),
        Ok(false)
    );
    add_relation(&mut facts, x.clone(), y.clone(), Comparison::LessEqual);
    add_relation(&mut facts, y, constant(7), Comparison::Less);
    assert_eq!(
        facts.proves(&e, &[(0, Some(x.clone()))], &mut LogicBudget::default()),
        Ok(true)
    );
    assert_eq!(
        facts.proves(&e, &[(0, None)], &mut LogicBudget::default()),
        Ok(false)
    );
    assert_eq!(
        facts.proves(
            &e,
            &[(0, Some(word(11, 0, u64::MAX)))],
            &mut LogicBudget::default()
        ),
        Ok(false)
    );
    let mut underflow = e.clone();
    underflow.nodes[2].kind = Sub(0, 1);
    underflow.nodes[3].kind = Add(2, 1);
    underflow.nodes[4].kind = Equal(3, 0);
    assert_eq!(
        facts.proves(&underflow, &[(0, Some(x))], &mut LogicBudget::default()),
        Ok(false)
    );
}

#[test]
fn common_affine_terms_cancel_before_transitive_queries() {
    let x = word(10, 0, 100);
    let y = word(20, 0, 100);
    let z = word(30, 0, 100);
    let w = word(40, 0, 100);
    let sum = |a: &Value, b: &Value| {
        let (LogicValue::Word(a), LogicValue::Word(b)) = (&a.value, &b.value) else {
            panic!()
        };
        Value {
            ty: LogicType::Usize,
            value: LogicValue::Word(a.add(b).unwrap()),
        }
    };
    let mut facts = Facts::new();
    add_relation(&mut facts, sum(&x, &z), sum(&y, &z), Comparison::LessEqual);
    add_relation(&mut facts, y, w.clone(), Comparison::Less);
    assert_eq!(
        facts.entails(Comparison::Less, &x, &w, &mut LogicBudget::default()),
        Ok(true)
    );
}
