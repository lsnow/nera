use super::*;
use LogicNodeKind::*;

pub(super) fn captured(ty: LogicType<u32>, op: LogicNodeKind<u32>) -> Value {
    let e = expression(vec![
        (ty, Binder(LogicBinder::Parameter(0))),
        (ty, Binder(LogicBinder::Parameter(1))),
        (LogicType::Bool, op),
    ]);
    let mut x = word(1, 0, 20);
    x.ty = ty;
    let mut y = word(2, 0, 20);
    y.ty = ty;
    e.evaluate_for_capture(
        &[x, y],
        &[],
        &mut |_, _, _, _| Err(LogicError::Unbound),
        &mut |_, _| Err(LogicError::Unbound),
        &mut LogicBudget::default(),
    )
    .unwrap()
}
fn import(facts: &mut Facts, value: Value) -> Result<(), LogicError> {
    facts.extend(
        &expression(vec![(LogicType::Bool, Binder(LogicBinder::Parameter(0)))]),
        &[(0, Some(value))],
        &mut LogicBudget::default(),
    )
}

#[test]
fn captured_comparison_guarantees_feed_only_their_recorded_numeric_type() {
    for ty in [LogicType::U64, LogicType::Usize] {
        for (kind, op) in [
            (Less(0, 1), Comparison::Less),
            (LessEqual(0, 1), Comparison::LessEqual),
            (Equal(0, 1), Comparison::Equal),
        ] {
            let capture = captured(ty, kind);
            let LogicValue::BoolComparison { word_type, .. } = capture.value else {
                panic!()
            };
            assert_eq!(word_type.logic_type::<u32>(), ty);
            let mut facts = Facts::new();
            import(&mut facts, capture).unwrap();
            for query_type in [LogicType::U64, LogicType::Usize] {
                let mut a = word(1, 0, 20);
                a.ty = query_type;
                let mut b = word(2, 0, 20);
                b.ty = query_type;
                assert_eq!(
                    facts.entails(op, &a, &b, &mut LogicBudget::default()),
                    Ok(query_type == ty)
                );
            }
        }
    }
}

#[test]
fn typed_numeric_facts_refine_nested_comparison_captures_without_equating_types() {
    for ty in [LogicType::U64, LogicType::Usize] {
        let mut x = word(1, 0, 20);
        x.ty = ty;
        let mut y = word(2, 0, 20);
        y.ty = ty;
        let mut facts = Facts::new();
        add_relation(&mut facts, x, y, Comparison::Less);
        for target_type in [LogicType::U64, LogicType::Usize] {
            let value = Value {
                ty: LogicType::Bool,
                value: LogicValue::boolean_binary(
                    BooleanOperation::Or,
                    LogicValue::Bool(Some(false)),
                    captured(target_type, Less(0, 1)).value,
                    false,
                    &mut LogicBudget::default(),
                )
                .unwrap(),
            };
            let result = facts.refine(value, &mut LogicBudget::default()).unwrap();
            assert_eq!(
                result.value.known_boolean(),
                (ty == target_type).then_some(true)
            );
        }
    }
}

#[test]
fn capture_structure_and_source_clause_share_typed_numeric_propositions() {
    let mut facts = Facts::new();
    let unknown = Value {
        ty: LogicType::Bool,
        value: LogicValue::BoolAtom {
            atom: 3,
            negated: false,
            known: None,
        },
    };
    let formula = Value {
        ty: LogicType::Bool,
        value: LogicValue::boolean_binary(
            BooleanOperation::Or,
            unknown.value.clone(),
            captured(LogicType::Usize, Less(0, 1)).value,
            false,
            &mut LogicBudget::default(),
        )
        .unwrap(),
    };
    import(&mut facts, formula).unwrap();
    let mut negative = unknown;
    negative.value = negative.value.bool_not();
    import(&mut facts, negative).unwrap();
    let source = expression(vec![
        (LogicType::Usize, Binder(LogicBinder::Parameter(0))),
        (LogicType::Usize, Binder(LogicBinder::Parameter(1))),
        (LogicType::Bool, Less(0, 1)),
    ]);
    assert_eq!(
        facts.proves(
            &source,
            &[(0, Some(word(1, 0, 20))), (1, Some(word(2, 0, 20)))],
            &mut LogicBudget::default()
        ),
        Ok(true)
    );
    let before = facts.facts.len();
    assert_eq!(
        import(&mut facts, captured(LogicType::Usize, LessEqual(1, 0))),
        Err(LogicError::Unproved)
    );
    assert_eq!(facts.facts.len(), before);
    // The same atom numbers in a distinct numeric type remain independent.
    import(&mut facts, captured(LogicType::U64, LessEqual(1, 0))).unwrap();
}

#[test]
fn captured_disequality_is_symmetric_without_choosing_an_order() {
    for ty in [LogicType::U64, LogicType::Usize] {
        let mut facts = Facts::new();
        let mut unequal = captured(ty, Equal(0, 1));
        unequal.value = unequal.value.bool_not();
        import(&mut facts, unequal).unwrap();
        let reversed = facts
            .refine(captured(ty, Equal(1, 0)), &mut LogicBudget::default())
            .unwrap();
        assert_eq!(reversed.value.known_boolean(), Some(false));
        for op in [Less(0, 1), Less(1, 0)] {
            assert_eq!(
                facts
                    .refine(captured(ty, op), &mut LogicBudget::default())
                    .unwrap()
                    .value
                    .known_boolean(),
                None
            );
        }
    }
}
