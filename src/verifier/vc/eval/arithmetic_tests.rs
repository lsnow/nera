use super::tests::function;
use super::*;
use crate::VirValueId;

fn add(arena: &mut VcArena, term: VcTerm) -> VcTermId {
    arena.intern(term, 65_536).unwrap()
}
fn run(arena: &VcArena, root: VcTermId) -> Option<AbstractBool> {
    evaluate_bool(
        arena,
        root,
        &BTreeSet::new(),
        SnapshotValues::Results(&[]),
        &function(),
        &mut VcQueryBudget::new(VcLimits::default()),
    )
}

#[test]
fn checked_arithmetic_matches_independent_u128_model() {
    let inputs: Vec<u64> = (0..12)
        .chain([u64::MAX / 2, u64::MAX / 2 + 1, u64::MAX - 1, u64::MAX])
        .collect();
    for &a in &inputs {
        for &b in &inputs {
            for op in 0..3 {
                let mut arena = VcArena::default();
                let x = add(&mut arena, VcTerm::U64(a));
                let y = add(&mut arena, VcTerm::U64(b));
                let term = match op {
                    0 => VcTerm::CheckedAdd(x, y),
                    1 => VcTerm::CheckedSub(x, y),
                    _ => VcTerm::CheckedScale(x, b),
                };
                let value = add(&mut arena, term);
                let expected = match op {
                    0 => Some(u128::from(a) + u128::from(b)),
                    1 => u128::from(a).checked_sub(u128::from(b)),
                    _ => Some(u128::from(a) * u128::from(b)),
                }
                .filter(|v| *v <= u128::from(u64::MAX));
                let root = add(&mut arena, VcTerm::Equal(value, value));
                assert_eq!(
                    run(&arena, root),
                    Some(if expected.is_some() {
                        AbstractBool::True
                    } else {
                        AbstractBool::Unknown
                    }),
                    "{a} op{op} {b}"
                );
                if let Some(expected) = expected {
                    let exact = add(&mut arena, VcTerm::U64(expected as u64));
                    let root = add(&mut arena, VcTerm::Equal(value, exact));
                    assert_eq!(run(&arena, root), Some(AbstractBool::True));
                    let wrong = add(&mut arena, VcTerm::U64((expected as u64) ^ 1));
                    let root = add(&mut arena, VcTerm::Equal(value, wrong));
                    assert_eq!(run(&arena, root), Some(AbstractBool::False));
                }
            }
        }
    }
}

#[test]
fn byte_range_queries_match_finite_sets_and_checked_endpoints() {
    for a in 0..5 {
        for b in 0..5 {
            for c in 0..5 {
                for d in 0..5 {
                    let mut arena = VcArena::default();
                    let ids = [a, b, c, d].map(|n| add(&mut arena, VcTerm::U64(n)));
                    let disjoint = a <= b && c <= d && !(a..b).any(|n| (c..d).contains(&n));
                    let contained = a <= b && c <= d && a <= c && d <= b;
                    for (node, expected) in [
                        (VcTerm::RangeDisjoint(ids), disjoint),
                        (VcTerm::RangeContains(ids), contained),
                    ] {
                        let root = add(&mut arena, node);
                        assert_eq!(
                            run(&arena, root),
                            Some(if expected {
                                AbstractBool::True
                            } else {
                                AbstractBool::False
                            }),
                            "{a}..{b}, {c}..{d}"
                        );
                    }
                }
            }
        }
    }
    let mut arena = VcArena::default();
    let max = add(&mut arena, VcTerm::U64(u64::MAX));
    let zero = add(&mut arena, VcTerm::U64(0));
    let root = add(&mut arena, VcTerm::RangeContains([zero, max, max, max]));
    assert_eq!(run(&arena, root), Some(AbstractBool::True));
    let one = add(&mut arena, VcTerm::U64(1));
    let bad = add(&mut arena, VcTerm::CheckedAdd(max, one));
    let root = add(&mut arena, VcTerm::RangeDisjoint([zero, bad, max, max]));
    assert_eq!(run(&arena, root), Some(AbstractBool::Unknown));
}

#[test]
fn undefined_arithmetic_is_not_a_boolean_and_short_circuit_is_ordered() {
    let mut arena = VcArena::default();
    let zero = add(&mut arena, VcTerm::U64(0));
    let one = add(&mut arena, VcTerm::U64(1));
    let bad = add(&mut arena, VcTerm::CheckedSub(zero, one));
    let eq = add(&mut arena, VcTerm::Equal(bad, bad));
    let not = add(&mut arena, VcTerm::Not(eq));
    let f = add(&mut arena, VcTerm::Bool(false));
    let t = add(&mut arena, VcTerm::Bool(true));
    for root in [eq, not] {
        assert_eq!(run(&arena, root), Some(AbstractBool::Unknown));
    }
    for (node, expected) in [
        (VcTerm::And(vec![f, eq]), AbstractBool::False),
        (VcTerm::Or(vec![t, eq]), AbstractBool::True),
        (VcTerm::And(vec![eq, f]), AbstractBool::Unknown),
        (VcTerm::Or(vec![eq, t]), AbstractBool::Unknown),
    ] {
        let root = add(&mut arena, node);
        assert_eq!(run(&arena, root), Some(expected));
    }
    let short = add(&mut arena, VcTerm::Or(vec![t, eq]));
    let mut budget = VcQueryBudget::new(VcLimits {
        max_query_steps: 3,
        ..Default::default()
    });
    assert_eq!(
        evaluate_bool(
            &arena,
            short,
            &BTreeSet::new(),
            SnapshotValues::Results(&[]),
            &function(),
            &mut budget
        ),
        Some(AbstractBool::True)
    );
}

#[test]
fn same_normalized_goal_reads_fresh_path_premises_and_never_mutates_resources() {
    let mut state = ResourceState::new();
    for id in 0..2 {
        state
            .define_value(
                VirValueId::new(id),
                AbstractValue::U64(U64Interval::new(0, 10).unwrap()),
            )
            .unwrap();
    }
    let mut guarded = state.clone();
    guarded.conjoin_path_fact(PathFact::comparison(
        crate::VirIntegerPredicate::LessThan,
        VirValueId::new(0),
        VirValueId::new(1),
    ));
    let mut arena = VcArena::default();
    let x = add(
        &mut arena,
        VcTerm::Snapshot(VirSpecSnapshot::Value {
            function: function().id,
            value: VirValueId::new(0),
        }),
    );
    let y = add(
        &mut arena,
        VcTerm::Snapshot(VirSpecSnapshot::Value {
            function: function().id,
            value: VirValueId::new(1),
        }),
    );
    let x8 = add(&mut arena, VcTerm::CheckedScale(x, 8));
    let y8 = add(&mut arena, VcTerm::CheckedScale(y, 8));
    let root = add(&mut arena, VcTerm::LessThan(x8, y8));
    let mut contradictory = guarded.clone();
    contradictory.conjoin_path_fact(PathFact::comparison(
        crate::VirIntegerPredicate::GreaterOrEqual,
        VirValueId::new(0),
        VirValueId::new(1),
    ));
    for (input, expected) in [
        (&guarded, AbstractBool::True),
        (&contradictory, AbstractBool::Unknown),
        (&state, AbstractBool::Unknown),
        (&guarded, AbstractBool::True),
    ] {
        let before = input.clone();
        let mut budget = VcQueryBudget::new(VcLimits::default());
        assert_eq!(
            evaluate_bool(
                &arena,
                root,
                &BTreeSet::new(),
                SnapshotValues::State(input),
                &function(),
                &mut budget
            ),
            Some(expected)
        );
        assert_eq!(input, &before);
        assert!(!budget.relations.finish().unwrap().is_empty());
    }
    let sub = add(&mut arena, VcTerm::CheckedSub(y, x));
    let max = add(&mut arena, VcTerm::U64(u64::MAX));
    let root = add(&mut arena, VcTerm::LessOrEqual(sub, max));
    assert_eq!(
        evaluate_bool(
            &arena,
            root,
            &BTreeSet::new(),
            SnapshotValues::State(&guarded),
            &function(),
            &mut VcQueryBudget::new(VcLimits::default())
        ),
        Some(AbstractBool::True)
    );
    let root = add(&mut arena, VcTerm::LessThan(x8, y8));
    let mut budget = VcQueryBudget::new(VcLimits::default());
    budget.relation_limits.max_variables = 0;
    assert_eq!(
        evaluate_bool(
            &arena,
            root,
            &BTreeSet::new(),
            SnapshotValues::State(&guarded),
            &function(),
            &mut budget
        ),
        Some(AbstractBool::Unknown)
    );
}

#[test]
fn checked_numeric_normalization_shares_dag_nodes_and_enforces_budgets() {
    use crate::verifier::vc::normalize::VcNormalizer;
    use crate::{
        VirLocation, VirSpecClause, VirSpecClauseId, VirSpecClauseKind, VirSpecClauseOrigin,
        VirSpecClauseOwner, VirSpecLocation, VirSpecProve, VirSpecProveId, VirSpecTerm,
        VirSpecTermId, VirSpecTermKind as T, VirSpecType,
    };
    let output = crate::analyze(&crate::SourceFile::from_text(
        "numeric-normalize.nera",
        "fn main() -> u64 { return 1; }",
    ));
    let mut unit = output.vir().unwrap().as_unit().clone();
    let function = unit.runtime.entry;
    let origin = unit
        .source_map
        .origin_at(VirLocation::FunctionEntry { function })
        .unwrap()
        .id;
    let clause = VirSpecClauseId::new(0);
    let id = VirSpecTermId::new;
    let range = T::RangeContains {
        outer_start: id(0),
        outer_end: id(1),
        inner_start: id(0),
        inner_end: id(1),
    };
    for (i, (ty, kind)) in [
        (VirSpecType::U64, T::U64(2)),
        (
            VirSpecType::U64,
            T::CheckedScale {
                operand: id(0),
                stride: 8,
            },
        ),
        (VirSpecType::Bool, range.clone()),
        (VirSpecType::Bool, range),
    ]
    .into_iter()
    .enumerate()
    {
        unit.specs.terms_mut().push(VirSpecTerm {
            id: id(i as u32),
            clause,
            ty,
            kind,
            origin,
        });
    }
    let location = VirSpecLocation::FunctionEntry { function };
    unit.specs.clauses_mut().push(VirSpecClause {
        id: clause,
        owner: VirSpecClauseOwner::Prove(VirSpecProveId::new(0)),
        location,
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic { root: id(2) },
    });
    unit.specs.proves_mut().push(VirSpecProve {
        id: VirSpecProveId::new(0),
        function,
        location,
        clause,
        origin,
    });
    let unit = unit.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let mut normalizer = VcNormalizer::new(VcLimits::default());
    let first = normalizer.normalize(&resolved, id(2)).unwrap();
    assert_eq!(normalizer.normalize(&resolved, id(3)).unwrap(), first);
    assert!(
        VcNormalizer::new(VcLimits {
            max_nodes: 2,
            ..Default::default()
        })
        .normalize(&resolved, id(2))
        .is_err()
    );
    assert!(
        VcNormalizer::new(VcLimits {
            max_normalization_steps: 1,
            ..Default::default()
        })
        .normalize(&resolved, id(2))
        .is_err()
    );
}
