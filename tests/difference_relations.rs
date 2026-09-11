#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::verifier::relation::difference::{
    DifferenceDerivation, DifferenceGoal, DifferenceLimits, DifferencePremise, DifferenceStop,
    replay_difference, solve_difference,
};
use nera::verifier::relation::{
    RelationComparison as C, RelationGoal, RelationRule, RelationTerm as T,
    replay_relation_evidence,
};
use nera::{
    CfgAnalysisConfig, ObligationStatus as S, U64Interval, VirType, VirValueId, verify_program,
};

fn word(n: u32) -> T {
    T::Value {
        value: VirValueId::new(n),
        ty: VirType::U64,
    }
}
fn goal(c: C, left: T, right: T) -> DifferenceGoal {
    DifferenceGoal {
        comparison: c,
        left,
        right,
    }
}
fn cmp(c: C, left: T, right: T) -> DifferencePremise {
    DifferencePremise::Compare {
        comparison: c,
        left,
        right,
    }
}
fn domain(n: u32, lo: u64, hi: u64) -> DifferencePremise {
    DifferencePremise::Interval {
        value: VirValueId::new(n),
        interval: U64Interval::new(lo, hi).unwrap(),
    }
}

#[test]
fn finite_integer_enumeration_oracle_checks_both_verdicts_and_contradictions() {
    let comparisons = [C::LessThan, C::LessOrEqual, C::Equal, C::NotEqual];
    // Deterministic mixed DBM + disequality corpus; all variables range 0..=3.
    for seed in 0..512usize {
        let a = (seed % 3) as u32;
        let b = ((seed / 3) % 3) as u32;
        let c = ((seed / 9) % 3) as u32;
        let bound = ((seed / 27) % 5) as i128 - 2;
        let relation = comparisons[(seed / 135) % 4];
        let premises = vec![
            domain(0, 0, 3),
            domain(1, 0, 3),
            domain(2, 0, 3),
            DifferencePremise::Bound {
                left: word(a),
                right: word(b),
                bound,
            },
            cmp(relation, word(b), word(c)),
        ];
        let holds = |c, x: u64, y: u64| match c {
            C::LessThan => x < y,
            C::LessOrEqual => x <= y,
            C::Equal => x == y,
            C::NotEqual => x != y,
        };
        let models = (0..64)
            .map(|i| [i % 4, (i / 4) % 4, i / 16])
            .filter(|m| {
                i128::from(m[a as usize]) - i128::from(m[b as usize]) <= bound
                    && holds(relation, m[b as usize], m[c as usize])
            })
            .collect::<Vec<_>>();
        for comparison in comparisons {
            let query = goal(comparison, word(0), word(2));
            let actual = solve_difference(&premises, query, DifferenceLimits::default());
            let expected = if models.is_empty() {
                S::Unknown
            } else if models.iter().all(|m| holds(comparison, m[0], m[2])) {
                S::Proven
            } else if models.iter().all(|m| !holds(comparison, m[0], m[2])) {
                S::Refuted
            } else {
                S::Unknown
            };
            assert_eq!(
                actual.status, expected,
                "seed={seed} query={query:?} stop={:?}",
                actual.stop
            );
            if models.is_empty() {
                assert_eq!(actual.stop, DifferenceStop::Inconsistent);
                assert!(actual.branches.iter().all(|b| b.contradiction.is_some()));
            } else {
                assert_eq!(actual.stop, DifferenceStop::Complete);
            }
            // Independently check every exported closure bound against the
            // ORIGINAL concrete premises, not against the exported bounds.
            for model in &models {
                let branch = actual
                    .branches
                    .iter()
                    .find(|branch| {
                        branch.choices.is_empty()
                            || branch.choices[0] == (model[b as usize] < model[c as usize])
                    })
                    .unwrap();
                assert!(branch.contradiction.is_none());
                for edge in &branch.bounds {
                    let value = |id: Option<VirValueId>| {
                        id.map_or(0, |id| i128::from(model[id.get() as usize]))
                    };
                    assert!(value(edge.left) - value(edge.right) <= edge.bound);
                }
            }
        }
    }
}

#[test]
fn transitivity_equalities_negative_offsets_and_total_order_splits() {
    let premises = [
        cmp(C::LessOrEqual, word(0), word(1)),
        cmp(C::LessThan, word(1), word(2)),
    ];
    assert_eq!(
        solve_difference(
            &premises,
            goal(C::LessThan, word(0), word(2)),
            DifferenceLimits::default()
        )
        .status,
        S::Proven
    );
    let subtract = [DifferencePremise::EqualOffset {
        left: word(0),
        right: word(1),
        offset: -1,
    }];
    assert_eq!(
        solve_difference(
            &subtract,
            goal(C::LessThan, word(0), word(1)),
            DifferenceLimits::default()
        )
        .status,
        S::Proven
    );
    let premises = [cmp(C::NotEqual, word(0), word(1))];
    let result = solve_difference(
        &premises,
        goal(C::NotEqual, word(0), word(1)),
        DifferenceLimits::default(),
    );
    assert_eq!(result.status, S::Proven);
    assert_eq!(result.branches.len(), 2);
    assert!(result.branches.iter().all(|b| b.contradiction.is_none()));
    assert_eq!(
        solve_difference(
            &premises,
            goal(C::LessThan, word(0), word(1)),
            DifferenceLimits::default()
        )
        .status,
        S::Unknown
    );
    let premises = [
        cmp(C::NotEqual, word(0), word(1)),
        cmp(C::LessOrEqual, word(0), word(1)),
    ];
    let result = solve_difference(
        &premises,
        goal(C::LessThan, word(0), word(1)),
        DifferenceLimits::default(),
    );
    assert_eq!(result.status, S::Proven);
    assert_eq!(
        result
            .branches
            .iter()
            .filter(|b| b.contradiction.is_some())
            .count(),
        1
    );
}

#[test]
fn unsigned_extremes_checked_normalization_and_types_fail_closed() {
    for (left, right, status) in [
        (0, u64::MAX, S::Proven),
        (u64::MAX, 0, S::Refuted),
        (u64::MAX, u64::MAX, S::Refuted),
    ] {
        assert_eq!(
            solve_difference(
                &[],
                goal(C::LessThan, T::Constant(left), T::Constant(right)),
                DifferenceLimits::default()
            )
            .status,
            status
        );
    }
    for p in [
        DifferencePremise::Bound {
            left: T::Constant(1),
            right: word(0),
            bound: i128::MIN,
        },
        DifferencePremise::EqualOffset {
            left: word(0),
            right: word(1),
            offset: i128::MIN,
        },
    ] {
        let result = solve_difference(
            &[p],
            goal(C::Equal, word(0), word(1)),
            DifferenceLimits::default(),
        );
        assert_eq!(result.status, S::Unknown);
        assert_eq!(result.stop, DifferenceStop::ArithmeticOverflow);
    }
    // Two legal i128 edges whose closure sum itself overflows.
    let result = solve_difference(
        &[
            DifferencePremise::Bound {
                left: word(0),
                right: word(1),
                bound: i128::MIN + 1,
            },
            DifferencePremise::Bound {
                left: word(1),
                right: word(2),
                bound: -100,
            },
        ],
        goal(C::LessThan, word(0), word(2)),
        DifferenceLimits::default(),
    );
    assert_eq!(result.status, S::Unknown);
    assert!(matches!(
        result.stop,
        DifferenceStop::ArithmeticOverflow | DifferenceStop::Inconsistent
    ));
    let wrong = T::Value {
        value: VirValueId::new(0),
        ty: VirType::Bool,
    };
    assert_eq!(
        solve_difference(
            &[],
            goal(C::Equal, wrong, word(0)),
            DifferenceLimits::default()
        )
        .stop,
        DifferenceStop::InvalidInput
    );
}

#[test]
fn every_budget_degrades_to_unknown_and_traces_are_replayable_not_authority() {
    let premises = [
        cmp(C::NotEqual, word(0), word(1)),
        cmp(C::LessOrEqual, word(0), word(1)),
    ];
    let query = goal(C::LessThan, word(0), word(1));
    let limits = DifferenceLimits::default();
    let original = solve_difference(&premises, query, limits);
    assert!(replay_difference(&premises, query, limits, &original));
    for limited in [
        DifferenceLimits {
            max_variables: 1,
            ..limits
        },
        DifferenceLimits {
            max_constraints: 1,
            ..limits
        },
        DifferenceLimits {
            max_steps: 0,
            ..limits
        },
        // Completing a prefix of the branches must not turn a query into a
        // success when the shared budget is exhausted in the final branch.
        DifferenceLimits {
            max_steps: original.steps - 1,
            ..limits
        },
        DifferenceLimits {
            max_derivations: 0,
            ..limits
        },
        DifferenceLimits {
            max_branches: 1,
            ..limits
        },
    ] {
        let result = solve_difference(&premises, query, limited);
        assert_eq!(
            (result.status, result.stop),
            (S::Unknown, DifferenceStop::Budget)
        );
    }
    let mut mutations = Vec::new();
    let mut m = original.clone();
    m.premises.clear();
    mutations.push(m);
    let mut m = original.clone();
    m.branches[0].choices[0] = !m.branches[0].choices[0];
    mutations.push(m);
    let mut m = original.clone();
    m.branches[0].contradiction = None;
    m.branches[0].derivation.clear();
    mutations.push(m);
    let mut m = original.clone();
    m.branches[0]
        .derivation
        .push(DifferenceDerivation::Compose {
            first: usize::MAX,
            second: 0,
            bound: -1,
        });
    mutations.push(m);
    let mut m = original.clone();
    m.status = S::Refuted;
    mutations.push(m);
    for mutation in mutations {
        assert!(!replay_difference(&premises, query, limits, &mutation));
    }
}

const LOCAL: &str = include_str!("../spec/cases/verify/difference-local.nera");

#[test]
fn true_guard_relations_are_consumed_but_an_unchecked_comparison_is_not_a_fact() {
    for condition in ["i <= j", "i == j", "i < j"] {
        let source = format!(
            "fn main() -> u64 {{ return read(1usize, 2usize); }}
          fn read(i: usize, j: usize) -> u64 {{ let a = [42, 42, 42, 42];
          if i < 4usize {{ if j < 4usize {{ if {condition} {{
            let s = &a[i..j]; return a[i]; }} }} }} return 42; }}"
        );
        frontend_checks::checked("guard.nera", &source, 42);
        let output = frontend_checks::accepted("guard.nera", &source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(
            result
                .functions()
                .values()
                .flat_map(|f| f.cfg().relation_evidence())
                .any(|r| {
                    matches!(r.goal, RelationGoal::Ordered { .. })
                        && r.rule == RelationRule::BoundedDifference
                        && r.status == S::Proven
                })
        );
    }
    let source = "fn main() -> u64 { return read(2usize, 1usize); }
      fn read(i: usize, j: usize) -> u64 { let a = [42, 42, 42, 42];
        if i < 4usize { if j < 4usize { let condition = i <= j;
          let s = &a[i..j]; return a[i]; } } return 42; }";
    let output = frontend_checks::accepted("unchecked-condition.nera", source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!result.is_memory_checked_core0());
    assert!(
        result
            .functions()
            .values()
            .flat_map(|f| f.cfg().relation_evidence())
            .any(|r| { matches!(r.goal, RelationGoal::Ordered { .. }) && r.status == S::Unknown })
    );
}

#[test]
fn numeric_success_does_not_initialize_storage() {
    let source = "fn main() -> u64 { return read(1usize); }
      fn read(i: usize) -> u64 { let mut a: [u64; 4]; a[0] = 42;
        if i < 3usize { let end = i + 1usize; let s = &a[i..end]; return 42; }
        return 0; }";
    let output = frontend_checks::accepted("uninitialized.nera", source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!result.is_memory_checked_core0());
    assert!(
        result
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|r| {
                matches!(
                    r.obligation().kind(),
                    nera::ResourceObligationKind::ObjectValueBytesInitialized { .. }
                        | nera::ResourceObligationKind::MemoryInitialized { .. }
                ) && r.obligation().status() != S::Proven
            })
    );
    assert!(
        result
            .functions()
            .values()
            .flat_map(|f| f.cfg().relation_evidence())
            .any(|r| {
                matches!(r.goal, RelationGoal::Ordered { .. })
                    && r.status == S::Proven
                    && r.rule == RelationRule::BoundedDifference
            })
    );
}

#[test]
fn production_range_order_consumes_checked_affine_difference_and_replays() {
    frontend_checks::checked("difference-local.nera", LOCAL, 42);
    let output = frontend_checks::accepted("difference-local.nera", LOCAL);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let verified = verify_program(&resolved, config).unwrap();
    let record = verified
        .functions()
        .values()
        .flat_map(|f| f.cfg().relation_evidence())
        .find(|r| {
            matches!(r.goal, RelationGoal::Ordered { .. })
                && r.rule == RelationRule::BoundedDifference
                && r.status == S::Proven
        })
        .expect("actual range-order consumer");
    assert!(
        record
            .difference
            .as_ref()
            .unwrap()
            .premises
            .iter()
            .any(|p| matches!(p, DifferencePremise::EqualOffset { offset: 1, .. }))
    );
    assert!(replay_relation_evidence(&resolved, config, record).unwrap());
    let mut forged = record.clone();
    forged.difference.as_mut().unwrap().branches[0]
        .derivation
        .clear();
    assert!(!replay_relation_evidence(&resolved, config, &forged).unwrap());
    let mut forged = record.clone();
    forged.difference.as_mut().unwrap().premises.clear();
    assert!(!replay_relation_evidence(&resolved, config, &forged).unwrap());
    let limited = CfgAnalysisConfig {
        relation_limits: DifferenceLimits {
            max_variables: 0,
            ..config.relation_limits
        },
        ..config
    };
    let rejected = verify_program(&resolved, limited).unwrap();
    assert!(!rejected.is_memory_checked_core0());
    assert!(
        rejected
            .functions()
            .values()
            .flat_map(|f| f.cfg().relation_evidence())
            .any(|r| matches!(r.goal, RelationGoal::Ordered { .. }) && r.status == S::Unknown)
    );
    assert!(!replay_relation_evidence(&resolved, limited, record).unwrap());
}

#[test]
fn wrapping_addition_does_not_acquire_a_mathematical_offset_premise() {
    let source = "fn main() -> u64 { return read(18446744073709551615usize); }
      fn read(i: usize) -> u64 { let a = [42, 42, 42, 42];
        let end = i + 1usize; let s = &a[i..end]; return 42; }";
    let output = frontend_checks::accepted("wrapping.nera", source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let verified = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!verified.is_memory_checked_core0());
    let records = verified
        .functions()
        .values()
        .flat_map(|f| f.cfg().relation_evidence())
        .filter(|r| matches!(r.goal, RelationGoal::Ordered { .. }))
        .collect::<Vec<_>>();
    assert!(!records.is_empty());
    for r in records {
        assert_ne!(r.status, S::Proven);
        if let Some(e) = &r.difference {
            assert!(
                !e.premises
                    .iter()
                    .any(|p| matches!(p, DifferencePremise::EqualOffset { offset: 1, .. }))
            );
        }
    }
}
