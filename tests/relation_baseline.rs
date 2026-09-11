#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::verifier::relation::{
    RelationEvidence, RelationGoal, RelationPremise, RelationTerm, replay_relation_evidence,
};
use nera::{CfgAnalysisConfig, interpret, verify_program};

const MATRIX: &str = include_str!("../spec/cases/verify/relation-baseline.nera");

fn accepted(source: &str) -> nera::FrontendOutput {
    frontend_checks::accepted("relation-baseline.nera", source)
}

fn evidence(verification: &nera::ProgramVerification) -> Vec<&RelationEvidence> {
    verification
        .functions()
        .values()
        .flat_map(|f| f.cfg().relation_evidence())
        .collect()
}

#[test]
fn existing_checked_paths_emit_all_baseline_goal_families_and_replay() {
    frontend_checks::checked("relation-baseline.nera", MATRIX, 42);
    let output = accepted(MATRIX);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let first = verify_program(&resolved, config).unwrap();
    assert_eq!(first, verify_program(&resolved, config).unwrap());
    let observations = evidence(&first);
    for family in 0..6 {
        let record = observations
            .iter()
            .find(|r| {
                matches!(
                    (&r.goal, family),
                    (RelationGoal::Compare { .. }, 0)
                        | (RelationGoal::NoOverflow { .. }, 1)
                        | (RelationGoal::Ordered { .. }, 2)
                        | (RelationGoal::Contained { .. }, 3)
                        | (RelationGoal::Disjoint { .. }, 4)
                        | (RelationGoal::Aligned { .. }, 5)
                )
            })
            .expect("every baseline family observed");
        assert!(replay_relation_evidence(&resolved, config, record).unwrap());
    }
    assert!(
        observations
            .iter()
            .all(|r| r.status == nera::ObligationStatus::Proven)
    );
}

#[test]
fn goal_type_origin_premise_rule_and_configuration_mutations_do_not_replay() {
    let output = accepted(MATRIX);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let verification = verify_program(&resolved, config).unwrap();
    let observations = evidence(&verification);
    let original = (*observations
        .iter()
        .find(|r| matches!(r.goal, RelationGoal::Compare { .. }))
        .unwrap())
    .clone();
    let mut mutations = Vec::new();
    let mut goal = original.clone();
    goal.goal = RelationGoal::Ordered {
        start: RelationTerm::Constant(100),
        end: RelationTerm::Constant(0),
    };
    mutations.push(goal);
    let mut wrong_type = original.clone();
    if let RelationGoal::Compare {
        left: RelationTerm::Value { ty, .. },
        ..
    } = &mut wrong_type.goal
    {
        *ty = nera::VirType::Bool;
    } else {
        panic!("typed index query");
    }
    mutations.push(wrong_type);
    let mut origin = original.clone();
    origin.finding = observations
        .iter()
        .find(|r| r.finding != original.finding)
        .unwrap()
        .finding;
    mutations.push(origin);
    let mut premise = original.clone();
    premise.premises.clear();
    mutations.push(premise);
    let mut result = original.clone();
    result.status = nera::ObligationStatus::Refuted;
    mutations.push(result);
    let mut rule = original.clone();
    rule.kernel_version += 1;
    mutations.push(rule);
    let mut wrong_rule = original.clone();
    wrong_rule.rule = nera::verifier::relation::RelationRule::GuaranteedOrExactAlignment;
    mutations.push(wrong_rule);
    let mut case = original.clone();
    case.case_ordinal += 1_000;
    mutations.push(case);
    for mutation in mutations {
        assert!(!replay_relation_evidence(&resolved, config, &mutation).unwrap());
    }
    let config = CfgAnalysisConfig {
        max_refinement_passes: 0,
        ..config
    };
    assert!(!replay_relation_evidence(&resolved, config, &original).unwrap());
    assert_eq!(
        verification,
        verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
    );
}

#[test]
fn observations_retain_guards_and_do_not_merge_path_specific_intervals() {
    let source = "fn main() -> u64 { return read(true); } fn read(flag: bool) -> u64 {
      let values = [42, 42, 42, 42]; let mut i = 0usize; if flag { i = 1usize; }
      return values[i]; }";
    let output = accepted(source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let verified = verify_program(&resolved, config).unwrap();
    assert!(verified.is_memory_checked_core0());
    let observations = evidence(&verified);
    let pair = observations
        .iter()
        .find_map(|a| {
            observations
                .iter()
                .find(|b| {
                    a.finding == b.finding
                        && a.obligation_ordinal == b.obligation_ordinal
                        && a.case_ordinal != b.case_ordinal
                        && a.premises != b.premises
                })
                .map(|b| (*a, *b))
        })
        .expect("distinct cases at one use");
    let mut mixed = pair.0.clone();
    mixed.premises = pair.1.premises.clone();
    assert!(!replay_relation_evidence(&resolved, config, &mixed).unwrap());
    assert!(
        pair.0
            .premises
            .iter()
            .any(|p| matches!(p, RelationPremise::Interval { .. }))
    );
}

#[test]
fn relation_capability_matrix_keeps_checked_and_gated_cases_distinct() {
    let cases = [
        ("chain", "fn main() -> u64 { return read(0usize, 1usize); }
          fn read(i: usize, j: usize) -> u64 { let values = [42, 42, 42, 42];
          if i < j { if j < 4usize { return values[i]; } } return 42; }"),
        ("dual-index", "fn main() -> u64 { return edit(0usize, 1usize); }
          fn edit(i: usize, j: usize) -> u64 { let mut values = [1, 2, 3, 4];
          if i >= 4usize { return 42; } if j >= 4usize { return 42; } if i == j { return 42; }
          let a = &mut values[i]; let b = &mut values[j]; *a = 20; *b = 22; return *a + *b; }"),
        ("split", "fn main() -> u64 { return edit(2usize); }
          fn edit(mid: usize) -> u64 { let mut values = [1, 2, 3, 4]; if mid > 4usize { return 42; }
          let a = &mut values[..mid]; let b = &mut values[mid..]; return a[0] + b[0]; }"),
        ("siblings", "fn main() -> u64 { let mut values = [1, 2, 3, 4]; let parent = &mut values[..];
          let a = &mut parent[..2]; let b = &mut parent[2..]; a[0] = 20; b[0] = 22; return a[0] + b[0]; }"),
        ("stride", "fn main() -> u64 { return edit(0usize, 1usize); }
          fn edit(i: usize, j: usize) -> u64 { let mut values = [[1, 2], [3, 4]];
          if i >= 2usize { return 42; } if j >= 2usize { return 42; } if i == j { return 42; }
          let a = &mut values[i][0]; let b = &mut values[j][0]; *a = 20; *b = 22; return *a + *b; }"),
    ];
    for (name, source) in cases {
        let output = accepted(source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        let checked = matches!(name, "chain" | "dual-index" | "siblings" | "stride");
        assert_eq!(
            verification.is_memory_checked_core0(),
            checked,
            "{name} baseline changed"
        );
        assert_eq!(
            verification,
            verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
        );
        if !checked {
            assert!(!verification.diagnostics().is_empty());
        }
        // Execute only after checking the entire program; a safe concrete
        // branch alone cannot upgrade a gated program.
        if checked {
            assert_eq!(
                interpret(resolved.runtime()).unwrap().values(),
                [nera::VirRuntimeValue::U64(42)]
            );
        }
    }
}

#[test]
fn unknown_and_refuted_numeric_observations_remain_distinct() {
    for (source, expected) in [
        (
            "fn main() -> u64 { let a = [42, 42]; let i = 2usize; return a[i]; }",
            nera::ObligationStatus::Refuted,
        ),
        (
            "fn main() -> u64 { return read(0usize); } fn read(i: usize) -> u64 { let a = [42, 42]; return a[i]; }",
            nera::ObligationStatus::Unknown,
        ),
    ] {
        let output = accepted(source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let verified = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(!verified.is_memory_checked_core0());
        let observations = evidence(&verified);
        let record = observations
            .iter()
            .find(|r| matches!(r.goal, RelationGoal::Compare { .. }) && r.status == expected)
            .unwrap();
        assert!(replay_relation_evidence(&resolved, CfgAnalysisConfig::default(), record).unwrap());
        let mut forged = (*record).clone();
        forged.status = nera::ObligationStatus::Proven;
        assert!(
            !replay_relation_evidence(&resolved, CfgAnalysisConfig::default(), &forged).unwrap()
        );
    }
}
