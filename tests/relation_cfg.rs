#[path = "support/frontend_checks.rs"]
mod frontend_checks;
use nera::verifier::relation::difference::DifferenceLimits;
use nera::verifier::relation::{RelationGoal, RelationRule, replay_relation_evidence};
use nera::{CfgAnalysisConfig, ObligationStatus as S, ResourceObligationKind as K, verify_program};

const SOURCE: &str = include_str!("../spec/cases/verify/relation-cfg.nera");

#[test]
fn comparison_chain_survives_early_exit_edges_and_guard_forgetting() {
    let source = "fn main() -> u64 { return read(1usize,2usize,4usize); }
      fn read(i: usize,j: usize,k: usize) -> u64 { let a = [42,42,42,42,42];
      if i >= j { return 0; } if j >= k { return 0; } if k >= 5usize { return 0; }
      let view = &a[i..k]; return a[i]; }";
    frontend_checks::checked("early-exit.nera", source, 42);
    let output = frontend_checks::accepted("early-exit.nera", source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert!(
        verify_program(&resolved, collapsed())
            .unwrap()
            .is_memory_checked_core0()
    );
    let mutated = source.replace("if j >= k { return 0; }", "if j >= k { }");
    let output = frontend_checks::accepted("missing-edge.nera", &mutated);
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert!(
        !verify_program(&resolved, collapsed())
            .unwrap()
            .is_memory_checked_core0()
    );
}

fn collapsed() -> CfgAnalysisConfig {
    CfgAnalysisConfig {
        max_guarded_cases_per_block: 1,
        max_guard_atoms_per_case: 0,
        max_refinement_passes: 0,
        ..CfgAnalysisConfig::default()
    }
}

#[test]
fn differing_affine_offsets_join_to_a_common_relation_without_guard_cases() {
    frontend_checks::checked("relation-cfg.nera", SOURCE, 42);
    let output = frontend_checks::accepted("relation-cfg.nera", SOURCE);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let config = collapsed();
    let result = verify_program(&resolved, config).unwrap();
    assert!(
        result.is_memory_checked_core0(),
        "{:#?}",
        result.diagnostics()
    );
    assert_eq!(result, verify_program(&resolved, config).unwrap());
    let record = result
        .functions()
        .values()
        .flat_map(|f| f.cfg().relation_evidence())
        .find(|r| {
            matches!(r.goal, RelationGoal::Ordered { .. })
                && r.rule == RelationRule::BoundedDifference
        })
        .unwrap();
    assert_eq!(record.status, S::Proven);
    assert!(replay_relation_evidence(&resolved, config, record).unwrap());
    let mut forged = record.clone();
    forged.difference.as_mut().unwrap().branches[0]
        .bounds
        .clear();
    assert!(!replay_relation_evidence(&resolved, config, &forged).unwrap());
    for limits in [
        DifferenceLimits {
            max_variables: 0,
            ..config.relation_limits
        },
        DifferenceLimits {
            max_constraints: 0,
            ..config.relation_limits
        },
        DifferenceLimits {
            max_steps: 0,
            ..config.relation_limits
        },
        DifferenceLimits {
            max_derivations: 0,
            ..config.relation_limits
        },
    ] {
        let limited = verify_program(
            &resolved,
            CfgAnalysisConfig {
                relation_limits: limits,
                ..config
            },
        )
        .unwrap();
        assert!(!limited.is_memory_checked_core0());
    }
}

#[test]
fn one_bad_predecessor_cannot_borrow_another_predecessors_relation() {
    let source = SOURCE.replace("end = i + 2usize", "end = 0usize");
    let output = frontend_checks::accepted("bad-join.nera", &source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    for config in [collapsed(), CfgAnalysisConfig::default()] {
        let result = verify_program(&resolved, config).unwrap();
        assert!(!result.is_memory_checked_core0());
        assert!(
            result
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .any(
                    |r| matches!(r.obligation().kind(), K::SliceRangeOrdered { .. })
                        && r.obligation().status() != S::Proven
                )
        );
    }
}

#[test]
fn loop_induction_requires_entry_and_backedge_and_does_not_assume_wrapping() {
    let source = "fn main() -> u64 { return read(0usize); }
      fn read(i: usize) -> u64 { let a = [42,42,42,42]; if i < 2usize {
        let mut start = i; let mut end = i + 1usize;
        while end < 3usize { start = start + 1usize; end = end + 1usize; }
        let view = &a[start..end]; return 42; } return 0; }";
    frontend_checks::checked("relation-loop.nera", source, 42);
    let output = frontend_checks::accepted("relation-loop.nera", source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let result = verify_program(&resolved, collapsed()).unwrap();
    assert!(
        result.is_memory_checked_core0(),
        "{:#?}",
        result.diagnostics()
    );
    assert!(
        result
            .functions()
            .values()
            .any(|f| !f.cfg().loop_blocks().is_empty())
    );
    for source in [
        source.replace("end = i + 1usize", "end = 0usize"),
        source.replace(
            "start = start + 1usize",
            "start = start + 18446744073709551615usize",
        ),
    ] {
        let output = frontend_checks::accepted("bad-loop.nera", &source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        assert!(
            !verify_program(&resolved, collapsed())
                .unwrap()
                .is_memory_checked_core0()
        );
    }
    assert!(
        verify_program(
            &resolved,
            CfgAnalysisConfig {
                max_block_visits: 1,
                ..collapsed()
            }
        )
        .is_err()
    );
}

#[test]
fn old_loaded_values_do_not_describe_new_loads_after_alias_write_or_call() {
    for change in ["*p = 0usize;", "change(p);"] {
        let source = format!(
            "fn main() -> u64 {{ let mut v = 2usize; return read(&mut v,1usize); }}
          fn change(p: &mut usize) {{ *p = 0usize; return; }}
          fn read(p: &mut usize, i: usize) -> u64 {{ let a = [42,42,42,42]; let before = *p;
          if i < 4usize {{ if before < 4usize {{ if i < before {{ {change}
          let after = *p; let s = &a[i..after]; return 42; }} }} }} return 0; }}"
        );
        let output = frontend_checks::accepted("reload.nera", &source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(!result.is_memory_checked_core0());
        assert!(
            result
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .any(
                    |r| matches!(r.obligation().kind(), K::SliceRangeOrdered { .. })
                        && r.obligation().status() != S::Proven
                )
        );
    }
}
