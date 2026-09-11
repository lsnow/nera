use nera::verifier::summary::*;
#[path = "support/preview_checks.rs"]
mod preview_checks;
use nera::{CfgAnalysisConfig, FrontendStatus, SourceFile, VirRuntimeValue, verify_program};

fn inspect(
    source: &str,
    config: CfgAnalysisConfig,
    check: impl FnOnce(&nera::ResolvedVirUnit<'_>, &nera::ProgramVerification),
) {
    let output = nera::verification::verify_source(
        &SourceFile::from_text("summary-recursive.nera", source),
        config,
    );
    assert_eq!(
        output.frontend_status(),
        Some(FrontendStatus::AcceptedProposal),
        "{:?}",
        output.frontend_issues()
    );
    preview_checks::observe(&output);
    let unit = output.validated_unit().unwrap().resolve().unwrap();
    let report = output.verification().unwrap();
    for (&id, f) in report.functions() {
        f.summary().validate_structure(&unit, id, config).unwrap();
    }
    check(&unit, report);
}
fn checked(source: &str, expected: u64) {
    inspect(source, Default::default(), |unit, report| {
        assert!(
            report.is_memory_checked_core0(),
            "{:?}",
            report.diagnostics()
        );
        for f in report.functions().values() {
            assert!(
                f.summary().call_uses.iter().all(|c| matches!(
                    c.outcome,
                    CallSummaryOutcome::Applied | CallSummaryOutcome::Inductive
                )),
                "{:?}",
                report
                    .functions()
                    .values()
                    .map(|f| (
                        &f.summary().state,
                        &f.summary().recursion,
                        &f.summary().call_uses
                    ))
                    .collect::<Vec<_>>()
            );
            if let Some(scc) = &f.summary().recursion {
                assert_eq!(scc.outcome, SccOutcome::Closed, "{scc:?}");
                assert!(scc.final_recheck);
            }
        }
        assert_eq!(
            nera::interpret(unit.runtime()).unwrap().values(),
            [VirRuntimeValue::U64(expected)]
        );
    });
}

#[test]
fn scalar_base_case_and_mutual_components_publish_after_final_replay() {
    checked(
        include_str!("../spec/cases/verify/summary-recursive.nera"),
        42,
    );
    checked(
        "fn main()->u64 { let a=[10,42]; return a[index(0)]; }
        fn index(n:u64)->usize { if n==3 { return 1usize; } return index(n+1); }",
        42,
    );
    checked(
        "fn main()->u64 { return even(0); }
        fn even(n:u64)->u64 { if n==4 { return 42; } return odd(n+1); }
        fn odd(n:u64)->u64 { if n==3 { return 42; } return even(n+1); }",
        42,
    );
}

#[test]
fn borrowed_recursive_writes_and_identity_views_keep_real_loan_endpoints() {
    checked("fn main()->u64 { let mut value=1; fill(&mut value,0); let view=id(&value,0); return *view; }
        fn fill(p:&mut u64,n:u64) { if n==3 { *p=42; return; } fill(p,n+1); return; }
        fn id(p:&u64,n:u64)->&u64 { if n==3 { return p; } return id(p,n+1); }",42);
}

#[test]
fn recursive_owner_return_and_fresh_results_are_distinct_from_input_resources() {
    checked(
        "fn main()->u64 { let p=alloc<u64>(1); *p=42; let q=id(p,0); return *q; }
        fn id(p:Own<u64>,n:u64)->Own<u64> { if n==3 { return p; } return id(p,n+1); }",
        42,
    );
    checked("fn main()->u64 { let p=make(0); let q=make(1); return *p+*q; }
        fn make(n:u64)->Own<u64> { if n==3 { let p=alloc<u64>(1); *p=21; return p; } return make(n+1); }",42);
}

#[test]
fn conditional_owner_replacement_stays_in_complete_recursive_worlds() {
    for flag in ["true", "false"] {
        checked(&format!("fn main()->u64 {{ let p=alloc<u64>(1); *p=42; let q=choose(p,{flag},0); return *q; }}
            fn choose(p:Own<u64>,flag:bool,n:u64)->Own<u64> {{ if n==2 {{ if flag {{ return p; }} free(p); let q=alloc<u64>(1); *q=42; return q; }} return choose(p,flag,n+1); }}"),42);
    }
}

#[test]
fn widening_is_bounded_and_final_recheck_cannot_be_skipped_by_a_budget() {
    let source = "fn main()->u64 { return count(0); } fn count(n:u64)->u64 { if n==3 { return 0; } return count(n+1)+1; }";
    checked(source, 3);
    inspect(source, Default::default(), |_, report| {
        let scc = report
            .functions()
            .values()
            .find_map(|f| f.summary().recursion.as_ref())
            .unwrap();
        assert!(scc.widenings > 0, "{scc:?}");
        assert!(scc.iterations <= 8);
        assert!(scc.body_analyses <= 1024);
    });
    let source = "fn main()->u64 { let a=[42]; return a[index(0)]; } fn index(n:u64)->usize { if n==2 { return 0usize; } return index(n+1); }";
    for (limits, reason) in [
        (
            SccLimits {
                max_functions: 0,
                ..Default::default()
            },
            SccOutcome::FunctionBudget,
        ),
        (
            SccLimits {
                max_iterations: 0,
                ..Default::default()
            },
            SccOutcome::IterationBudget,
        ),
        (
            SccLimits {
                max_body_analyses: 1,
                ..Default::default()
            },
            SccOutcome::AnalysisBudget,
        ),
        (
            SccLimits {
                max_worlds: 0,
                ..Default::default()
            },
            SccOutcome::StateBudget,
        ),
        (
            SccLimits {
                max_candidate_bytes: 0,
                ..Default::default()
            },
            SccOutcome::StateBudget,
        ),
    ] {
        let config = CfgAnalysisConfig {
            summary_limits: limits,
            ..Default::default()
        };
        inspect(source, config, |unit, report| {
            assert!(!report.is_memory_checked_core0());
            let scc = report
                .functions()
                .values()
                .find_map(|f| f.summary().recursion.as_ref())
                .unwrap();
            assert_eq!(scc.outcome, reason, "{scc:?}");
            assert!(
                report.functions().values().all(|f| f
                    .summary()
                    .call_uses
                    .iter()
                    .all(|c| c.outcome != CallSummaryOutcome::Inductive)),
                "no provisional assumptions survive failure"
            );
            assert_eq!(*report, verify_program(unit, config).unwrap());
        });
    }
}

#[test]
fn faults_in_recursive_members_and_after_calls_cannot_hide_behind_hypotheses() {
    for source in [
        "fn main()->u64 { return bad(0); } fn bad(n:u64)->u64 { if n==2 { return 42; } let p=alloc<u64>(1); let v=*p; free(p); return bad(n+1); }",
        "fn main()->u64 { return a(0); } fn a(n:u64)->u64 { if n==2 { return 42; } return b(n+1); } fn b(n:u64)->u64 { let p=alloc<u64>(1); let v=*p; free(p); return a(n); }",
        "fn main()->u64 { let a=[42]; return a[index(0)]; } fn index(n:u64)->usize { if n==2 { return 1usize; } return index(n+1); }",
        "fn main()->u64 { return bad(0); } fn bad(n:u64)->u64 { if n==2 { return 42; } let v=bad(n+1); let a=[42]; let index=1usize; return a[index]; }",
    ] {
        inspect(source, Default::default(), |unit, report| {
            assert!(!report.is_memory_checked_core0(), "{source}");
            assert_eq!(*report, verify_program(unit, Default::default()).unwrap());
        });
    }
}

#[test]
fn absent_normal_returns_never_erase_later_memory_obligations() {
    inspect("fn main()->u64 { let p=alloc<u64>(1); let ignored=forever(); let v=*p; free(p); return v; }
        fn forever()->u64 { return forever(); }",Default::default(),|_,report| {
        assert!(!report.is_memory_checked_core0());
        for f in report.functions().values().filter(|f| f.summary().recursion.is_some()) {
            let Knowledge::Known(returns)=&f.summary().normal_returns else { panic!(); };
            assert!(!returns.is_empty());
        }
    }); // Deliberately do not execute the infinite recursion.
}

#[test]
fn closure_evidence_and_whole_component_bindings_reject_mutation() {
    inspect(
        "fn main()->u64 { return a(0); } fn a(n:u64)->u64 { if n==2 { return 42; } return b(n+1); }
        fn b(n:u64)->u64 { if n==3 { return 42; } return a(n+1); }",
        Default::default(),
        |unit, report| {
            for (&id, f) in report
                .functions()
                .iter()
                .filter(|(_, f)| f.summary().recursion.is_some())
            {
                assert_eq!(f.summary().state, SummaryState::Closed);
                for mutation in 0..4 {
                    let mut summary = f.summary().clone();
                    let record = summary.recursion.as_mut().unwrap();
                    match mutation {
                        0 => record.members.pop().map(|_| ()).unwrap(),
                        1 => record.final_recheck = false,
                        2 => record.outcome = SccOutcome::Unsupported,
                        _ => record.body_analyses = 0,
                    }
                    assert!(
                        summary
                            .validate_structure(unit, id, Default::default())
                            .is_err()
                    );
                }
                let changed = CfgAnalysisConfig {
                    summary_limits: SccLimits {
                        max_iterations: 0,
                        ..Default::default()
                    },
                    ..Default::default()
                };
                assert!(f.summary().validate_structure(unit, id, changed).is_err());
            }
        },
    );
}

#[test]
fn declaration_order_does_not_turn_acyclic_dependents_into_recursive_members() {
    let main = "fn main()->u64 { let a=[0,42]; return a[outer(0)]; }";
    let outer = "fn outer(n:u64)->usize { return even(n); }";
    let even = "fn even(n:u64)->usize { if n==4 { return 1usize; } return odd(n+1); }";
    let odd = "fn odd(n:u64)->usize { if n==3 { return 1usize; } return even(n+1); }";
    for source in [
        [main, outer, even, odd].join(" "),
        // The current source profile chooses the first function as entry.
        [main, odd, even, outer].join(" "),
    ] {
        checked(&source, 42);
        inspect(&source, Default::default(), |unit, report| {
            for function in unit.runtime().functions {
                let summary = report.functions()[&function.id].summary();
                assert_eq!(
                    summary.recursion.is_some(),
                    matches!(function.name.as_str(), "even" | "odd")
                );
                if let Some(scc) = &summary.recursion {
                    assert_eq!(scc.members.len(), 2);
                }
            }
        });
    }
}
