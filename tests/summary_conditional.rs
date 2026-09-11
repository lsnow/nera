use nera::verifier::summary::{CallSummaryOutcome, Knowledge, SummaryState};
use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, VirRuntimeValue, analyze, verify_program,
};

#[path = "support/summary_enum_program.rs"]
mod summary_enum_program;

#[test]
fn typed_enum_tag_and_fresh_owner_payload_stay_in_one_world_across_calls() {
    for flag in [false, true] {
        let validated = summary_enum_program::unit(flag, false, false)
            .into_validated()
            .unwrap();
        let unit = validated.resolve().unwrap();
        let report = verify_program(&unit, Default::default()).unwrap();
        assert!(
            report.is_memory_checked_core0(),
            "{:?}; {:?}",
            report
                .diagnostics()
                .iter()
                .map(|d| d.message())
                .collect::<Vec<_>>(),
            report
                .functions()
                .iter()
                .map(|(id, f)| (id, &f.summary().state, &f.summary().call_uses))
                .collect::<Vec<_>>()
        );
        let f = unit
            .runtime()
            .functions
            .iter()
            .find(|f| f.name == "make")
            .unwrap();
        assert_eq!(
            report.functions()[&f.id].summary().state,
            SummaryState::Closed
        );
        assert_eq!(
            nera::interpret(unit.runtime()).unwrap().values(),
            [VirRuntimeValue::U64(42)]
        );
    }
    for (wrong_tag, missing_payload) in [(true, false), (false, true)] {
        let validated = summary_enum_program::unit(true, wrong_tag, missing_payload)
            .into_validated()
            .unwrap();
        let unit = validated.resolve().unwrap();
        let report = verify_program(&unit, Default::default()).unwrap();
        assert!(!report.is_memory_checked_core0());
        assert!(nera::interpret(unit.runtime()).is_err());
    }
}

fn inspect(
    source: &str,
    check: impl FnOnce(&nera::ResolvedVirUnit<'_>, &nera::ProgramVerification),
) {
    let out = analyze(&SourceFile::from_text("conditional-summary.nera", source));
    assert_eq!(
        out.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        out.issues()
    );
    let unit = out.vir().unwrap().resolve().unwrap();
    let report = verify_program(&unit, Default::default()).unwrap();
    check(&unit, &report);
}

const OWNER: &str = "fn main()->u64 { return run(true); }
fn run(flag:bool)->u64 { let p=alloc<u64>(1); *p=42; let old=&raw *p;
    let returned=outer(p,flag); if flag { if old!=&raw *returned { return 0; } } return *returned; }
fn outer(p:Own<u64>,flag:bool)->Own<u64> { return choose(p,flag); }
fn choose(p:Own<u64>,flag:bool)->Own<u64> { if flag { return p; }
    free(p); let q=alloc<u64>(1); *q=42; return q; }";

#[test]
fn conditional_owner_identity_or_fresh_keeps_the_old_alias_lifetime_in_each_world() {
    for flag in ["true", "false"] {
        inspect(
            &OWNER.replace("run(true)", &format!("run({flag})")),
            |unit, report| {
                assert!(
                    report.is_memory_checked_core0(),
                    "{:?}",
                    report.diagnostics()
                );
                for name in ["choose", "outer"] {
                    let f = unit
                        .runtime()
                        .functions
                        .iter()
                        .find(|f| f.name == name)
                        .unwrap();
                    let summary = report.functions()[&f.id].summary();
                    assert_eq!(summary.state, SummaryState::Closed, "{summary:#?}");
                    assert!(
                        matches!(&summary.normal_returns, Knowledge::Known(a) if a.iter().map(|a| a.worlds.len()).sum::<usize>() == 2)
                    );
                }
                let run = unit
                    .runtime()
                    .functions
                    .iter()
                    .find(|f| f.name == "run")
                    .unwrap();
                assert!(
                    report.functions()[&run.id]
                        .summary()
                        .call_uses
                        .iter()
                        .all(|c| c.outcome == CallSummaryOutcome::Applied)
                );
                assert_eq!(
                    nera::interpret(unit.runtime()).unwrap().values(),
                    [VirRuntimeValue::U64(42)]
                );
            },
        );
    }
}

#[test]
fn conditional_constant_results_and_input_guards_cross_wrappers() {
    inspect(
        "fn main()->u64 { return run(false); }
        fn run(flag:bool)->u64 { let a=[42,42]; return a[outer(flag)]; }
        fn outer(flag:bool)->usize { return index(flag); }
        fn index(flag:bool)->usize { if flag { return 0usize; } return 1usize; }",
        |unit, report| {
            assert!(
                report.is_memory_checked_core0(),
                "{:?}",
                report.diagnostics()
            );
            assert_eq!(
                nera::interpret(unit.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(42)]
            );
        },
    );
}

#[test]
fn boolean_result_of_a_numeric_guard_refines_the_callers_input_snapshot() {
    for source in [
        "fn main()->u64 { return run(0usize); }
        fn run(i:usize)->u64 { let a=[42]; if outer(i) { return a[i]; } return 42; }
        fn outer(i:usize)->bool { return valid(i); }
        fn valid(i:usize)->bool { return i<1usize; }",
        "fn main()->u64 { return run(0usize); }
        fn run(i:usize)->u64 { let a=[42]; let tag=outer(i); if tag { return a[i]; } return 42; }
        fn outer(i:usize)->bool { if i<1usize { return true; } return false; }",
    ] {
        inspect(source, |unit, report| {
            assert!(
                report.is_memory_checked_core0(),
                "{:?}",
                report.diagnostics()
            );
            assert_eq!(
                nera::interpret(unit.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(42)]
            );
        });
    }
}

#[test]
fn aggregate_partial_move_refill_and_input_or_fresh_payload_preserve_identity() {
    for flag in ["true", "false"] {
        let source = include_str!("../spec/cases/verify/summary-conditional-payload.nera")
            .replace("run(true)", &format!("run({flag})"));
        inspect(&source, |unit, report| {
            assert!(
                report.is_memory_checked_core0(),
                "{:?}",
                report.diagnostics()
            );
            let run = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == "run")
                .unwrap();
            assert!(
                report.functions()[&run.id]
                    .summary()
                    .call_uses
                    .iter()
                    .all(|c| c.outcome == CallSummaryOutcome::Applied),
                "{:?}",
                report.functions()[&run.id].summary().call_uses
            );
            assert_eq!(
                nera::interpret(unit.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(42)]
            );
        });
    }
}

#[test]
fn overlapping_existential_guards_keep_all_results_and_discarding_results_loses_the_relation() {
    for suffix in [
        "let answer=choose(&flag); if answer { return a[i]; } return 42;",
        "let answer=valid(i); return a[i];",
    ] {
        inspect(
            &format!(
                "fn main()->u64 {{ return run(0usize); }}
            fn run(i:usize)->u64 {{ let flag=true; let a=[42]; {suffix} }}
            fn choose(p:&bool)->bool {{ if *p {{ return true; }} return false; }}
            fn valid(i:usize)->bool {{ return i<1usize; }}"
            ),
            |_, report| assert!(!report.is_memory_checked_core0()),
        );
    }
    inspect(
        "fn main()->u64 { let flag=true; let a=[42,42]; return a[choose(&flag)]; }
        fn choose(p:&bool)->usize { if *p { return 0usize; } return 1usize; }",
        |unit, report| {
            assert!(report.is_memory_checked_core0());
            let f = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == "choose")
                .unwrap();
            let Knowledge::Known(alternatives) =
                &report.functions()[&f.id].summary().normal_returns
            else {
                panic!()
            };
            assert_eq!(alternatives.len(), 1);
            assert!(alternatives[0].guard.is_empty());
            assert_eq!(alternatives[0].worlds.len(), 2);
        },
    );
}

#[test]
fn wrong_branch_and_discarded_guard_never_hide_freed_input_or_bad_results() {
    for source in [
        OWNER.replace("if flag { if old!=&raw *returned { return 0; } }", "if flag { return *returned; } if old!=&raw *returned { return 0; }"),
        OWNER.replace("if flag { if old!=&raw *returned { return 0; } }", "if old!=&raw *returned { return 0; }"),
        OWNER.replace("if flag { if old!=&raw *returned { return 0; } }", "{ let flag=true; if flag { if old!=&raw *returned { return 0; } } }"),
        "fn main()->u64 { return run(true); } fn run(flag:bool)->u64 { let a=[42]; return a[index(flag)]; }
         fn index(flag:bool)->usize { if flag { return 0usize; } return 1usize; }".into(),
    ] {
        inspect(&source, |_, report| assert!(!report.is_memory_checked_core0()));
    }
    // Empty feasible-return selection is not a license to erase the caller's
    // continuation. Do not execute this deliberate diverging program.
    inspect(
        "fn main()->u64 { let a=[42]; return a[index(false)]; }
        fn index(flag:bool)->usize { if flag { return 0usize; } while true {} return 2usize; }",
        |_, report| assert!(!report.is_memory_checked_core0()),
    );
}

#[test]
fn world_deletion_guard_and_result_mutation_and_budget_fail_closed() {
    inspect(OWNER, |unit, report| {
        let f = unit
            .runtime()
            .functions
            .iter()
            .find(|f| f.name == "choose")
            .unwrap();
        let original = report.functions()[&f.id].summary();
        for mutation in 0..3 {
            let mut summary = original.clone();
            let Knowledge::Known(ref mut alternatives) = summary.normal_returns else {
                panic!()
            };
            match mutation {
                0 => {
                    alternatives.pop();
                }
                1 => alternatives[0].guard.clear(),
                _ => alternatives[0].worlds[0].values.clear(),
            }
            assert!(
                summary
                    .validate_structure(unit, f.id, Default::default())
                    .is_err()
            );
        }
        let config = CfgAnalysisConfig {
            max_guarded_cases_per_block: 1,
            ..Default::default()
        };
        let limited = verify_program(unit, config).unwrap();
        assert!(!limited.is_memory_checked_core0());
        assert_eq!(limited, verify_program(unit, config).unwrap());
    });
}
