use nera::verifier::summary::*;
use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, VirRuntimeValue, analyze, verify_program,
};

fn inspect(
    source: &str,
    check: impl FnOnce(&nera::ResolvedVirUnit<'_>, &nera::ProgramVerification),
) {
    let output = analyze(&SourceFile::from_text("summary-borrows.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let unit = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&unit, CfgAnalysisConfig::default()).unwrap();
    check(&unit, &report);
}

fn checked(source: &str, expected: u64) {
    inspect(source, |unit, report| {
        assert!(
            report.is_memory_checked_core0(),
            "{:?}",
            report.diagnostics()
        );
        for function in report.functions().values() {
            // Site-local audit snapshots intentionally retain caller loan IDs;
            // only the cross-call interface must remain signature-relative.
            let s = function.summary();
            assert!(
                !format!(
                    "{:?}",
                    (&s.inputs, &s.input_resources, &s.normal_returns, &s.effects)
                )
                .contains("VirLoanId")
            );
            if let Knowledge::Known(alternatives) = &function.summary().normal_returns {
                for restoration in alternatives
                    .iter()
                    .flat_map(|a| &a.worlds)
                    .flat_map(|w| &w.borrow_restoration)
                {
                    assert_eq!(
                        restoration.permission.availability,
                        nera::PermissionAvailability::Available
                    );
                }
            }
            assert!(
                function
                    .summary()
                    .call_uses
                    .iter()
                    .all(|c| c.outcome == CallSummaryOutcome::Applied),
                "{:?}",
                report
                    .functions()
                    .iter()
                    .map(|(id, f)| (id, &f.summary().state, &f.summary().call_uses))
                    .collect::<Vec<_>>()
            );
        }
        assert_eq!(
            nera::interpret(unit.runtime()).unwrap().values(),
            [VirRuntimeValue::U64(expected)]
        );
    });
}

#[test]
fn conditional_mutable_view_restores_only_the_current_child_endpoint() {
    for (flag, expected) in [("true", 42), ("false", 21)] {
        checked(
            &include_str!("../spec/cases/verify/summary-borrows.nera")
                .replace("run(true)", &format!("run({flag})")),
            expected,
        );
    }
}

#[test]
fn shared_aliases_and_empty_views_do_not_gain_unique_authority() {
    checked("fn main()->u64 { let values=[10,20,30]; let view=&values[1..]; let a=outer(view); let b=outer(view); return sum(a,b); }
        fn outer(v:&[u64])->&[u64] { return v; }
        fn sum(a:&[u64],b:&[u64])->u64 { if len(a)>0usize { if len(b)>0usize { return a[0]+b[0]; } } return 0; }", 40);
    checked("fn main()->u64 { let values=[10,20,30]; let view=outer(&values[3..]); if len(view)==0usize { return 42; } return 0; }
        fn outer(v:&[u64])->&[u64] { return inner(v); } fn inner(v:&[u64])->&[u64] { return v; }", 42);
}

#[test]
fn conditional_borrow_effects_compose_with_reborrow_and_owner_restoration() {
    for flag in ["true", "false"] {
        checked(
            &format!(
                "fn main()->u64 {{ return run({flag}); }}
            fn run(flag:bool)->u64 {{ let mut value=1; let parent=&mut value;
                {{ let child=&mut *parent; update(child,flag); }} return *parent; }}
            fn update(r:&mut u64,flag:bool) {{ if flag {{ let child=&mut *r; nested(child); }} else {{ *r=42; }} return; }}
            fn nested(r:&mut u64) {{ *r=42; return; }}"
            ),
            42,
        );
        checked(&format!("fn main()->u64 {{ return run({flag}); }}
            fn run(flag:bool)->u64 {{ let mut a=1; let mut b=1; update(&mut a,&mut b,flag); return a+b; }}
            fn update(a:&mut u64,b:&mut u64,flag:bool) {{ if flag {{ *a=42; }} else {{ *b=42; }} return; }}"), 43);
    }
}

#[test]
fn wrong_range_early_parent_use_and_local_escape_fail_closed() {
    for source in [
        "fn main()->u64 { let values=[10,20,30]; let view=id(&values[1..]); return view[2]; } fn id(v:&[u64])->&[u64] { return v; }",
        "fn main()->u64 { let values=[10,20,30]; let view=id(&values[3..]); return view[0]; } fn id(v:&[u64])->&[u64] { return v; }",
        "fn main()->u64 { let mut value=1; let parent=&mut value; let child=&mut *parent; let view=id(child); *parent=2; return *view; } fn id(r:&mut u64)->&mut u64 { return r; }",
        "fn main()->u64 { let mut value=1; let view=id(&value); value=2; return *view; } fn id(r:&u64)->&u64 { return r; }",
    ] {
        inspect(source, |unit, report| {
            assert!(!report.is_memory_checked_core0(), "{source}");
            assert!(
                nera::interpret(unit.runtime()).is_err(),
                "loan shadow or bounds must independently reject: {source}"
            );
        });
    }
}

#[test]
fn unexpressed_region_and_payload_interfaces_remain_frontend_gated() {
    for source in [
        "fn bad(r:&u64)->&u64 { let value=42; return &value; }",
        "fn choose(a:&u64,b:&u64,flag:bool)->&u64 { if flag { return a; } return b; }",
        "fn tail(v:&[u64])->&[u64] { if len(v)>0usize { return &v[1..]; } return v; }",
        "struct Holder { r: &u64, n: u64 } fn id(v:Holder)->Holder { return v; }",
    ] {
        let output = analyze(&SourceFile::from_text("gated.nera", source));
        assert_ne!(
            output.status(),
            FrontendStatus::AcceptedProposal,
            "{source}"
        );
    }
}

#[test]
fn borrowed_world_mutations_and_stale_analysis_are_not_import_authority() {
    inspect(
        "fn main()->u64 { let value=42; let r=id(&value,true); return *r; }
        fn id(r:&u64,flag:bool)->&u64 { if flag { return r; } return r; }",
        |unit, report| {
            let function = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == "id")
                .unwrap();
            let original = report.functions()[&function.id].summary();
            assert_eq!(original.state, SummaryState::Closed);
            for mutation in 0..7 {
                let mut summary = original.clone();
                let Knowledge::Known(alternatives) = &mut summary.normal_returns else {
                    panic!();
                };
                let world = &mut alternatives[0].worlds[0];
                match mutation {
                    0 => world.borrow_restoration.clear(),
                    1 => world.borrow_restoration[0].activity = nera::LoanActivity::Ended,
                    2 => world.borrow_restoration[0].permission.authority = SummaryAuthority::Owner,
                    3 => world.borrow_restoration[0].permission.range = SummaryRange::Unknown,
                    4 => world.resources[0].region = Some(nera::VirRegionId::new(99)),
                    5 => {
                        let SummaryValue::Pointer(p) = &mut world.values[0].value else {
                            panic!();
                        };
                        p.domain = SummaryDomain::Allocation;
                    }
                    _ => {
                        summary.version -= 1;
                    }
                }
                assert!(
                    summary
                        .validate_structure(unit, function.id, Default::default())
                        .is_err(),
                    "mutation {mutation}"
                );
            }
            let config = CfgAnalysisConfig {
                max_active_loans_per_case: 0,
                ..Default::default()
            };
            assert!(
                original
                    .validate_structure(unit, function.id, config)
                    .is_err()
            );
            let budgeted = verify_program(unit, config).unwrap();
            assert!(!budgeted.is_memory_checked_core0());
            assert_eq!(
                budgeted.functions()[&function.id].summary().stable_dump(),
                verify_program(unit, config).unwrap().functions()[&function.id]
                    .summary()
                    .stable_dump()
            );
        },
    );
}

#[test]
fn returned_subslice_wrappers_apply_body_summaries() {
    inspect(
        "fn main()->u64 { let values=[10,20,30]; let view=outer(&values[1..]); return view[1]; }
        fn outer(v:&[u64])->&[u64] { return inner(v); }
        fn inner(v:&[u64])->&[u64] { return v; }",
        |unit, report| {
            assert!(
                report.is_memory_checked_core0(),
                "{:?}",
                report.diagnostics()
            );
            for function in report.functions().values() {
                assert_eq!(
                    function.summary().state,
                    SummaryState::Closed,
                    "{:#?}",
                    function.summary()
                );
                assert!(
                    function
                        .summary()
                        .call_uses
                        .iter()
                        .all(|c| c.outcome == CallSummaryOutcome::Applied),
                    "{:?}",
                    function.summary().call_uses
                );
            }
            assert_eq!(
                nera::interpret(unit.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(30)]
            );
        },
    );
}
