use nera::verifier::summary::*;
use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, VirRuntimeValue, analyze, verify_program,
};

fn inspect(
    source: &str,
    check: impl FnOnce(&nera::ResolvedVirUnit<'_>, &nera::ProgramVerification),
) {
    let output = analyze(&SourceFile::from_text("summary-calls.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&resolved, Default::default()).unwrap();
    for (&id, function) in report.functions() {
        function
            .summary()
            .validate_structure(&resolved, id, Default::default())
            .unwrap();
    }
    check(&resolved, &report);
}
fn summary<'a>(
    unit: &nera::ResolvedVirUnit<'_>,
    report: &'a nera::ProgramVerification,
    name: &str,
) -> &'a FunctionSummary {
    let id = unit
        .runtime()
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap()
        .id;
    report.functions()[&id].summary()
}

#[test]
fn wrappers_constants_owner_identity_and_fresh_instances_close_in_one_product_path() {
    inspect(
        include_str!("../spec/cases/verify/summary-calls.nera"),
        |unit, report| {
            assert!(
                report.is_memory_checked_core0(),
                "{:?}",
                report.diagnostics()
            );
            for name in ["make", "inner", "outer", "index_inner", "index_outer"] {
                assert_eq!(
                    summary(unit, report, name).state,
                    SummaryState::Closed,
                    "{name}"
                );
            }
            assert!(
                summary(unit, report, "outer")
                    .dependencies
                    .iter()
                    .all(|d| d.state == SummaryState::Closed)
            );
            assert!(
                summary(unit, report, "main")
                    .call_uses
                    .iter()
                    .all(|c| c.outcome == CallSummaryOutcome::Applied)
            );
            assert_eq!(
                nera::interpret(unit.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(42)]
            );
            let main = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == "main")
                .unwrap();
            let instances = report.functions()[&main.id]
                .cfg()
                .blocks()
                .values()
                .flat_map(|b| b.instruction_states())
                .flat_map(|s| s.allocations().keys())
                .filter(|id| matches!(id, nera::AbstractAllocationId::SummaryInstance { .. }))
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(
                instances.len(),
                2,
                "each call must instantiate a distinct existential"
            );
        },
    );
}

#[test]
fn may_effects_record_reads_writes_restores_and_hidden_local_lifetimes() {
    inspect("fn main()->u64 { let mut n=42; outer(&mut n); let v=read(&n); let discarded=local(); return v; }
        fn outer(p:&mut u64) { restore(p); return; }
        fn restore(p:&mut u64) { *p=1; *p=42; return; }
        fn read(p:&u64)->u64 { return *p; }
        fn local()->u64 { let p=alloc<u64>(1); *p=42; let v=*p; free(p); return v; }", |unit, report| {
        assert!(report.is_memory_checked_core0());
        for name in ["restore", "outer"] {
            let s = summary(unit, report, name);
            assert_eq!(s.state, SummaryState::Closed, "{name}: {s:?}");
            assert!(matches!(&s.effects.may_write, Knowledge::Known(w) if !w.is_empty()));
        }
        let read = summary(unit, report, "read");
        assert_eq!(read.effects.may_write, Knowledge::Known(vec![]));
        assert!(matches!(&read.effects.may_read, Knowledge::Known(r) if !r.is_empty()));
        let local = summary(unit, report, "local");
        assert_eq!(local.state, SummaryState::Closed);
        assert_eq!(local.effects.may_free, Knowledge::Known(vec![]));
        assert!(local.local_effect_events >= 3);
        assert_eq!(nera::interpret(unit.runtime()).unwrap().values(), [VirRuntimeValue::U64(42)]);
    });
}

#[test]
fn frame_preserves_disjoint_fields_and_shared_aliases_without_assuming_distinct_parameters() {
    inspect("struct Pair { a:u64, b:u64, }
        fn main()->u64 { let mut pair=Pair { a:21, b:0 }; write(&mut pair.b); return sum(&pair.a, &pair.a); }
        fn write(p:&mut u64) { *p=42; return; }
        fn sum(a:&u64,b:&u64)->u64 { return *a+*b; }", |unit, report| {
        assert!(report.is_memory_checked_core0());
        assert!(summary(unit, report, "main").call_uses.iter().all(|c| c.outcome == CallSummaryOutcome::Applied));
        assert_eq!(nera::interpret(unit.runtime()).unwrap().values(), [VirRuntimeValue::U64(42)]);
    });
}

#[test]
fn unsafe_callees_remain_unpublished_while_proved_recursive_sccs_close() {
    inspect(
        "fn main()->u64 { bad(); return 42; } fn bad() { let p=alloc<u64>(1); let x=*p; free(p); return; }",
        |unit, report| {
            assert!(!report.is_memory_checked_core0());
            let bad = summary(unit, report, "bad");
            assert!(matches!(bad.state, SummaryState::Unknown(_)));
            assert!(
                bad.faults
                    .requirements
                    .iter()
                    .any(|r| r.status == nera::ObligationStatus::Refuted)
            );
            assert!(
                bad.local_effect_events > 0,
                "fault-before-return effects retained"
            );
            assert!(
                summary(unit, report, "main")
                    .call_uses
                    .iter()
                    .all(|c| c.outcome == CallSummaryOutcome::NotClosed)
            );
        },
    );
    inspect(
        "fn main()->u64 { return recurse(true); } fn recurse(stop:bool)->u64 { if stop { return 42; } return recurse(true); }",
        |unit, report| {
            assert!(report.is_memory_checked_core0());
            assert_eq!(summary(unit, report, "recurse").state, SummaryState::Closed);
            assert!(
                summary(unit, report, "main")
                    .call_uses
                    .iter()
                    .all(|c| c.outcome == CallSummaryOutcome::Applied)
            );
        },
    );
}

#[test]
fn publication_is_order_independent_and_closed_dumps_are_not_import_authority() {
    for source in [
        "fn main()->u64 { let a=[42]; return a[outer()]; } fn outer()->usize { return leaf(); } fn leaf()->usize { return 0usize; }",
        "fn leaf()->usize { return 0usize; } fn outer()->usize { return leaf(); } fn main()->u64 { let a=[42]; return a[outer()]; }",
    ] {
        inspect(source, |unit, report| {
            assert!(report.is_memory_checked_core0());
            let outer = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == "outer")
                .unwrap();
            let s = summary(unit, report, "outer");
            let mut mutated = s.clone();
            mutated.state = SummaryState::Candidate;
            assert!(
                mutated
                    .validate_structure(unit, outer.id, Default::default())
                    .is_err()
            );
            let mut mutated = s.clone();
            mutated.dependencies[0].state = SummaryState::Uncomputed;
            assert!(
                mutated
                    .validate_structure(unit, outer.id, Default::default())
                    .is_err()
            );
            assert!(
                s.validate_structure(
                    unit,
                    outer.id,
                    CfgAnalysisConfig {
                        max_block_visits: 1,
                        ..Default::default()
                    }
                )
                .is_err()
            );
            assert_eq!(report, &verify_program(unit, Default::default()).unwrap());
        });
    }
}

#[test]
fn closed_callee_does_not_excuse_alias_conflicts_or_invalid_result_bounds() {
    for source in [
        "fn main()->u64 { let mut x=42; let p=&mut x; write(p,p); return x; }
        fn write(a:&mut u64,b:&mut u64) { *a=20; *b=22; return; }",
        "fn main()->u64 { let a=[42]; return a[index()]; }
        fn index()->usize { return 3usize; }",
    ] {
        inspect(source, |unit, report| {
            assert!(!report.is_memory_checked_core0());
            assert!(
                report
                    .functions()
                    .values()
                    .any(|f| f.summary().state == SummaryState::Closed)
            );
            assert!(nera::interpret(unit.runtime()).is_err());
        });
    }
}

#[test]
fn repeated_fresh_call_site_reuses_only_retired_instances_and_budget_loss_is_not_a_frame() {
    inspect(
        "fn main()->u64 { for i in 0usize..3usize { let p=make(); free(p); } return 42; }
        fn make()->Own<u64> { let p=alloc<u64>(1); *p=42; return p; }",
        |unit, report| {
            assert!(
                report.is_memory_checked_core0(),
                "{:?}",
                report.diagnostics()
            );
            assert_eq!(summary(unit, report, "make").state, SummaryState::Closed);
            assert!(
                summary(unit, report, "main")
                    .call_uses
                    .iter()
                    .all(|c| c.outcome == CallSummaryOutcome::Applied)
            );
            assert_eq!(
                nera::interpret(unit.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(42)]
            );
            let limited = verify_program(
                unit,
                CfgAnalysisConfig {
                    max_relation_evidence: 0,
                    ..Default::default()
                },
            );
            assert!(matches!(
                limited,
                Err(nera::VerificationError::Cfg {
                    error: nera::CfgAnalysisError::RelationEvidenceBudgetExceeded { limit: 0, .. },
                    ..
                })
            ));
        },
    );
}
