use nera::*;
#[path = "support/spec_local_arena.rs"]
mod fixture;
#[path = "support/spec_arena.rs"]
#[allow(dead_code)]
mod raw;

fn lower(source: &str) -> ValidatedVirUnit {
    let output = analyze(&SourceFile::from_text("spec-arena-local.nera", source));
    assert!(output.vir().is_some(), "{:?}", output.issues());
    output.vir().unwrap().clone()
}

#[path = "support/runtime_origins.rs"]
mod runtime_origins;
use runtime_origins::runtime_with_resolved_origins;

#[test]
fn local_arena_checks_real_guards_and_restored_storage_at_runtime() {
    let annotated = lower(fixture::SOURCE);
    let erased = lower(&fixture::erased());
    let resolved = annotated.resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let report = verify_program(&resolved, config).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    assert!(annotated.as_unit().specs.trust_entries().is_empty());
    assert!(annotated.as_unit().specs.proves().is_empty());
    assert_ne!(
        runtime_with_resolved_origins(&annotated),
        runtime_with_resolved_origins(&erased)
    );
    assert!(
        verify_program(&erased.resolve().unwrap(), config)
            .unwrap()
            .is_memory_checked_core0()
    );
    // Concrete independent oracle; also exercise both guards and rejected bounds.
    for first in 0..=6 {
        for second in 0..=6 {
            let source = fixture::SOURCE.replace(
                "arena(1usize, 3usize)",
                &format!("arena({first}usize, {second}usize)"),
            );
            let unit = lower(&source);
            assert_eq!(
                interpret(unit.resolve().unwrap().runtime())
                    .unwrap()
                    .values(),
                [VirRuntimeValue::U64(
                    if 0 < first && first < second && second < 6 {
                        49
                    } else {
                        0
                    }
                )]
            );
        }
    }
}

#[test]
fn arena_assertions_do_not_hide_invalid_bounds_overflow_or_overlap() {
    for (from, to) in [
        ("assert second < 6usize;", "assert second > 6usize;"),
        ("parent[first..second]", "parent[0usize..second]"),
    ] {
        let unit = lower(&fixture::SOURCE.replace(from, to));
        let report =
            verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
        assert!(!report.is_memory_checked_core0(), "mutation {to}");
        assert!(
            report
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .any(|o| !o.obligation().status().is_proven())
        );
        if from.starts_with("assert") {
            assert_eq!(
                interpret(unit.resolve().unwrap().runtime())
                    .unwrap_err()
                    .kind(),
                &VirExecutionErrorKind::CheckFailed
            );
        }
    }
    let unit = lower(fixture::SOURCE);
    let config = CfgAnalysisConfig {
        max_relation_evidence: 0,
        ..Default::default()
    };
    assert!(matches!(
        verify_program(&unit.resolve().unwrap(), config),
        Err(VerificationError::Cfg {
            error: CfgAnalysisError::RelationEvidenceBudgetExceeded { limit: 0, .. },
            ..
        })
    ));
}

#[test]
fn passing_runtime_checks_cannot_mask_a_later_memory_failure() {
    let source = fixture::SOURCE.replace(
        "return answer;",
        "let p=alloc<u64>(1); free(p); return *p + answer;",
    );
    let unit = lower(&source);
    let report = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert!(unit.as_unit().specs.proves().is_empty());
    assert!(!report.is_memory_checked_core0());
}

#[test]
fn active_parent_element_reborrow_precision_gap_remains_unproved() {
    // Baseline parent access succeeds, but a new element reborrow while the
    // sibling-slice scope is active is not yet reconstructed precisely.
    let source = raw::SOURCE.replace(
        "return parent[0] + sentinel;",
        "let probe = &parent[0]; return *probe + sentinel;",
    );
    let unit = lower(&source);
    let report = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| matches!(
                o.obligation().kind(),
                ResourceObligationKind::LoanCompatible { .. }
            ) && !o.obligation().status().is_proven())
    );
}

#[test]
fn measure_local_arena_when_requested() {
    if std::env::var_os("NERA_SPEC_LOCAL_MEASURE").is_none() {
        return;
    }
    let baseline = lower(raw::SOURCE);
    let local = lower(fixture::SOURCE);
    let erased = lower(&fixture::erased());
    let raw = raw::unit(1, 3, raw::Mutation::None)
        .into_validated()
        .unwrap();
    let dynamic = raw::unit(1, 3, raw::Mutation::DynamicInitialization)
        .into_validated()
        .unwrap();
    println!(
        "case,sample,checked,cfg_queries,spec_queries,block_visits,refinement_visits,cfg_obligations,proves,spec_terms,verify_us"
    );
    for (name, unit, expected) in [
        ("baseline", baseline, true),
        ("local-erased", erased, true),
        ("local", local, true),
        ("raw", raw, true),
        ("raw-dynamic", dynamic, false),
    ] {
        let resolved = unit.resolve().unwrap();
        for sample in 0..5 {
            let start = std::time::Instant::now();
            let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
            let elapsed = start.elapsed().as_micros();
            assert_eq!(report.is_memory_checked_core0(), expected);
            let functions: Vec<_> = report.functions().values().collect();
            let cfg_queries: usize = functions
                .iter()
                .map(|f| f.cfg().relation_queries().len())
                .sum();
            let spec_queries: usize = functions
                .iter()
                .flat_map(|f| f.proofs())
                .map(|p| p.relation_queries().len())
                .sum();
            let visits: u64 = functions.iter().map(|f| f.cfg().block_visits()).sum();
            let refinements: u64 = functions
                .iter()
                .map(|f| f.cfg().refinement_block_visits())
                .sum();
            let obligations: usize = functions.iter().map(|f| f.cfg().obligations().len()).sum();
            let proves: usize = functions.iter().map(|f| f.proofs().len()).sum();
            let terms = unit.as_unit().specs.terms().len();
            println!(
                "{name},{sample},{expected},{cfg_queries},{spec_queries},{visits},{refinements},{obligations},{proves},{terms},{elapsed}"
            );
        }
    }
}
