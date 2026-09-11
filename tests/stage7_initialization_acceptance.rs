#[path = "support/frontend_checks.rs"]
mod frontend_checks;
#[path = "../src/bin/fuzz_support/initialization_cases.rs"]
mod initialization_cases;

use nera::{
    CfgAnalysisConfig, SourceFile, VirInstruction, VirRuntimeValue, analyze, interpret,
    verify_program,
};

const MATRIX: &str = include_str!("../spec/cases/verify/initialization-acceptance.nera");

#[test]
fn combined_initialization_matrix_replays_plans_findings_and_execution() {
    frontend_checks::checked("initialization-acceptance.nera", MATRIX, 42);
    let output = frontend_checks::accepted("initialization-acceptance.nera", MATRIX);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let first = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert_eq!(
        first,
        verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
    );
    assert!(
        first
            .functions()
            .values()
            .all(|function| function.cfg().all_obligations_proven())
    );
    for ordinal in 0..16 {
        initialization_cases::check_effect_mutation(output.vir().unwrap(), ordinal);
    }
}

#[test]
fn generated_initialization_families_cover_both_verdicts_and_effect_origin_mutations() {
    for ordinal in 0..initialization_cases::FAMILY_COUNT * 8 {
        let source = initialization_cases::source(ordinal, ordinal.wrapping_mul(0x9e37_79b9));
        let output = frontend_checks::accepted("initialization-family.nera", &source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let first = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert_eq!(
            first,
            verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
        );
        assert_eq!(
            first.is_memory_checked_core0(),
            initialization_cases::expected_checked(ordinal),
            "{source}\n{:#?}",
            first.diagnostics()
        );
        if first.is_memory_checked_core0() {
            interpret(resolved.runtime()).unwrap();
        } else {
            assert!(!first.diagnostics().is_empty());
        }
        initialization_cases::check_effect_mutation(output.vir().unwrap(), ordinal);
    }
}

#[test]
fn a_safe_execution_does_not_initialize_an_unvisited_branch() {
    let source = initialization_cases::source(4, 41);
    let output = frontend_checks::accepted("unvisited-initialization.nera", &source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let first = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!first.is_memory_checked_core0());
    // Deliberately unverified execution; never part of the checked differential.
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(10)]
    );
    assert_eq!(
        first,
        verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
    );
    let missing = first
        .functions()
        .values()
        .flat_map(|f| f.cfg().obligations())
        .filter(|record| !record.obligation().is_proven())
        .collect::<Vec<_>>();
    assert!(!missing.is_empty());
    assert!(
        missing
            .iter()
            .any(|record| matches!(record.obligation().kind(),
                nera::ResourceObligationKind::MemoryInitialized { access: Some(range), .. }
                    if range.start() == 8 && range.end() == 16
            )),
        "missing field retains its canonical byte range: {missing:#?}"
    );
    assert!(
        missing.iter().any(|record| {
            let span = record.finding().source_span();
            source
                .get(span.start()..span.end())
                .is_some_and(|text| text.contains("p.right"))
        }),
        "missing range retains its source access: {missing:#?}"
    );
}

#[test]
fn reduced_case_guard_iteration_and_evidence_budgets_never_promote_unsafe_inputs() {
    for ordinal in 4..initialization_cases::FAMILY_COUNT {
        let output = frontend_checks::accepted(
            "initialization-budget.nera",
            &initialization_cases::source(ordinal, 1234),
        );
        let resolved = output.vir().unwrap().resolve().unwrap();
        for config in [
            CfgAnalysisConfig {
                max_guarded_cases_per_block: 1,
                max_guard_atoms_per_case: 0,
                ..CfgAnalysisConfig::default()
            },
            CfgAnalysisConfig {
                max_refinement_passes: 0,
                max_refinement_block_visits: 0,
                ..CfgAnalysisConfig::default()
            },
            CfgAnalysisConfig {
                max_block_visits: 1,
                ..CfgAnalysisConfig::default()
            },
        ] {
            let first = verify_program(&resolved, config);
            assert_eq!(first, verify_program(&resolved, config));
            assert!(!first.is_ok_and(|result| result.is_memory_checked_core0()));
        }
    }
}

#[test]
fn definite_missing_value_unknown_join_and_unsupported_surface_stay_distinct() {
    let definite = frontend_checks::accepted("definite.nera", &initialization_cases::source(6, 0));
    let resolved = definite.vir().unwrap().resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        verification
            .diagnostics()
            .iter()
            .any(|d| d.kind() == nera::VerifierDiagnosticKind::RefutedObligation)
    );
    let conditional = frontend_checks::accepted(
        "unknown.nera",
        "fn main() -> u64 { return maybe(true); }
        fn maybe(b: bool) -> u64 { let mut value: u64; if b { value = 42; } return value; }",
    );
    let resolved = conditional.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig {
        max_guarded_cases_per_block: 1,
        max_guard_atoms_per_case: 0,
        max_refinement_passes: 0,
        max_refinement_block_visits: 0,
        ..CfgAnalysisConfig::default()
    };
    let verification = verify_program(&resolved, config).unwrap();
    assert!(!verification.is_memory_checked_core0());
    assert!(
        verification
            .diagnostics()
            .iter()
            .any(|d| d.kind() == nera::VerifierDiagnosticKind::MissingFact)
    );
    let unsupported = analyze(&SourceFile::from_text(
        "unsupported.nera",
        "enum E { Empty, Value(u64), } fn main() -> u64 { let mut value: E; return 0; }",
    ));
    assert_eq!(unsupported.status(), nera::FrontendStatus::Unsupported);
    assert!(unsupported.vir().is_none());
}

#[test]
fn initialization_region_metadata_remains_ghost_non_interfering() {
    let output = frontend_checks::accepted("initialization-ghost.nera", MATRIX);
    let baseline = output.vir().unwrap();
    let mut enriched = baseline.as_unit().clone();
    let mut regions = enriched.borrows.regions().to_vec();
    for region in &mut regions {
        if region.origin == nera::VirBorrowRegionOrigin::Inferred {
            region.origin = nera::VirBorrowRegionOrigin::Lexical;
        }
    }
    enriched.borrows =
        nera::VirBorrowEnvironment::from_tables(regions, enriched.borrows.constraints().to_vec());
    let enriched = enriched.into_validated().unwrap();
    assert_ne!(baseline.stable_dump(), enriched.stable_dump());
    let baseline = baseline.resolve().unwrap();
    let enriched = enriched.resolve().unwrap();
    for resolved in [&baseline, &enriched] {
        assert!(
            verify_program(resolved, CfgAnalysisConfig::default())
                .unwrap()
                .is_memory_checked_core0()
        );
    }
    assert_eq!(
        interpret(baseline.runtime()).unwrap(),
        interpret(enriched.runtime()).unwrap()
    );
    let target = nera::backend::X86_64_UNKNOWN_LINUX_GNU;
    assert_eq!(
        target.plan_program(baseline.runtime()).unwrap(),
        target.plan_program(enriched.runtime()).unwrap()
    );
    assert_eq!(
        target.codegen_program(baseline.runtime()).unwrap(),
        target.codegen_program(enriched.runtime()).unwrap()
    );
}

/// Fixed corpus, default config, debug build. Wall time is recorded, never a
/// flaky pass threshold; structural bounds are the regression assertions.
#[test]
fn fixed_corpus_records_scaling_without_analysis_loop_unrolling() {
    println!("initialization config: {:?}", CfgAnalysisConfig::default());
    for length in [1, 8, 64, 512] {
        let source = format!(
            "fn main() -> u64 {{ let mut a: [u64; {length}];
            for i in 0usize..{length}usize {{ a[i] = 42; }} let whole = a; return whole[{}]; }}",
            length - 1
        );
        let start = std::time::Instant::now();
        let output = analyze(&SourceFile::from_text(
            "initialization-scaling.nera",
            &source,
        ));
        let frontend = start.elapsed();
        let validated = output.vir().expect("fixed array lowers");
        let access = validated.as_unit().runtime.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| match i.instruction {
                VirInstruction::StorageReset { access, .. } => Some(access),
                _ => None,
            })
            .unwrap();
        let shape = validated.as_unit().memory.object_shape(access).unwrap();
        let resolved = validated.resolve().unwrap();
        let start = std::time::Instant::now();
        let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        let verify = start.elapsed();
        assert!(verification.is_memory_checked_core0());
        let cfg = verification.functions()[&nera::VirFunctionId::new(0)].cfg();
        let ranges = cfg
            .blocks()
            .values()
            .flat_map(|b| b.instruction_states())
            .flat_map(|state| state.allocations().values())
            .map(|a| {
                a.initialization().initialized().ranges().len()
                    + a.initialization().uninitialized().ranges().len()
                    + a.valid_value_bytes().ranges().len()
            })
            .max()
            .unwrap_or(0);
        let start = std::time::Instant::now();
        nera::backend::X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(resolved.runtime())
            .unwrap();
        let codegen = start.elapsed();
        assert!(cfg.block_visits() < 50, "not {length} iterations");
        assert_eq!(shape.leaves().len(), length);
        assert_eq!(shape.value_bytes().len(), 1);
        assert!(ranges <= 4, "contiguous facts stay compact");
        println!(
            "initialization scaling: length={length} leaves={} value_ranges={} peak_fact_ranges={ranges} visits={} obligations={} frontend_us={} verify_us={} codegen_us={}",
            shape.leaves().len(),
            shape.value_bytes().len(),
            cfg.block_visits(),
            cfg.obligations().len(),
            frontend.as_micros(),
            verify.as_micros(),
            codegen.as_micros()
        );
    }
}
