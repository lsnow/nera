use nera::*;
#[path = "support/loop_baseline.rs"]
mod fixture;

fn inspect(source: &str) -> (FrontendOutput, ProgramVerification) {
    inspect_with_config(source, Default::default())
}

fn inspect_with_config(
    source: &str,
    config: CfgAnalysisConfig,
) -> (FrontendOutput, ProgramVerification) {
    let output = analyze(&SourceFile::from_text("loop-baseline.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let report = verify_program(&output.vir().unwrap().resolve().unwrap(), config).unwrap();
    (output, report)
}

#[test]
fn scalar_and_stable_resource_targets_are_admitted_and_checked() {
    for source in [fixture::SCALAR, fixture::UPDATE, fixture::INITIALIZE] {
        let output = analyze(&SourceFile::from_text("loop-target.nera", source));
        assert_eq!(
            output.status(),
            FrontendStatus::AcceptedProposal,
            "{:?}",
            output.issues()
        );
        assert!(output.vir().is_some());
        {
            assert!(
                verify_program(
                    &output.vir().unwrap().resolve().unwrap(),
                    Default::default()
                )
                .unwrap()
                .is_memory_checked_core0()
            );
        }
        assert_eq!(source.len(), fixture::erased(source).len());
    }
}

#[test]
fn legacy_implicit_analysis_without_candidates_retains_its_baseline() {
    for (name, source) in [
        ("scalar", fixture::SCALAR),
        ("update", fixture::UPDATE),
        ("initialize", fixture::INITIALIZE),
    ] {
        for n in [0, 1, 6, 8] {
            let source = fixture::erased(source).replacen("6usize", &format!("{n}usize"), 1);
            let (output, report) = inspect_with_config(
                &source,
                CfgAnalysisConfig {
                    max_loop_candidates: 0,
                    ..Default::default()
                },
            );
            assert!(!report.is_memory_checked_core0());
            // Current failure is contract availability, not an unsafe loop
            // body or an unsupported source construct.
            assert!(
                report.functions()[&VirFunctionId::new(1)]
                    .cfg()
                    .all_obligations_proven()
            );
            assert!(
                report.functions()[&VirFunctionId::new(0)]
                    .cfg()
                    .obligations()
                    .iter()
                    .any(|o| matches!(
                        o.obligation().kind(),
                        ResourceObligationKind::CallContractAvailable { .. }
                    ) && o.obligation().status() == ObligationStatus::Unknown)
            );
            let result = interpret(output.vir().unwrap().resolve().unwrap().runtime()).unwrap();
            let expected = if name == "scalar" {
                if n == 6 { 42 } else { 99 }
            } else if n == 0 {
                0
            } else {
                42
            };
            assert_eq!(result.values(), [VirRuntimeValue::U64(expected)]);
            assert!(
                output
                    .vir()
                    .unwrap()
                    .as_unit()
                    .specs
                    .trust_entries()
                    .is_empty()
            );
        }
    }
}

#[test]
fn local_expansion_retains_the_existing_implicit_prefix_proof() {
    for (name, source) in [
        ("scalar", fixture::SCALAR),
        ("update", fixture::UPDATE),
        ("initialize", fixture::INITIALIZE),
    ] {
        for n in [0, 1, 6, 8] {
            let (output, report) = inspect(&fixture::inline(source, n));
            assert!(
                report.is_memory_checked_core0(),
                "{name}/{n}: {:?}",
                report.diagnostics()
            );
            assert_eq!(
                interpret(output.vir().unwrap().resolve().unwrap().runtime())
                    .unwrap()
                    .values(),
                [VirRuntimeValue::U64(if n == 0 && name != "scalar" {
                    0
                } else {
                    42
                })]
            );
        }
    }
}

#[test]
fn missing_write_early_exit_and_out_of_bounds_do_not_become_initialization() {
    let source =
        fixture::inline(fixture::INITIALIZE, 6).replace("let value = p[0];", "let value = p[5];");
    assert!(inspect(&source).1.is_memory_checked_core0());
    for bad in [
        source.replace("p[i] = 42;", "p[0] = 42;"),
        source.replace("p[i] = 42;", "p[i] = 42; if i == 0usize { break; }"),
        source.replace("while i < n", "while i < 9usize"),
    ] {
        let (output, report) = inspect(&bad);
        assert!(!report.is_memory_checked_core0());
        assert!(
            report
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .any(|o| !o.obligation().is_proven())
        );
        assert!(interpret(output.vir().unwrap().resolve().unwrap().runtime()).is_err());
    }
}

#[test]
fn measure_loop_baseline_when_requested() {
    if std::env::var_os("NERA_LOOP_BASELINE_MEASURE").is_none() {
        return;
    }
    println!(
        "case,sample,checked,relation_queries,block_visits,refinement_visits,obligations,postconditions,verify_us"
    );
    for (name, source) in [
        ("scalar", fixture::SCALAR),
        ("update", fixture::UPDATE),
        ("initialize", fixture::INITIALIZE),
    ] {
        for (profile, source, expected) in [
            ("interface", fixture::erased(source), false),
            ("inline", fixture::inline(source, 6), true),
        ] {
            let output = analyze(&SourceFile::from_text(name, source));
            let resolved = output.vir().unwrap().resolve().unwrap();
            for sample in 0..5 {
                let start = std::time::Instant::now();
                let report = verify_program(&resolved, Default::default()).unwrap();
                let micros = start.elapsed().as_micros();
                assert_eq!(report.is_memory_checked_core0(), expected);
                let fs: Vec<_> = report.functions().values().collect();
                println!(
                    "{name}-{profile},{sample},{expected},{},{},{},{},{},{micros}",
                    fs.iter()
                        .map(|f| f.cfg().relation_queries().len())
                        .sum::<usize>(),
                    fs.iter().map(|f| f.cfg().block_visits()).sum::<u64>(),
                    fs.iter()
                        .map(|f| f.cfg().refinement_block_visits())
                        .sum::<u64>(),
                    fs.iter()
                        .map(|f| f.cfg().obligations().len())
                        .sum::<usize>(),
                    fs.iter().map(|f| f.postconditions().len()).sum::<usize>()
                );
            }
        }
    }
}
