use nera::verification::*;
use nera::*;
#[path = "support/cli_process.rs"]
mod cli_process;
#[path = "support/preview_checks.rs"]
mod preview_checks;
#[path = "../src/bin/fuzz_support/spec_mutation.rs"]
mod spec_mutation;
#[path = "../src/bin/fuzz_support/summary_cases.rs"]
mod summary_cases;

fn source(text: &str) -> SourceFile {
    SourceFile::from_text("fail-closed.nera", text)
}

fn limits() -> Vec<(&'static str, CfgAnalysisConfig)> {
    let mut result = Vec::new();
    macro_rules! limit { ($($field:ident),*) => { $(result.push((stringify!($field), CfgAnalysisConfig { $field: 0, ..Default::default() }));)* }; }
    limit!(
        max_block_visits,
        max_refinement_passes,
        max_refinement_block_visits,
        max_guarded_cases_per_block,
        max_guard_atoms_per_case,
        max_active_loans_per_case,
        max_aliases_per_loan,
        max_region_constraints_per_function,
        max_reborrow_depth,
        max_region_pairs_per_instruction,
        max_relation_evidence,
        max_summary_evidence
    );
    macro_rules! numeric { ($($field:ident),*) => { $(result.push((stringify!($field), CfgAnalysisConfig { relation_limits: nera::verifier::relation::difference::DifferenceLimits { $field: 0, ..Default::default() }, ..Default::default() }));)* }; }
    numeric!(
        max_variables,
        max_constraints,
        max_steps,
        max_derivations,
        max_branches
    );
    macro_rules! summary { ($($field:ident),*) => { $(result.push((stringify!($field), CfgAnalysisConfig { summary_limits: nera::verifier::summary::SccLimits { $field: 0, ..Default::default() }, ..Default::default() }));)* }; }
    summary!(
        max_functions,
        max_iterations,
        max_body_analyses,
        max_worlds,
        max_candidate_bytes
    );
    result
}

#[test]
fn independent_budget_reductions_never_promote_known_unsafe_sources() {
    let mut sources: Vec<_> = (4..summary_cases::FAMILY_COUNT)
        .map(|i| summary_cases::source(i, 0))
        .collect();
    sources.extend([
        include_str!("../spec/cases/verify/uaf.nera").to_owned(),
        "fn main()->u64 { let mut x=42; let p=&x; x=0; return *p; }".to_owned(),
    ]);
    for text in sources {
        let input = source(&text);
        let baseline = verify_source(&input, Default::default());
        assert_eq!(baseline.outcome(), PreviewOutcome::Unproved);
        for (name, config) in limits() {
            let preview = verify_source(&input, config);
            assert_eq!(
                preview.frontend_status(),
                Some(FrontendStatus::AcceptedProposal)
            );
            assert!(preview.is_resolved());
            assert!(!preview.is_checked(), "{name} promoted {text}");
            assert_eq!(preview.config(), config);
            preview_checks::observe(&preview);
            assert_eq!(preview, verify_source(&input, config), "{name} replay");
        }
    }
}

#[test]
fn precision_loss_and_mandatory_abort_are_distinct_from_fast_path_success() {
    let scalar = "fn main()->u64 { return index(0); } fn index(n:u64)->u64 { if n==2 { return 42; } return index(n+1); }";
    let indexed = summary_cases::source(0, 0);
    let config = CfgAnalysisConfig {
        summary_limits: nera::verifier::summary::SccLimits {
            max_iterations: 0,
            ..Default::default()
        },
        ..Default::default()
    };
    for (text, verdict) in [
        (scalar, PreviewOutcome::Checked),
        (indexed.as_str(), PreviewOutcome::Unproved),
    ] {
        let preview = verify_source(&source(text), config);
        assert_eq!(preview.outcome(), verdict);
        assert!(preview.counts().unwrap().summaries_unknown > 0);
        preview_checks::observe(&preview);
        let rendered = render_text(&preview, TextReportMode::Explain);
        assert!(rendered.contains("NotClosed"));
        assert!(rendered.contains("IterationBudget"));
    }
    let input = source("fn main()->u64 { let a=[42,0]; return a[0]; }");
    let config = CfgAnalysisConfig {
        relation_limits: nera::verifier::relation::difference::DifferenceLimits {
            max_variables: 0,
            max_constraints: 0,
            max_steps: 0,
            max_derivations: 0,
            max_branches: 0,
        },
        ..Default::default()
    };
    let preview = verify_source(&input, config);
    assert!(
        preview.is_checked(),
        "interval fast path does not require numeric closure"
    );
    preview_checks::observe(&preview);
    for config in [
        CfgAnalysisConfig {
            max_block_visits: 0,
            ..Default::default()
        },
        CfgAnalysisConfig {
            max_relation_evidence: 0,
            ..Default::default()
        },
    ] {
        let preview = verify_source(&source(&indexed), config);
        assert_eq!(preview.outcome(), PreviewOutcome::BudgetAborted);
        preview_checks::observe(&preview);
    }
}

#[test]
fn malformed_schema_is_reported_at_validation_not_as_a_source_error() {
    let preview = verify_source(&source("fn main()->u64 { return 42; }"), Default::default());
    let unit = preview.validated_unit().unwrap();
    for selector in 0..5 {
        spec_mutation::check_spec_mutation(unit, selector);
        let malformed = spec_mutation::malformed_spec_unit(unit, selector);
        let report = verify_unit(malformed, Default::default());
        assert_eq!(
            report.outcome(),
            PreviewOutcome::Rejected(PreviewStage::Validation)
        );
        assert_eq!(report.frontend_status(), None);
        assert!(!report.is_resolved());
        preview_checks::observe(&report);
    }
}

#[test]
fn forged_closure_and_deleted_failures_are_neither_replayable_nor_preview_inputs() {
    use nera::verifier::relation::audit::RelationReplayCache;
    use nera::verifier::summary::{SummaryState, audit::SummaryAudit};
    let input = source(&summary_cases::source(6, 0));
    let preview = verify_source(&input, Default::default());
    assert_eq!(preview.outcome(), PreviewOutcome::Unproved);
    let unit = preview.validated_unit().unwrap().resolve().unwrap();
    let original = SummaryAudit::from_report(preview.verification().unwrap());
    let cache = RelationReplayCache::new(&unit, Default::default()).unwrap();
    assert!(cache.accepts_summary_audit(&original));
    for deleted in [false, true] {
        let mut forged = original.clone();
        forged.memory_checked = true;
        for function in &mut forged.functions {
            function.summary.state = SummaryState::Closed;
            if deleted {
                function.requirements.clear();
                function.issues.clear();
                function.summary.faults.requirements.clear();
            }
        }
        assert!(!cache.accepts_summary_audit(&forged));
        preview_checks::observe(&preview);
        assert_eq!(preview.outcome(), PreviewOutcome::Unproved);
    }
    let mut display = preview.versions();
    display.report += 1;
    assert_ne!(display, preview.versions());
    assert_eq!(preview, verify_source(&input, Default::default()));
}

#[test]
fn source_and_dependency_edits_require_fresh_analysis_in_real_processes() {
    let fixture = cli_process::Fixture::new();
    let safe = "fn main()->u64 { let a=[42]; return a[outer()]; } fn outer()->usize { return index(); } fn index()->usize { return 0usize; }";
    let original = source(safe);
    let old = verify_source(&original, Default::default());
    assert!(old.is_checked());
    for (text, code) in [
        (safe.to_owned(), 0),
        (safe.replace("return 0usize", "return 1usize"), 1),
        (safe.to_owned(), 0),
    ] {
        let path = fixture.file("same-path.nera", &text);
        let input = SourceFile::load(&path).unwrap();
        let preview = verify_source(&input, Default::default());
        let changed = source(&text);
        assert_eq!(old.matches_source(&changed, Default::default()), code == 0);
        preview_checks::observe(&preview);
        for mode in [TextReportMode::Summary, TextReportMode::Explain] {
            let mut command = fixture.command();
            command.arg("verify");
            if mode == TextReportMode::Explain {
                command.arg("--explain");
            }
            let output = cli_process::run(command.arg(&path));
            assert_eq!(output.status.code(), Some(code));
            assert_eq!(output.stdout, render_text(&preview, mode).as_bytes());
            assert!(output.stderr.is_empty());
        }
    }
    let config = CfgAnalysisConfig {
        max_block_visits: 0,
        ..Default::default()
    };
    assert!(!old.matches_source(&original, config));
    let fresh = verify_source(&original, config);
    assert_eq!(fresh.outcome(), PreviewOutcome::BudgetAborted);
    preview_checks::observe(&fresh);
}

#[test]
fn partial_write_and_flush_failures_never_return_a_success_code() {
    use std::io::{self, Write};
    struct Broken {
        remaining: usize,
        flush: bool,
    }
    impl Write for Broken {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            if self.flush {
                return Ok(bytes.len());
            }
            if self.remaining == 0 {
                return Err(io::ErrorKind::BrokenPipe.into());
            }
            let count = bytes.len().min(self.remaining);
            self.remaining -= count;
            Ok(count)
        }
        fn flush(&mut self) -> io::Result<()> {
            Err(io::ErrorKind::BrokenPipe.into())
        }
    }
    for text in [
        "fn main()->u64 { return 42; }",
        include_str!("../spec/cases/verify/uaf.nera"),
    ] {
        let preview = verify_source(&source(text), Default::default());
        for mode in [TextReportMode::Summary, TextReportMode::Explain] {
            for flush in [false, true] {
                assert!(
                    write_report(
                        &preview,
                        mode,
                        &mut Broken {
                            remaining: 32,
                            flush
                        }
                    )
                    .is_err()
                );
            }
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
fn successful_run_and_native_build_cannot_promote_a_whole_function_verdict() {
    let fixture = cli_process::Fixture::new();
    // The entry chooses the safe branch; another branch returns uninitialized storage.
    let path = fixture.file("favorable.nera", summary_cases::source(6, 0));
    let before = cli_process::run(fixture.command().arg("verify").arg(&path));
    assert_eq!(before.status.code(), Some(1));
    let executed = cli_process::run(fixture.command().arg("run").arg(&path));
    assert_eq!(executed.status.code(), Some(0));
    assert!(String::from_utf8_lossy(&executed.stdout).contains("status: executed (unverified)"));
    assert!(String::from_utf8_lossy(&executed.stdout).contains("return: 42"));
    let artifact = fixture.0.join("favorable-native");
    let built = cli_process::run(
        fixture
            .command()
            .args(["build", "--emit", "exe"])
            .arg(&path)
            .arg("-o")
            .arg(&artifact),
    );
    assert_eq!(built.status.code(), Some(0), "{built:?}");
    assert!(String::from_utf8_lossy(&built.stdout).contains("unverified"));
    assert!(artifact.is_file());
    // Do not run unverified native code: successful code generation is not verification.
    let after = cli_process::run(fixture.command().arg("verify").arg(&path));
    assert_eq!(after.status.code(), Some(1));
    assert_eq!(before.stdout, after.stdout);
}
