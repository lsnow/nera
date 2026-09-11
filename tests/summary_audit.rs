use nera::verifier::relation::audit::RelationReplayCache;
use nera::verifier::summary::{audit::*, *};
use nera::*;
#[path = "support/preview_checks.rs"]
mod preview_checks;
#[path = "../src/bin/fuzz_support/summary_cases.rs"]
mod summary_cases;
#[path = "support/summary_scale.rs"]
mod summary_scale;
use nera::verification::{verify_source, verify_unit};
#[path = "support/cli_process.rs"]
mod cli_process;

fn unit(source: &str) -> ValidatedVirUnit {
    let output = analyze(&SourceFile::from_text("summary-audit.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    output.vir().unwrap().clone()
}
const SOURCE: &str = include_str!("../spec/cases/verify/summary-recursive.nera");

#[test]
fn complete_audit_links_calls_worlds_body_findings_and_existing_memory_traces() {
    for source in [
        SOURCE,
        include_str!("../spec/cases/verify/summary-conditional.nera"),
        include_str!("../spec/cases/verify/summary-borrows.nera"),
        include_str!("../spec/cases/verify/summary-conditional-payload.nera"),
    ] {
        let input = unit(source);
        let resolved = input.resolve().unwrap();
        let report = verify_program(&resolved, Default::default()).unwrap();
        assert!(
            report.is_memory_checked_core0(),
            "{:?}",
            report.diagnostics()
        );
        let audit = SummaryAudit::from_report(&report);
        let cache = RelationReplayCache::new(&resolved, Default::default()).unwrap();
        assert!(cache.accepts_summary_audit(&audit));
        assert_eq!(
            audit.stable_dump(),
            SummaryAudit::from_report(&verify_program(&resolved, Default::default()).unwrap())
                .stable_dump()
        );
        let mut calls = 0;
        for f in &audit.functions {
            assert!(cache.accepts_memory_trace(
                f.function,
                &f.provenance,
                &f.queries,
                &f.relations
            ));
            assert_eq!(f.requirements.len(), f.summary.faults.requirements.len());
            assert!(
                f.metrics.summary_evidence_weight
                    <= CfgAnalysisConfig::default().max_summary_evidence
            );
            for c in &f.summary.call_uses {
                calls += 1;
                let observation = &c.observation;
                assert_eq!(observation.finding.unwrap().site().function(), f.function);
                let target = resolved
                    .runtime()
                    .functions
                    .iter()
                    .find(|t| t.name == c.symbol)
                    .unwrap();
                let callee = &report.functions()[&target.id];
                assert_eq!(
                    observation.dependency.as_ref(),
                    Some(&callee.summary().binding)
                );
                assert!(!observation.worlds.is_empty());
                assert!(matches!(
                    c.outcome,
                    CallSummaryOutcome::Applied | CallSummaryOutcome::Inductive
                ));
                for w in &observation.worlds {
                    // Inductive calls reference candidate worlds, not the final
                    // projected body's ordinal namespace. Replay binds both.
                    if c.outcome == CallSummaryOutcome::Applied {
                        assert!(w.return_evidence < callee.cfg().returns().len());
                    } else {
                        let candidate = callee
                            .summary()
                            .recursion
                            .as_ref()
                            .unwrap()
                            .final_candidates
                            .iter()
                            .find(|c| c.function == target.id)
                            .unwrap();
                        assert!(
                            matches!(&candidate.normal_returns,Knowledge::Known(a) if a.iter().flat_map(|a| &a.worlds).any(|x| x.return_evidence==w.return_evidence && x.effects==w.effects))
                        );
                    }
                    for mapping in &w.resources {
                        if matches!(mapping.formal, ResourceName::Fresh(_)) {
                            assert!(
                                matches!(mapping.allocation, AbstractAllocationId::SummaryInstance { call_site, .. } if call_site==observation.instance_site)
                            );
                        }
                    }
                }
            }
        }
        assert!(calls > 0);
        interpret(resolved.runtime()).unwrap();
    }
}

#[test]
fn deleted_effect_forged_guard_resource_and_closure_are_rejected_by_actual_replay() {
    let input = unit(SOURCE);
    let resolved = input.resolve().unwrap();
    let preview = verify_unit(input.as_unit().clone(), Default::default());
    preview_checks::observe(&preview);
    let original = SummaryAudit::from_report(preview.verification().unwrap());
    let cache = RelationReplayCache::new(&resolved, Default::default()).unwrap();
    for mutation in 0..15 {
        let mut bad = original.clone();
        match mutation {
            0 => {
                bad.functions.pop();
            }
            1 => {
                bad.functions[0].summary.call_uses.clear();
            }
            2 => {
                bad.functions[0].requirements.clear();
            }
            3 => {
                bad.functions[0].metrics.summary_bytes += 1;
            }
            4 => {
                bad.functions[0].summary.effects.may_write = Knowledge::Unknown;
            }
            5 => {
                bad.functions
                    .iter_mut()
                    .find(|f| f.summary.recursion.is_some())
                    .unwrap()
                    .summary
                    .recursion
                    .as_mut()
                    .unwrap()
                    .final_recheck = false;
            }
            6 => {
                bad.functions[0].summary.dependencies.clear();
            }
            7 => {
                bad.functions[0].summary.call_uses[0].observation.guard =
                    PathCondition::unreachable();
            }
            8 => {
                bad.functions[0].summary.call_uses[0].observation.dependency = None;
            }
            9 => {
                bad.functions[0].summary.call_uses[0].observation.worlds[0]
                    .effects
                    .may_free = Knowledge::Unknown;
            }
            10 => {
                bad.functions
                    .iter_mut()
                    .flat_map(|f| &mut f.summary.call_uses)
                    .flat_map(|c| &mut c.observation.worlds)
                    .flat_map(|w| &mut w.resources)
                    .next()
                    .unwrap()
                    .allocation = AbstractAllocationId::SummaryInstance {
                    call_site: u64::MAX,
                    resource: 0,
                };
            }
            11 => {
                bad.functions[0].summary.call_uses[0]
                    .observation
                    .instance_site += 1;
            }
            12 => {
                let effects = bad
                    .functions
                    .iter_mut()
                    .flat_map(|f| &mut f.summary.call_uses)
                    .flat_map(|c| &mut c.observation.worlds)
                    .find_map(|w| match &mut w.effects.may_write {
                        Knowledge::Known(v) if !v.is_empty() => Some(v),
                        _ => None,
                    })
                    .unwrap();
                effects.clear();
            }
            13 => {
                bad.functions
                    .iter_mut()
                    .find(|f| f.summary.recursion.is_some())
                    .unwrap()
                    .summary
                    .recursion
                    .as_mut()
                    .unwrap()
                    .final_candidates = std::sync::Arc::from([]);
            }
            _ => {
                bad.memory_checked = false;
            }
        }
        assert_ne!(bad, original, "mutation {mutation} must change evidence");
        assert!(!cache.accepts_summary_audit(&bad), "mutation {mutation}");
    }
    preview_checks::observe(&preview);
}

#[test]
fn body_interface_configuration_and_transitive_dependency_changes_invalidate_audit() {
    let source = "fn main()->u64 { return outer(); } fn outer()->u64 { return inner(); } fn inner()->u64 { return 42; }";
    let input = unit(source);
    let resolved = input.resolve().unwrap();
    let audit = SummaryAudit::from_report(&verify_program(&resolved, Default::default()).unwrap());
    for changed in [
        source.replace("42", "21"),
        source
            .replace("inner()", "inner(0)")
            .replace("fn inner(0)", "fn inner(n:u64)"),
    ] {
        let other = unit(&changed);
        let r = other.resolve().unwrap();
        assert!(
            !RelationReplayCache::new(&r, Default::default())
                .unwrap()
                .accepts_summary_audit(&audit)
        );
    }
    let config = CfgAnalysisConfig {
        max_summary_evidence: 32,
        ..Default::default()
    };
    assert!(
        !RelationReplayCache::new(&resolved, config)
            .unwrap()
            .accepts_summary_audit(&audit)
    );
}

#[test]
fn separate_calls_to_one_callee_and_evidence_budget_are_not_silently_coalesced() {
    let input = unit("fn main()->u64 { return value()+value(); } fn value()->u64 { return 21; }");
    let resolved = input.resolve().unwrap();
    let report = verify_program(&resolved, Default::default()).unwrap();
    let calls = &report.functions()[&VirFunctionId::new(0)]
        .summary()
        .call_uses;
    assert_eq!(calls.len(), 2);
    assert_ne!(calls[0].observation.finding, calls[1].observation.finding);
    for limit in [0, 1] {
        let report = verify_program(
            &resolved,
            CfgAnalysisConfig {
                max_summary_evidence: limit,
                ..Default::default()
            },
        )
        .unwrap();
        let audit = SummaryAudit::from_report(&report);
        assert!(
            audit.functions[0]
                .issues
                .contains(&SummaryIssue::EvidenceBudget)
        );
        assert_ne!(audit.functions[0].summary.state, SummaryState::Closed);
    }
    for (source, config, expected) in [
        (
            "fn main()->u64 { bad(); return 42; } fn bad() { let p=alloc<u64>(1); let v=*p; free(p); return; }",
            CfgAnalysisConfig::default(),
            SummaryIssue::BodyObligation,
        ),
        (
            "fn main()->u64 { let mut x=42; let p=&mut x; write(p,p); return x; } fn write(a:&mut u64,b:&mut u64) { *a=20; *b=22; return; }",
            CfgAnalysisConfig::default(),
            SummaryIssue::CallPrecondition,
        ),
        (
            include_str!("../spec/cases/verify/summary-conditional.nera"),
            CfgAnalysisConfig {
                max_guarded_cases_per_block: 1,
                ..Default::default()
            },
            SummaryIssue::Guard,
        ),
        (
            SOURCE,
            CfgAnalysisConfig {
                summary_limits: SccLimits {
                    max_iterations: 0,
                    ..Default::default()
                },
                ..Default::default()
            },
            SummaryIssue::RecursiveNotClosed,
        ),
    ] {
        let input = unit(source);
        let resolved = input.resolve().unwrap();
        let audit = SummaryAudit::from_report(&verify_program(&resolved, config).unwrap());
        assert!(
            audit.functions.iter().any(|f| f.issues.contains(&expected)),
            "missing {expected:?}"
        );
    }
}

#[test]
fn generated_compositions_pin_verdicts_and_concretize_both_guards() {
    let fixture = cli_process::Fixture::new();
    for family in 0..summary_cases::FAMILY_COUNT {
        for entropy in 0..4 {
            let path = fixture.file(
                format!("generated-{family}-{entropy}.nera"),
                summary_cases::source(family, entropy),
            );
            let source = SourceFile::load(&path).unwrap();
            let preview = verify_source(&source, Default::default());
            preview_checks::observe(&preview);
            for mode in [
                nera::verification::TextReportMode::Summary,
                nera::verification::TextReportMode::Explain,
            ] {
                let mut command = fixture.command();
                command.arg("verify");
                if mode == nera::verification::TextReportMode::Explain {
                    command.arg("--explain");
                }
                let output = cli_process::run(command.arg(&path));
                assert_eq!(
                    output.status.code(),
                    Some(i32::from(!summary_cases::expected_checked(family)))
                );
                assert_eq!(
                    output.stdout,
                    nera::verification::render_text(&preview, mode).as_bytes()
                );
                assert!(output.stderr.is_empty());
            }
            let resolved = preview.validated_unit().unwrap().resolve().unwrap();
            let report = preview.verification().unwrap();
            assert_eq!(
                report.is_memory_checked_core0(),
                summary_cases::expected_checked(family),
                "family {family} entropy {entropy}: {:?}",
                report.diagnostics()
            );
            assert_eq!(preview, verify_source(&source, Default::default()));
            if summary_cases::expected_checked(family) {
                assert_eq!(
                    interpret(resolved.runtime()).unwrap().values(),
                    [VirRuntimeValue::U64(42)]
                );
            } else {
                for config in [
                    CfgAnalysisConfig {
                        max_summary_evidence: 0,
                        ..Default::default()
                    },
                    CfgAnalysisConfig {
                        summary_limits: SccLimits {
                            max_iterations: 0,
                            ..Default::default()
                        },
                        ..Default::default()
                    },
                ] {
                    let reduced = verify_source(&source, config);
                    assert!(!reduced.is_checked());
                    preview_checks::observe(&reduced);
                }
            }
        }
    }
}

#[test]
fn summary_scale_records_bounded_work_separately_from_measurements() {
    // Select dimension and size for process-isolated Linux VmHWM measurements.
    let selected = std::env::var("NERA_SUMMARY_SCALE").ok();
    let selected_size = std::env::var("NERA_SUMMARY_SCALE_SIZE")
        .ok()
        .map(|s| s.parse::<usize>().unwrap());
    for dimension in summary_scale::DIMENSIONS {
        if selected.as_deref().is_some_and(|s| s != dimension) {
            continue;
        }
        for size in summary_scale::SIZES {
            if selected_size.is_some_and(|s| s != size) {
                continue;
            }
            let source = summary_scale::source(dimension, size);
            let input = unit(&source);
            let resolved = input.resolve().unwrap();
            let start = std::time::Instant::now();
            let report = verify_program(&resolved, Default::default()).unwrap();
            let elapsed = start.elapsed();
            let audit = SummaryAudit::from_report(&report);
            assert!(
                report.is_memory_checked_core0(),
                "{dimension}/{size}: {:?}",
                report.diagnostics()
            );
            let visits: u64 = audit
                .functions
                .iter()
                .map(|f| f.metrics.cfg_visits + f.metrics.refinement_visits)
                .sum();
            let bytes: usize = audit
                .functions
                .iter()
                .map(|f| f.metrics.summary_bytes)
                .sum();
            let queries: usize = audit
                .functions
                .iter()
                .map(|f| f.metrics.relation_queries)
                .sum();
            let evidence: usize = audit
                .functions
                .iter()
                .map(|f| f.metrics.summary_evidence_weight)
                .sum();
            let worlds: usize = audit.functions.iter().map(|f| f.metrics.worlds).sum();
            let alternatives: usize = audit.functions.iter().map(|f| f.metrics.alternatives).sum();
            let closed = audit
                .functions
                .iter()
                .filter(|f| f.summary.state == SummaryState::Closed)
                .count();
            if closed != audit.functions.len() {
                eprintln!(
                    "summary-scale precision dimension={dimension} size={size}: {:?}",
                    audit
                        .functions
                        .iter()
                        .map(|f| (&f.summary.state, &f.issues, &f.guarded_precision_losses))
                        .collect::<Vec<_>>()
                );
            }
            let scc = audit
                .functions
                .iter()
                .find_map(|f| f.summary.recursion.as_ref());
            assert!(visits <= report.functions().len() as u64 * 12_000);
            if let Some(scc) = scc {
                assert!(scc.body_analyses <= 1024);
                assert!(scc.peak_worlds <= 32);
            }
            let scc_work = scc.map(|s| {
                (
                    s.body_analyses,
                    s.baseline_block_visits,
                    s.body_block_visits,
                    s.body_queries,
                    s.body_call_evidence,
                    s.peak_worlds,
                    s.peak_candidate_bytes,
                )
            });
            let peak_rss_kib = std::fs::read_to_string("/proc/self/status")
                .ok()
                .and_then(|s| {
                    s.lines()
                        .find(|l| l.starts_with("VmHWM:"))
                        .and_then(|l| l.split_whitespace().nth(1))
                        .and_then(|v| v.parse::<usize>().ok())
                });
            eprintln!(
                "summary-scale dimension={dimension} size={size} functions={} closed={closed} final_visits={visits} alternatives={alternatives} worlds={worlds} bytes={bytes} queries={queries} evidence={evidence} elapsed_us={} peak_rss_kib={peak_rss_kib:?} scc_work={scc_work:?}",
                report.functions().len(),
                elapsed.as_micros()
            );
        }
    }
}
