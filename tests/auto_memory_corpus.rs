#[path = "support/auto_memory_cases.rs"]
mod cases;

use nera::verification::{PreviewOutcome, verify_source};
use nera::verifier::summary::{CallSummaryOutcome, SummaryState};
use nera::{FrontendStatus, ObligationStatus, SourceFile, VirRuntimeValue, interpret};
#[path = "support/cli_process.rs"]
mod cli_process;
use cli_process::{Fixture, run};
use nera::verification::{TextReportMode, VerificationPreview, render_text};

fn check_cli(fixture: &Fixture, preview: &VerificationPreview, code: i32) {
    for mode in [TextReportMode::Summary, TextReportMode::Explain] {
        let mut command = fixture.command();
        command.arg("verify");
        if mode == TextReportMode::Explain {
            command.arg("--explain");
        }
        let output = run(command.arg(preview.source().unwrap().path()));
        assert_eq!(output.status.code(), Some(code), "{output:?}");
        assert_eq!(output.stdout, render_text(preview, mode).as_bytes());
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn ordinary_sources_and_mutations_follow_one_manifest() {
    let fixture = Fixture::new();
    for case in cases::cases() {
        let path = fixture.file(format!("{}-{}.nera", case.name, case.branch), &case.source);
        let input = SourceFile::load(&path).unwrap();
        // Token spelling excludes comments and whitespace; ordinary guards are allowed.
        for token in nera::lex(&input).tokens() {
            let span = token.span();
            assert!(
                ![
                    "requires",
                    "ensures",
                    "proof",
                    "assume",
                    "trusted",
                    "ghost",
                    "invariant",
                    "decreases",
                    "reads",
                    "writes",
                    "assert",
                    "theorem"
                ]
                .iter()
                .any(|word| word.as_bytes() == &input.bytes()[span.start()..span.end()]),
                "{} contains explicit proof input",
                case.path
            );
        }
        let preview = verify_source(&input, Default::default());
        assert_eq!(
            preview.frontend_status(),
            Some(FrontendStatus::AcceptedProposal),
            "{} {}: {:?}",
            case.name,
            case.branch,
            preview.frontend_issues()
        );
        assert!(preview.is_resolved());
        assert_eq!(
            preview.outcome(),
            PreviewOutcome::Checked,
            "{} {}: {:?}",
            case.name,
            case.branch,
            preview.diagnostics()
        );
        assert!(preview.trust_report().unwrap().entries().is_empty());
        check_cli(&fixture, &preview, 0);
        let unit = preview.validated_unit().unwrap();
        for &(caller, callee) in case.applied {
            let id = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == caller)
                .unwrap()
                .id;
            let callee_id = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == callee)
                .unwrap()
                .id;
            let functions = preview.verification().unwrap().functions();
            assert_eq!(functions[&callee_id].summary().state, SummaryState::Closed);
            assert!(
                functions[&id]
                    .summary()
                    .call_uses
                    .iter()
                    .any(|c| c.symbol == callee && c.outcome == CallSummaryOutcome::Applied),
                "{}: {caller}->{callee}",
                case.name
            );
        }
        if let Some(name) = case.recursive {
            let id = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == name)
                .unwrap()
                .id;
            let scc = preview.verification().unwrap().functions()[&id]
                .summary()
                .recursion
                .as_ref()
                .unwrap();
            assert!(scc.final_recheck);
        }
        if let Some((caller, callee)) = case.skeleton {
            let functions = preview.verification().unwrap().functions();
            let id = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == caller)
                .unwrap()
                .id;
            let callee_id = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == callee)
                .unwrap()
                .id;
            assert!(matches!(
                functions[&callee_id].summary().state,
                SummaryState::Unknown(_)
            ));
            assert!(
                functions[&id]
                    .summary()
                    .call_uses
                    .iter()
                    .any(|c| c.symbol == callee && c.outcome == CallSummaryOutcome::NotClosed)
            );
            assert!(
                !functions[&callee_id]
                    .summary()
                    .recursion
                    .as_ref()
                    .unwrap()
                    .final_recheck
            );
        }
        assert_eq!(
            interpret(unit.resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(case.value)]
        );
        for mutation in case.mutations {
            let text = cases::replace_once(&case.source, mutation.from, mutation.to);
            let path = fixture.file(
                format!("{}-{}-{}.nera", case.name, case.branch, mutation.name),
                &text,
            );
            let input = SourceFile::load(path).unwrap();
            let bad = verify_source(&input, Default::default());
            assert_eq!(
                bad.frontend_status(),
                Some(FrontendStatus::AcceptedProposal),
                "{} {}: {:?}",
                case.name,
                mutation.name,
                bad.frontend_issues()
            );
            assert!(bad.is_resolved());
            assert_eq!(
                bad.outcome(),
                PreviewOutcome::Unproved,
                "{} {}: {:?}",
                case.name,
                mutation.name,
                bad.failure()
            );
            check_cli(&fixture, &bad, 1);
            assert!(
                bad.verification()
                    .unwrap()
                    .functions()
                    .values()
                    .flat_map(|f| f.cfg().obligations())
                    .any(|o| mutation.fault.matches(o.obligation().kind())
                        && o.obligation().status() != ObligationStatus::Proven),
                "{} {} wrong failure: {:?}",
                case.name,
                mutation.name,
                bad.diagnostics()
            );
            let executed = interpret(bad.validated_unit().unwrap().resolve().unwrap().runtime());
            if let Some(value) = mutation.execution[case.branch] {
                assert_eq!(
                    executed.unwrap().values(),
                    [VirRuntimeValue::U64(value)],
                    "{} {} favorable execution",
                    case.name,
                    mutation.name
                );
            } else {
                let error = executed.expect_err("mutated concrete path must fault");
                assert!(
                    mutation.fault.matches_execution(error.kind()),
                    "{} {} wrong runtime fault: {:?}",
                    case.name,
                    mutation.name,
                    error.kind()
                );
            }
        }
    }
}

#[test]
fn removing_generated_cleanup_is_a_vir_error_not_a_source_contract_requirement() {
    let case = cases::cases()
        .into_iter()
        .find(|c| c.name == "conditional-owner-provenance" && c.branch == 0)
        .unwrap();
    let preview = verify_source(
        &SourceFile::from_text(case.path, &case.source),
        Default::default(),
    );
    assert!(preview.is_checked());
    let mut unit = preview.validated_unit().unwrap().as_unit().clone();
    let mut removed = 0;
    for function in &mut unit.runtime.functions {
        if function.name != "run" {
            continue;
        }
        for block in &mut function.blocks {
            block.instructions.retain(|i| {
                let drop = matches!(i.instruction, nera::VirInstruction::DropOwn { .. });
                removed += usize::from(drop);
                !drop
            });
        }
    }
    assert!(removed > 0);
    unit.rebuild_source_map_from_runtime(case.path, case.source.len());
    let validated = unit
        .into_validated()
        .expect("cleanup omission remains structurally valid");
    let report = nera::verify_program(&validated.resolve().unwrap(), Default::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| matches!(
                o.obligation().kind(),
                nera::ResourceObligationKind::OwnershipConserved { .. }
            ) && o.obligation().status() == ObligationStatus::Refuted)
    );
}
