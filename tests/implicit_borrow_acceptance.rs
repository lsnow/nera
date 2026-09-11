use std::time::{Duration, Instant};

use nera::verification::{PreviewOutcome, TextReportMode, render_text, verify_source};
use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, TokenKind, VirRuntimeValue, interpret, lex,
};

#[path = "support/cli_process.rs"]
mod cli_process;

const PROGRAM: &str = include_str!("../spec/cases/verify/implicit-borrow-acceptance.nera");

fn source(name: &str, text: &str) -> SourceFile {
    SourceFile::from_text(name, text)
}

#[test]
fn natural_program_combines_owners_stored_borrows_generics_branches_and_nll() {
    let input = source("implicit-borrow-acceptance.nera", PROGRAM);
    let lexed = lex(&input);
    assert!(lexed.issues().is_empty());
    assert!(
        lexed
            .tokens()
            .iter()
            .all(|token| token.kind() != TokenKind::Lifetime)
    );
    for token in lexed.tokens() {
        let raw = token.raw(&input);
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
            ]
            .iter()
            .any(|word| raw == word.as_bytes()),
            "ordinary acceptance source contains explicit contract token"
        );
    }

    let started = Instant::now();
    let preview = verify_source(&input, Default::default());
    assert!(started.elapsed() < Duration::from_secs(30));
    assert_eq!(
        preview.frontend_status(),
        Some(FrontendStatus::AcceptedProposal)
    );
    assert_eq!(preview.outcome(), PreviewOutcome::Checked, "{preview:#?}");
    assert!(preview.trust_report().unwrap().entries().is_empty());
    assert_eq!(preview, verify_source(&input, Default::default()));

    let counts = preview.counts().unwrap();
    assert_eq!(counts.functions, 4);
    assert_eq!(counts.borrow_interfaces, 3);
    assert_eq!(counts.borrow_worlds, 4);
    assert!(counts.total() > 0);
    assert_eq!(counts.summaries_closed, counts.functions);
    let explain = render_text(&preview, TextReportMode::Explain);
    assert!(explain.contains("borrow interfaces below are derived from source function bodies"));
    assert!(explain.contains("`right` when always"));
    assert!(explain.contains("`choose` when parameter #0 == true"));

    let program = preview.validated_unit().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(program.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(program.runtime())
        .unwrap();
}

#[test]
fn real_cli_frontend_verify_run_and_native_build_agree() {
    let fixture = cli_process::Fixture::new();
    let path = fixture.file("acceptance.nera", PROGRAM);
    for command in ["frontend", "verify", "run"] {
        let output = cli_process::run(fixture.command().arg(command).arg(&path));
        assert!(output.status.success(), "{command}: {output:?}");
        if command == "run" {
            assert!(String::from_utf8_lossy(&output.stdout).contains("42"));
        }
    }
    if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        let output = cli_process::run(
            fixture
                .command()
                .arg("build")
                .arg(&path)
                .args(["--emit", "exe", "-o", "native"]),
        );
        assert!(output.status.success(), "{output:?}");
        assert_eq!(
            std::process::Command::new(fixture.0.join("native"))
                .status()
                .unwrap()
                .code(),
            Some(42)
        );
    }
}

#[test]
fn failures_distinguish_invalidated_returned_borrow_from_unknown_bounds() {
    let uaf = source(
        "returned-uaf.nera",
        "fn main()->u64{let p=alloc<u64>(1);*p=42;let r=id(&*p);free(p);return *r;} fn id(value:&u64)->&u64{return value;}",
    );
    let report = verify_source(&uaf, Default::default());
    assert_eq!(report.outcome(), PreviewOutcome::Unproved);
    let summary = render_text(&report, TextReportMode::Summary);
    let explain = render_text(&report, TextReportMode::Explain);
    assert!(
        summary.contains("allocation is live")
            || summary.contains("permission is available")
            || summary.contains("outstanding loans"),
        "{summary}"
    );
    assert!(explain.contains("`id` when always"));
    assert!(explain.contains("free(p)"));

    let unknown = verify_source(
        &source(
            "unknown-index.nera",
            "fn get(index:usize)->u64{let values=[42];return values[index];}",
        ),
        Default::default(),
    );
    assert_eq!(unknown.outcome(), PreviewOutcome::Unproved);
    let text = render_text(&unknown, TextReportMode::Summary);
    assert!(text.contains("Unknown"));
    assert!(!text.to_ascii_lowercase().contains("use after free"));
}

#[test]
fn mandatory_analysis_budget_failure_is_not_reported_as_a_proof() {
    let report = verify_source(
        &source("budget.nera", PROGRAM),
        CfgAnalysisConfig {
            max_block_visits: 0,
            ..Default::default()
        },
    );
    assert_eq!(report.outcome(), PreviewOutcome::BudgetAborted);
    assert!(!report.is_checked());
    assert!(report.counts().is_none());
}
