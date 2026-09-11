use nera::session::{CompilerSession, SessionError, SessionRequest};
use nera::source::{SourceDatabase, SourceDatabaseError, SourceInput};
use nera::verification::{PreviewOutcome, TextReportMode, render_text, verify_source, verify_unit};
use nera::{
    ByteSpan, CfgAnalysisConfig, FrontendStatus, SourceFile, VirSourceId, VirSourceSpan, analyze,
};

#[path = "support/cli_process.rs"]
mod cli_process;

const SAFE: &str = "fn main()->u64 { return 42; }";
const UAF: &str = include_str!("../spec/cases/verify/uaf.nera");

fn entry(key: &str, path: &str, text: &str) -> SourceInput {
    SourceInput::new(key, SourceFile::from_text(path, text))
}
fn session(entries: Vec<SourceInput>) -> CompilerSession {
    CompilerSession::new(SourceDatabase::new(entries).unwrap(), Default::default()).unwrap()
}

#[test]
fn input_order_is_not_identity_and_source_selection_is_explicit() {
    let entries = vec![
        entry("z.nera", "display-z.nera", SAFE),
        entry("a.nera", "display-a.nera", "invalid other file"),
    ];
    let one = session(entries.clone());
    let two = session(entries.into_iter().rev().collect());
    assert_eq!(one, two);
    assert_eq!(one.sources().id("z.nera"), Some(VirSourceId::new(1)));
    assert_eq!(one.verify("z.nera").unwrap(), two.verify("z.nera").unwrap());
    let good = one.verify("z.nera").unwrap();
    assert!(good.is_checked());
    assert_eq!(good.counts().unwrap().functions, 1);
    let text = render_text(&good, TextReportMode::Summary);
    assert!(text.contains("2 files; analyzed source: \"z.nera\""));
    assert!(text.contains("other files not analyzed"));
    assert!(!one.verify("a.nera").unwrap().is_checked());
    assert!(matches!(
        one.verify("missing.nera"),
        Err(SessionError::UnknownSource(_))
    ));
}

#[test]
fn duplicate_keys_and_lexical_path_aliases_are_rejected_without_io() {
    assert_eq!(SourceDatabase::new(vec![]), Err(SourceDatabaseError::Empty));
    for key in [
        "",
        "/abs.nera",
        "a//b",
        "./a",
        "a/../b",
        "a\\b",
        "a\nb",
        "C:a",
    ] {
        assert!(
            matches!(
                SourceDatabase::new(vec![entry(key, "display.nera", SAFE)]),
                Err(SourceDatabaseError::InvalidLogicalName(_))
            ),
            "{key:?}"
        );
    }
    for text in [SAFE, UAF] {
        assert!(matches!(
            SourceDatabase::new(vec![entry("a", "a", SAFE), entry("a", "b", text)]),
            Err(SourceDatabaseError::DuplicateLogicalName(_))
        ));
        assert!(matches!(
            SourceDatabase::new(vec![
                entry("a", "dir/file", SAFE),
                entry("b", "dir/./file", text)
            ]),
            Err(SourceDatabaseError::DuplicateDisplayPath(_))
        ));
    }
    // '..' and symlinks are not resolved against the filesystem. Logical keys
    // remain authoritative, even if a loader supplied physically aliased paths.
    assert!(
        SourceDatabase::new(vec![
            entry("a", "dir/../file", SAFE),
            entry("b", "file", SAFE)
        ])
        .is_ok()
    );
    for alias in ["./dir/file", "dir//file", "dir/./file"] {
        assert!(matches!(
            SourceDatabase::new(vec![entry("a", "dir/file", SAFE), entry("b", alias, SAFE)]),
            Err(SourceDatabaseError::DuplicateDisplayPath(_))
        ));
    }
}

#[test]
fn local_hir_and_generated_vir_origins_map_to_the_selected_snapshot_source() {
    let code = include_str!("../spec/cases/verify/auto-memory-composition.nera");
    let compiler = session(vec![
        entry("a", "wrong.nera", UAF),
        entry("b", "correct.nera", code),
    ]);
    let output = compiler.analyze("b").unwrap();
    assert_eq!(output.frontend().status(), FrontendStatus::AcceptedProposal);
    let hir = output.frontend().hir().unwrap();
    let span = output.input().locate(hir.entry_function().span).unwrap();
    assert_eq!(span.source, VirSourceId::new(1));
    assert_eq!(
        output
            .input()
            .sources()
            .source(span.source)
            .unwrap()
            .bytes(),
        code.as_bytes()
    );
    let map = &output.frontend().vir().unwrap().as_unit().source_map;
    assert_eq!(map.sources().len(), 1);
    let mut generated = 0;
    for origin in map.origins() {
        if matches!(origin.kind, nera::VirOriginKind::Generated { .. }) {
            generated += 1;
        }
        let original = map.source_span_for_origin(origin.id).unwrap();
        assert_eq!(original.source, VirSourceId::new(0));
        let mapped = output.locate_vir_span(original).unwrap();
        assert_eq!(mapped.source, VirSourceId::new(1));
        assert_eq!(mapped.span, original.span);
    }
    assert!(generated > 0);
    assert!(
        output
            .locate_vir_span(VirSourceSpan {
                source: VirSourceId::new(1),
                span: ByteSpan::new(0, 1).unwrap()
            })
            .is_none()
    );
    assert!(
        output
            .input()
            .locate(ByteSpan::new(0, code.len() + 1).unwrap())
            .is_none()
    );
    assert!(
        compiler
            .sources()
            .locate(VirSourceId::new(99), ByteSpan::new(0, 0).unwrap())
            .is_none()
    );
}

#[test]
fn equal_offsets_in_different_files_keep_diagnostic_identity() {
    let compiler = session(vec![
        entry("a", "first.nera", "fn main()->u64 { return missing; }"),
        entry("b", "second.nera", "fn main()->u64 { return missing; }"),
    ]);
    let one = compiler.analyze("a").unwrap();
    let two = compiler.analyze("b").unwrap();
    let first = one.issues().next().unwrap().location.unwrap();
    let second = two.issues().next().unwrap().location.unwrap();
    assert_eq!(first.span, second.span);
    assert_ne!(first.source, second.source);
    for (key, yes, no) in [
        ("a", "first.nera", "second.nera"),
        ("b", "second.nera", "first.nera"),
    ] {
        let report = compiler.verify(key).unwrap();
        let text = render_text(&report, TextReportMode::Summary);
        assert!(text.contains(&format!("--> {yes}:")));
        assert!(!text.contains(no));
        assert!(!report.is_checked());
    }
    let invalid = session(vec![SourceInput::new(
        "bad",
        SourceFile::new("bad.nera", b"fn \xff".to_vec()),
    )]);
    let analysis = invalid.analyze("bad").unwrap();
    assert!(!analysis.frontend().issues().is_empty());
    assert!(analysis.issues().all(|i| i.location.is_some()));
}

#[test]
fn snapshot_and_result_survive_disk_rewrite_and_session_drop() {
    let fixture = cli_process::Fixture::new();
    let path = fixture.file("source.nera", UAF);
    let compiler = session(vec![SourceInput::new(
        "source",
        SourceFile::load(&path).unwrap(),
    )]);
    let report = compiler.verify("source").unwrap();
    assert_eq!(report.outcome(), PreviewOutcome::Unproved);
    let before = render_text(&report, TextReportMode::Explain);
    fixture.file("source.nera", SAFE);
    assert_eq!(
        before,
        render_text(&compiler.verify("source").unwrap(), TextReportMode::Explain)
    );
    let changed = session(vec![SourceInput::new(
        "source",
        SourceFile::load(path).unwrap(),
    )]);
    assert!(!report.matches_session(&changed, "source"));
    assert!(changed.verify("source").unwrap().is_checked());
    drop(compiler);
    drop(fixture);
    assert_eq!(before, render_text(&report, TextReportMode::Explain));
}

#[test]
fn full_snapshot_keys_paths_bytes_selection_and_budgets_bind_identity() {
    let entries = vec![entry("a", "a", SAFE), entry("b", "b", SAFE)];
    let compiler = session(entries.clone());
    let report = compiler.verify("a").unwrap();
    assert!(report.matches_session(&compiler, "a"));
    assert!(!report.matches_session(&compiler, "b"));
    for changed in [
        vec![entry("a", "a", SAFE), entry("b", "b", UAF)],
        vec![entry("a", "a", SAFE), entry("c", "b", SAFE)],
        vec![entry("a", "a", SAFE), entry("b", "renamed", SAFE)],
        vec![entry("a", "a", SAFE)],
    ] {
        assert!(!report.matches_session(&session(changed), "a"));
    }
    assert!(!report.matches_source(&SourceFile::from_text("a", SAFE), Default::default()));
    let config = CfgAnalysisConfig {
        max_block_visits: 0,
        ..Default::default()
    };
    let limited = CompilerSession::new(
        SourceDatabase::new(entries).unwrap(),
        SessionRequest {
            analysis: config,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(!report.matches_session(&limited, "a"));
    let aborted = limited.verify("a").unwrap();
    assert_eq!(aborted.config(), config);
    assert_eq!(aborted.outcome(), PreviewOutcome::BudgetAborted);
}

#[test]
fn requested_defaults_resolve_explicitly_and_unknown_profiles_do_not_fall_back() {
    let db = SourceDatabase::new(vec![entry("a", "a", SAFE)]).unwrap();
    let default = CompilerSession::new(db.clone(), Default::default()).unwrap();
    let config = default.effective();
    let request = SessionRequest {
        target: Some(config.target().into()),
        runtime: Some("system-v2".into()),
        verifier: Some(config.verifier().into()),
        ..Default::default()
    };
    let explicit = CompilerSession::new(db.clone(), request.clone()).unwrap();
    assert_eq!(explicit.requested(), &request);
    assert_eq!(explicit.effective(), default.effective());
    let report = default.verify("a").unwrap();
    assert!(report.matches_session(&explicit, "a"));
    assert_eq!(
        report.verification(),
        explicit.verify("a").unwrap().verification()
    );
    for (field, request) in [
        (
            "target",
            SessionRequest {
                target: Some("aarch64-unknown-linux-gnu".into()),
                ..Default::default()
            },
        ),
        (
            "runtime",
            SessionRequest {
                runtime: Some("system-v1".into()),
                ..Default::default()
            },
        ),
        (
            "verifier",
            SessionRequest {
                verifier: Some("trust-all".into()),
                ..Default::default()
            },
        ),
    ] {
        assert!(
            matches!(CompilerSession::new(db.clone(), request), Err(SessionError::UnsupportedConfiguration { field: found, .. }) if field == found)
        );
    }
}

#[test]
fn compatibility_entry_and_session_share_artifacts_verdicts_and_real_cli() {
    let fixture = cli_process::Fixture::new();
    for (text, expected) in [(SAFE, 0), (UAF, 1), ("fn main( {", 2)] {
        let path = fixture.file("main.nera", text);
        let source = SourceFile::load(&path).unwrap();
        let compiler = CompilerSession::single(source.clone(), Default::default());
        assert_eq!(
            &analyze(&source),
            compiler.analyze("input.nera").unwrap().frontend()
        );
        let direct = verify_source(&source, Default::default());
        let report = compiler.verify("input.nera").unwrap();
        assert_eq!(direct, report);
        for (args, mode) in [
            (vec!["verify"], TextReportMode::Summary),
            (vec!["verify", "--explain"], TextReportMode::Explain),
        ] {
            let output = cli_process::run(fixture.command().args(args).arg(&path));
            assert_eq!(output.status.code(), Some(expected));
            assert!(output.stderr.is_empty());
            assert_eq!(
                String::from_utf8(output.stdout).unwrap(),
                render_text(&report, mode)
            );
        }
    }
}

#[test]
fn raw_unit_cannot_acquire_a_source_snapshot_binding() {
    let source = SourceFile::from_text("pretend.nera", SAFE);
    let unit = analyze(&source).vir().unwrap().as_unit().clone();
    let position = unit
        .source_map
        .source_span_for_origin(unit.source_map.origins()[0].id)
        .unwrap();
    let raw = verify_unit(unit, Default::default());
    assert!(raw.source_input().is_none());
    assert!(raw.locate_vir_span(position).is_none());
    assert!(!raw.matches_source(&source, Default::default()));
    assert!(render_text(&raw, TextReportMode::Explain).contains("source text unavailable"));
}

#[test]
fn selected_nonzero_source_renders_findings_and_preserves_runtime_behavior() {
    let compiler = session(vec![
        entry("a", "wrong.nera", SAFE),
        entry("b", "failure.nera", UAF),
    ]);
    let report = compiler.verify("b").unwrap();
    assert_eq!(report.outcome(), PreviewOutcome::Unproved);
    let map = &report.validated_unit().unwrap().as_unit().source_map;
    for obligation in report.obligations().unwrap() {
        if let Some(span) = map.source_span_for_origin(obligation.finding().origin()) {
            assert_eq!(
                report.locate_vir_span(span).unwrap().source,
                VirSourceId::new(1)
            );
        }
    }
    for mode in [TextReportMode::Summary, TextReportMode::Explain] {
        let text = render_text(&report, mode);
        assert!(text.contains("--> failure.nera:"));
        assert!(!text.contains("wrong.nera"));
    }
    let selected = session(vec![
        entry("a", "unused.nera", "invalid"),
        entry("b", "safe.nera", SAFE),
    ]);
    let analysis = selected.analyze("b").unwrap();
    let resolved = analysis.frontend().vir().unwrap().resolve().unwrap();
    assert_eq!(
        nera::interpret(resolved.runtime()).unwrap().values(),
        [nera::VirRuntimeValue::U64(42)]
    );
    assert!(
        nera::backend::X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(resolved.runtime())
            .is_ok()
    );
}
