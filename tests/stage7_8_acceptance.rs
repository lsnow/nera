use nera::session::CompilerSession;
use nera::source::{SourceDatabase, SourceInput};
use nera::verification::{TextReportMode, render_text};
use nera::{FrontendStatus, SourceFile, TokenKind, VirRuntimeValue, interpret, lex};

#[path = "support/cli_process.rs"]
mod cli_process;

const APP: &str = include_str!("../spec/cases/modules/stage7-acceptance-app.nera");
const VALUES: &str = include_str!("../spec/cases/modules/generic-values.nera");
const BORROW: &str = include_str!("../spec/cases/modules/generic-borrow.nera");
const OWNERSHIP: &str = include_str!("../spec/cases/modules/stage7-acceptance-ownership.nera");

fn session(files: &[(&str, &str)]) -> CompilerSession {
    let sources = files
        .iter()
        .map(|(name, text)| {
            SourceInput::new(*name, SourceFile::from_text(format!("{name}.nera"), text))
        })
        .collect();
    CompilerSession::modules(
        SourceDatabase::new(sources).unwrap(),
        Default::default(),
        "app::main",
    )
    .unwrap()
}

fn files() -> [(&'static str, &'static str); 4] {
    [
        ("app", APP),
        ("values", VALUES),
        ("borrow", BORROW),
        ("ownership", OWNERSHIP),
    ]
}

#[test]
fn module_generic_borrow_and_owner_path_closes_stage7() {
    for (name, text) in files() {
        let source = SourceFile::from_text(format!("{name}.nera"), text);
        let tokens = lex(&source);
        assert!(tokens.issues().is_empty(), "{name}: {:?}", tokens.issues());
        assert!(
            tokens
                .tokens()
                .iter()
                .all(|token| token.kind() != TokenKind::Lifetime),
            "{name} exposes a lifetime token"
        );
        for forbidden in [
            "requires",
            "ensures",
            "proof",
            "assume",
            "trusted",
            "ghost",
            "invariant",
            "decreases",
        ] {
            assert!(
                tokens
                    .tokens()
                    .iter()
                    .all(|token| token.raw(&source) != forbidden.as_bytes()),
                "{name} contains explicit contract token {forbidden}"
            );
        }
    }

    let compiler = session(&files());
    let analysis = compiler.analyze("app").unwrap();
    assert_eq!(
        analysis.frontend().status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        analysis.frontend().issues()
    );
    let reordered = session(&[
        ("ownership", OWNERSHIP),
        ("borrow", BORROW),
        ("values", VALUES),
        ("app", APP),
    ]);
    assert_eq!(analysis, reordered.analyze("app").unwrap());

    let artifact = analysis.interface_artifact().unwrap();
    assert!(artifact.matches_analysis(&analysis));
    for definition in [
        "values::repeat",
        "values::Buffer",
        "borrow::hold",
        "ownership::relay",
    ] {
        assert!(
            artifact
                .instances()
                .iter()
                .any(|instance| instance.definition == definition),
            "missing interface instance {definition}"
        );
    }

    let verification = compiler.verify("app").unwrap();
    assert!(
        verification.is_checked(),
        "{}",
        render_text(&verification, TextReportMode::Explain)
    );
    assert_eq!(verification, reordered.verify("app").unwrap());
    let resolved = analysis.frontend().vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        &[VirRuntimeValue::U64(42)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .unwrap();

    let fixture = cli_process::Fixture::new();
    fixture.file("app.nera", APP);
    fixture.file("values.nera", VALUES);
    fixture.file("borrow.nera", BORROW);
    fixture.file("ownership.nera", OWNERSHIP);
    let args = [
        "--module",
        "app=app.nera",
        "--module",
        "values=values.nera",
        "--module",
        "borrow=borrow.nera",
        "--module",
        "ownership=ownership.nera",
        "--entry",
        "app::main",
    ];
    for command in ["frontend", "verify", "run"] {
        let output = cli_process::run(fixture.command().arg(command).args(args));
        assert!(output.status.success(), "{command}: {output:?}");
        if command == "run" {
            assert!(String::from_utf8_lossy(&output.stdout).contains("42"));
        }
    }
    if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        let built = cli_process::run(
            fixture
                .command()
                .arg("build")
                .args(args)
                .args(["--emit", "exe", "-o", "native"]),
        );
        assert!(built.status.success(), "{built:?}");
        assert_eq!(
            std::process::Command::new(fixture.0.join("native"))
                .status()
                .unwrap()
                .code(),
            Some(42)
        );
    }
}
