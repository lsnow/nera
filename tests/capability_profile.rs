use nera::{
    CapabilityAxis, CapabilityProfile, CapabilityStatus, FrontendStatus, SourceFile,
    backend::X86_64_UNKNOWN_LINUX_GNU, current_capability_profile, interpret,
    verification::verify_source,
};

#[path = "support/cli_process.rs"]
mod cli_process;

const MANIFEST: &str = include_str!("../spec/capability-profile-v1.txt");
const BORROW_PROGRAM: &str = "fn main()->u64{let value=42;let r=id(&value);return *r;}\
     fn id(value:&u64)->&u64{return value;}";

#[test]
fn current_profile_is_closed_and_matches_the_compiler_schemas() {
    let profile = current_capability_profile().unwrap();
    assert_eq!(profile.profile(), "system-v1");
    assert_eq!(profile.language(), "0.3-draft");
    assert_eq!(profile.runtime(), "system-v2");
    assert_eq!(profile.hir_schema(), 12);
    assert_eq!(profile.vir_schema(), 18);
    assert_eq!(profile.verifier(), "automatic-memory-v1");
    assert_eq!(profile.interpreter(), "system-v2-interpreter-v1");
    assert_eq!(profile.target(), "x86_64-unknown-linux-gnu");
    assert_eq!(profile.backend(), "direct-x86_64-system-tools-v1");
    assert_eq!(profile.formal_checker(), "none");
    assert!(profile.feature("formal-core0").is_none());
    profile.check_implementation().unwrap();
}

#[test]
fn support_is_not_collapsed_across_consumers() {
    let profile = current_capability_profile().unwrap();
    let borrowed = profile.feature("borrowed-results").unwrap();
    assert_eq!(
        borrowed.status(CapabilityAxis::Surface),
        CapabilityStatus::Supported
    );
    assert_eq!(
        borrowed.status(CapabilityAxis::Verifier),
        CapabilityStatus::Supported
    );
    assert_eq!(
        borrowed.status(CapabilityAxis::Interpreter),
        CapabilityStatus::Supported
    );
    assert_eq!(
        borrowed.status(CapabilityAxis::Backend),
        CapabilityStatus::ErasedAfterValidation
    );
    assert_eq!(
        borrowed.status(CapabilityAxis::Formal),
        CapabilityStatus::Unsupported
    );

    let removed = profile.feature("named-lifetime-syntax").unwrap();
    assert_eq!(
        removed.status(CapabilityAxis::Surface),
        CapabilityStatus::RejectedWithDiagnostic
    );
    assert_eq!(
        removed.status(CapabilityAxis::Runtime),
        CapabilityStatus::NotApplicable
    );

    let library_only = profile.feature("returned-reference-aggregates").unwrap();
    assert_eq!(
        library_only.status(CapabilityAxis::Surface),
        CapabilityStatus::Unsupported
    );
    for axis in [CapabilityAxis::Hir, CapabilityAxis::Vir] {
        assert_eq!(library_only.status(axis), CapabilityStatus::SchemaOnly);
    }
    for axis in [
        CapabilityAxis::Runtime,
        CapabilityAxis::Verifier,
        CapabilityAxis::Interpreter,
        CapabilityAxis::Backend,
    ] {
        assert_eq!(library_only.status(axis), CapabilityStatus::Unsupported);
    }
}

#[test]
fn malformed_unknown_and_incompatible_profiles_fail_closed() {
    let unknown_status = MANIFEST.replacen("|supported|", "|guessed|", 1);
    assert!(CapabilityProfile::parse(&unknown_status).is_err());

    let unsorted = MANIFEST.replace("feature|borrowed-results|", "feature|zz-borrowed-results|");
    assert!(CapabilityProfile::parse(&unsorted).is_err());

    let incompatible = MANIFEST.replace("runtime|system-v2", "runtime|system-v3");
    let parsed = CapabilityProfile::parse(&incompatible).unwrap();
    assert!(parsed.check_implementation().is_err());

    let unknown_profile = MANIFEST.replace("profile|system-v1", "profile|custom-v1");
    let parsed = CapabilityProfile::parse(&unknown_profile).unwrap();
    assert!(parsed.check_implementation().is_err());
}

#[test]
fn registered_borrow_capability_matches_real_consumers() {
    let source = SourceFile::from_text("capability.nera", BORROW_PROGRAM);
    let frontend = nera::analyze(&source);
    assert_eq!(
        frontend.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        frontend.issues()
    );
    let preview = verify_source(&source, Default::default());
    assert!(preview.is_checked());
    assert!(
        nera::verification::render_text(&preview, nera::verification::TextReportMode::Summary)
            .contains("effective capability profile: system-v1")
    );
    let resolved = frontend.vir().unwrap().resolve().unwrap();
    let execution = interpret(resolved.runtime()).unwrap();
    assert_eq!(execution.values(), &[nera::VirRuntimeValue::U64(42)]);
    X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("registered native consumer accepts the same construct");
}

#[test]
fn real_cli_consumers_report_the_registered_profile() {
    let fixture = cli_process::Fixture::new();
    let source = fixture.file("capability.nera", BORROW_PROGRAM);
    for command in ["frontend", "run"] {
        let output = cli_process::run(fixture.command().arg(command).arg(&source));
        assert!(output.status.success(), "{command}: {output:?}");
        assert!(String::from_utf8_lossy(&output.stdout).contains("capability-profile: system-v1"));
    }
    let verify = cli_process::run(fixture.command().arg("verify").arg(&source));
    assert!(verify.status.success(), "{verify:?}");
    assert!(
        String::from_utf8_lossy(&verify.stdout).contains("effective capability profile: system-v1")
    );

    let assembly = fixture.0.join("capability.s");
    let build = cli_process::run(
        fixture
            .command()
            .arg("build")
            .args(["--emit", "asm"])
            .arg(&source)
            .arg("-o")
            .arg(&assembly),
    );
    assert!(build.status.success(), "{build:?}");
    assert!(String::from_utf8_lossy(&build.stdout).contains("capability-profile: system-v1"));
    assert!(assembly.is_file());
}
