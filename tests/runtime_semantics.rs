use std::str::FromStr;

use nera::backend::X86_64LinuxTarget;
use nera::{
    CapabilityFailureKind, CfgAnalysisConfig, FrontendIssueKind, FrontendStatus, SourceFile,
    VIR_SYSTEM_SEMANTICS_V2, VirArithmeticSemantics, VirComparisonSemantics,
    VirDivergenceSemantics, VirFailureDisposition, VirPointerOffsetSemantics, VirProveSemantics,
    VirRuntimeValue, VirValidationErrorKind, analyze, interpret, verify_program,
};

#[test]
fn current_profile_freezes_supported_and_gated_runtime_semantics() {
    let profile = VIR_SYSTEM_SEMANTICS_V2;
    assert_eq!(profile.word_bits, 64);
    assert_eq!(profile.addition, VirArithmeticSemantics::Wrapping);
    assert_eq!(profile.subtraction, VirArithmeticSemantics::Unsupported);
    assert_eq!(profile.multiplication, VirArithmeticSemantics::Unsupported);
    assert_eq!(profile.division, VirArithmeticSemantics::Unsupported);
    assert_eq!(profile.remainder, VirArithmeticSemantics::Unsupported);
    assert_eq!(profile.shift_left, VirArithmeticSemantics::Unsupported);
    assert_eq!(profile.shift_right, VirArithmeticSemantics::Unsupported);
    assert_eq!(profile.division_by_zero, VirFailureDisposition::Abort);
    assert_eq!(profile.comparison, VirComparisonSemantics::Unsigned);
    assert_eq!(
        profile.pointer_offset,
        VirPointerOffsetSemantics::CheckedLiveDomain
    );
    assert_eq!(profile.allocation_failure, VirFailureDisposition::Abort);
    assert_eq!(profile.memory_fault, VirFailureDisposition::Abort);
    assert_eq!(profile.runtime_check_failure, VirFailureDisposition::Abort);
    assert_eq!(profile.abort, VirFailureDisposition::Abort);
    assert_eq!(profile.divergence, VirDivergenceSemantics::NoResult);
    assert_eq!(
        profile.prove,
        VirProveSemantics::GhostErasedAfterVerification
    );
}

#[test]
fn wrapping_word_add_is_shared_by_validated_interpreter_and_verifier() {
    let output = analyze(&SourceFile::from_text(
        "semantic-wrap.nera",
        "fn main() -> u64 { return 18446744073709551615 + 1; }",
    ));
    assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
    let vir = output.vir().expect("accepted output has VIR");
    assert_eq!(vir.runtime().semantic_profile, VIR_SYSTEM_SEMANTICS_V2);
    let resolved = vir.resolve().expect("semantic fixture resolves");
    let verification =
        verify_program(&resolved, CfgAnalysisConfig::default()).expect("semantic fixture verifies");
    assert!(verification.is_memory_checked_core0());
    assert_eq!(
        interpret(resolved.runtime())
            .expect("semantic fixture executes")
            .values(),
        [VirRuntimeValue::U64(0)]
    );
}

#[test]
fn semantic_profile_mutation_is_rejected_before_resolution() {
    let output = analyze(&SourceFile::from_text(
        "semantic-profile.nera",
        "fn main() -> u64 { return 0; }",
    ));
    let mut raw = output
        .vir()
        .expect("accepted output has VIR")
        .as_unit()
        .clone();
    raw.runtime.semantic_profile.word_bits = 32;
    let error = raw
        .into_validated()
        .expect_err("mutated semantics must not reach a consumer");
    assert!(matches!(
        error.kind(),
        VirValidationErrorKind::SemanticProfileMismatch { .. }
    ));
}

#[test]
fn unsupported_capabilities_remain_classified_at_their_own_boundary() {
    let frontend = analyze(&SourceFile::from_text(
        "runtime-unsupported.nera",
        "fn main() -> u64 { return 1.0; }",
    ));
    assert_eq!(frontend.status(), FrontendStatus::Unsupported);
    assert_eq!(frontend.issues()[0].kind(), FrontendIssueKind::Unsupported);
    assert_eq!(
        frontend.issues()[0].capability_failure_kind(),
        Some(CapabilityFailureKind::RuntimeSemanticsUnsupported)
    );

    let verification = nera::VerificationError::UnsupportedCapability("future-instruction");
    assert_eq!(
        verification.capability_failure_kind(),
        Some(CapabilityFailureKind::VerificationUnsupported)
    );

    let target = X86_64LinuxTarget::from_str("aarch64-unknown-linux-gnu")
        .expect_err("foreign target is unsupported by the x86 backend");
    assert_eq!(
        target.capability_failure_kind(),
        CapabilityFailureKind::TargetUnsupported
    );
}
