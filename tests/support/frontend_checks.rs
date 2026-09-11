//! Common positive-case assertions. Negative cases keep their own boundary-
//! specific checks; this helper does not accept an arbitrary error as evidence.
use nera::{
    CfgAnalysisConfig, FrontendOutput, FrontendStatus, SourceFile, VirRuntimeValue, analyze,
    interpret, verify_program,
};

pub fn accepted(name: &str, source: &str) -> FrontendOutput {
    let file = SourceFile::from_text(name, source);
    let output = analyze(&file);
    assert_eq!(output, analyze(&file), "{name}: frontend replay");
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{name}\n{source}\n{:#?}",
        output.issues()
    );
    output
}

pub fn checked(name: &str, source: &str, expected: u64) {
    let output = accepted(name, source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        verification.is_memory_checked_core0(),
        "{name}\n{source}\n{:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(expected)],
        "{name}: interpreter result"
    );
    // Codegen includes planning. Native process/ledger tests remain separate.
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .unwrap();
}
