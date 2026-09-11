//! Observations across the one lowering/verifier path. Optional capture/compare
//! directories support byte-for-byte before/after refactor checks, not proof caches.
use std::fmt::Write as _;
use std::io::Write as _;

use nera::{CfgAnalysisConfig, FrontendStatus, SourceFile, analyze, interpret, verify_program};

const CASES: &[(&str, &str, bool)] = &[
    (
        "summary",
        include_str!("../spec/cases/verify/summary-baseline.nera"),
        true,
    ),
    (
        "owner-abi",
        include_str!("../spec/cases/aggregate/owning-abi.nera"),
        true,
    ),
    (
        "borrow-calls",
        include_str!("../spec/cases/verify/borrow-calls.nera"),
        true,
    ),
    (
        "provenance",
        include_str!("../spec/cases/verify/provenance-flow.nera"),
        true,
    ),
    (
        "refill",
        include_str!("../spec/cases/verify/partial-refill.nera"),
        true,
    ),
    (
        "nll",
        include_str!("../spec/cases/verify/local-nll.nera"),
        true,
    ),
    (
        "unknown",
        "fn main()->u64 { let a=[42]; return a[index()]; } fn index()->usize { return 0usize; }",
        true,
    ),
    (
        "fault",
        "fn main()->u64 { bad(); return 42; } fn bad() { let p=alloc<u64>(1); let x=*p; free(p); return; }",
        false,
    ),
];

fn observe(name: &str, source: &str, checked: bool) -> String {
    let output = analyze(&SourceFile::from_text(name, source));
    assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
    let unit = output.vir().unwrap();
    let resolved = unit.resolve().unwrap();
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert_eq!(report.is_memory_checked_core0(), checked, "{name}");
    // The full report includes source-backed findings, guarded instruction states,
    // relation observations/queries and provenance evidence, including their order.
    // Canonical VIR contains the materialized cleanup and NLL end plan.
    let mut result = format!("{output:?}\n{}\n{report:?}\n", unit.stable_dump());
    let bounded = verify_program(
        &resolved,
        CfgAnalysisConfig {
            max_guarded_cases_per_block: 1,
            max_guard_atoms_per_case: 0,
            ..Default::default()
        },
    );
    writeln!(result, "bounded: {bounded:?}").unwrap();
    let execution = interpret(resolved.runtime());
    writeln!(result, "execution (not a proof): {execution:?}").unwrap();
    if checked {
        assert!(execution.is_ok());
        let assembly = nera::backend::X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(resolved.runtime())
            .unwrap();
        writeln!(result, "assembly: {assembly:?}").unwrap();
    }
    result
}

#[test]
fn summary_seams_preserve_deterministic_full_observations() {
    let capture = std::env::var_os("NERA_REFACTOR_CAPTURE_DIR");
    let compare = std::env::var_os("NERA_REFACTOR_COMPARE_DIR");
    assert!(
        capture.is_none() || compare.is_none(),
        "capture and compare are exclusive"
    );
    for &(name, source, checked) in CASES {
        let observation = observe(name, source, checked);
        assert_eq!(
            observation,
            observe(name, source, checked),
            "{name}: deterministic replay"
        );
        if let Some(directory) = &capture {
            let path = std::path::Path::new(directory).join(format!("{name}.txt"));
            // Never overwrite a reference, even if capture is requested twice.
            std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(path)
                .unwrap()
                .write_all(observation.as_bytes())
                .unwrap();
        }
        if let Some(directory) = &compare {
            let path = std::path::Path::new(directory).join(format!("{name}.txt"));
            let reference = std::fs::read(path).unwrap();
            // Do not dump megabytes of resource states on mismatch.
            assert!(
                reference == observation.as_bytes(),
                "{name}: before/after observation changed"
            );
        }
    }
}

#[test]
fn transfer_public_facade_preserves_result_and_error_types() {
    use nera::verifier as transfer;
    // These aliases must remain the very same types, not conversion wrappers.
    let _: fn(transfer::InstructionTransfer) -> nera::InstructionTransfer = |v| v;
    let _: fn(transfer::InstructionSequenceTransfer) -> nera::InstructionSequenceTransfer = |v| v;
    let _: fn(transfer::ResourceObligation) -> nera::ResourceObligation = |v| v;
    let _: fn(transfer::ObligationStatus) -> nera::ObligationStatus = |v| v;
    let _: fn(transfer::TransferError) -> nera::TransferError = |v| v;
}
