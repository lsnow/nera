#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, FrontendStatus, ObligationStatus, ResourceObligationKind, SourceFile,
    VirExecutionErrorKind, VirInstruction, VirValidationErrorKind, analyze, interpret,
    verify_program,
};

const BASELINE: &str = include_str!("../spec/cases/verify/provenance-baseline.nera");

#[test]
fn existing_byte_addresses_are_resource_neutral_and_do_not_read_the_pointee() {
    let output = frontend_checks::accepted("provenance-baseline.nera", BASELINE);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let verified = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(verified.is_memory_checked_core0());
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [nera::VirRuntimeValue::U64(42)]
    );
    assert_eq!(
        verified,
        verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
    );
    let offsets: Vec<_> = verified
        .functions()
        .values()
        .flat_map(|f| f.cfg().obligations())
        .filter(|r| {
            matches!(
                r.obligation().kind(),
                ResourceObligationKind::PointerOffsetWithinBounds { .. }
            )
        })
        .collect();
    assert_eq!(offsets.len(), 4);
    assert!(
        offsets
            .iter()
            .all(|r| r.obligation().status() == ObligationStatus::Proven)
    );
}

#[test]
fn formation_and_access_fail_at_distinct_boundaries() {
    // These sources must reach validated VIR. A frontend rejection would not
    // exercise either the verifier or the independent interpreter fault.
    for (name, body, fault) in [
        ("past-end", "let q = p + 9;", "offset"),
        ("one-past-read", "let q = p + 8; let x = *q;", "bounds"),
        ("misaligned-read", "let q = p + 1; let x = *q;", "alignment"),
        ("uninitialized-read", "let q = p + 0; let x = *q;", "init"),
        (
            "overflow",
            "let q = p + 8; let r = q + 18446744073709551615;",
            "overflow",
        ),
    ] {
        let source =
            format!("fn main() -> u64 {{ let p = alloc<u64>(1); {body} free(p); return 42; }}");
        let output = frontend_checks::accepted(name, &source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let verified = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(!verified.is_memory_checked_core0(), "{name}");
        assert!(
            verified
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .any(|r| {
                    r.obligation().status() == ObligationStatus::Refuted
                        && matches!(
                            (fault, r.obligation().kind()),
                            (
                                "offset",
                                ResourceObligationKind::PointerOffsetWithinBounds { .. }
                            ) | (
                                "overflow",
                                ResourceObligationKind::PointerOffsetNoOverflow { .. }
                            ) | ("bounds", ResourceObligationKind::AccessWithinBounds { .. })
                                | ("alignment", ResourceObligationKind::AccessAligned { .. })
                                | ("init", ResourceObligationKind::MemoryInitialized { .. })
                        )
                }),
            "{name}: {:#?}",
            verified.diagnostics()
        );
        let error = interpret(resolved.runtime()).unwrap_err();
        assert!(
            matches!(
                (fault, error.kind()),
                (
                    "offset" | "overflow",
                    VirExecutionErrorKind::PointerOffsetOutOfBounds { .. }
                ) | ("bounds", VirExecutionErrorKind::OutOfBoundsAccess { .. })
                    | ("alignment", VirExecutionErrorKind::MisalignedAccess { .. })
                    | ("init", VirExecutionErrorKind::UninitializedRead { .. })
            ),
            "{name}: {error:?}"
        );
    }
}

#[test]
fn deferred_pointer_operations_and_reference_recovery_remain_gated() {
    for (source, message) in [
        (
            "fn main() -> u64 { let x = 42; let p = &'a x; return x; }",
            "explicit lifetime annotations were removed",
        ),
        (
            "fn main() -> u64 { let x = 42; let p = &raw x; let r = &*p; return x; }",
            "10.1/10.3",
        ),
        (
            "fn main() -> u64 { let p = alloc<u64>(1); *p = 42; let q = p + 0; let r = &*q; return *r; }",
            "10.1/10.3",
        ),
    ] {
        let output = analyze(&SourceFile::from_text("raw-gate.nera", source));
        assert_eq!(
            output.status(),
            FrontendStatus::Unsupported,
            "{:#?}",
            output.issues()
        );
        assert!(output.vir().is_none());
        assert!(
            output
                .issues()
                .iter()
                .any(|i| i.diagnostic().message().contains(message))
        );
    }
    for (body, message) in [
        (
            "let delta = 8usize; let q = p + delta;",
            "pointer offset must be an unsuffixed integer literal",
        ),
        (
            "let q = p + 8usize;",
            "pointer offset must be an unsuffixed integer literal",
        ),
        (
            "let n = ptr_to_int(p);",
            "direct call target is not defined",
        ),
    ] {
        let source =
            format!("fn main() -> u64 {{ let p = alloc<u64>(2); {body} free(p); return 42; }}");
        let output = analyze(&SourceFile::from_text("pointer-gate.nera", &source));
        assert_eq!(
            output.status(),
            FrontendStatus::Invalid,
            "{body}: {:#?}",
            output.issues()
        );
        assert!(output.vir().is_none());
        assert!(
            output
                .issues()
                .iter()
                .any(|i| i.diagnostic().message().contains(message)),
            "{body}: {:#?}",
            output.issues()
        );
    }
}

#[test]
fn planned_distance_name_is_not_a_reserved_keyword() {
    frontend_checks::checked(
        "distance-name.nera",
        "fn main() -> u64 { return ptr_byte_distance(20, 22); }
        fn ptr_byte_distance(a: u64, b: u64) -> u64 { return a + b; }",
        42,
    );
}

#[test]
fn malformed_offset_operands_are_rejected_before_resource_analysis() {
    let output = frontend_checks::accepted("provenance-baseline.nera", BASELINE);
    let mut unit = output.vir().unwrap().as_unit().clone();
    let offset = unit.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .find(|i| matches!(i.instruction, VirInstruction::PointerOffset { .. }))
        .unwrap();
    let VirInstruction::PointerOffset {
        base, delta_bytes, ..
    } = &mut offset.instruction
    else {
        unreachable!()
    };
    *delta_bytes = *base;
    assert!(matches!(
        unit.validate().unwrap_err().kind(),
        VirValidationErrorKind::TypeMismatch {
            context: "pointer offset delta",
            ..
        }
    ));
}
