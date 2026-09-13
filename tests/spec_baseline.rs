#[path = "support/frontend_checks.rs"]
mod frontend_checks;
#[path = "support/spec_arena.rs"]
mod spec_arena;

use nera::{
    CfgAnalysisConfig, FrontendIssueKind, FrontendStatus, ObligationStatus, ResourceObligationKind,
    SourceFile, VirFunctionId, VirRuntimeValue, analyze, interpret, verify_program,
};
use spec_arena::Mutation;

#[test]
fn source_two_cut_borrow_baseline_preserves_remaining_storage() {
    for (first, second, expected) in [
        (1, 3, 49),
        (2, 4, 49),
        (0, 3, 0),
        (3, 3, 0),
        (3, 2, 0),
        (1, 6, 0),
    ] {
        let source = spec_arena::SOURCE.replace(
            "arena(1usize, 3usize)",
            &format!("arena({first}usize, {second}usize)"),
        );
        frontend_checks::checked("spec-arena-baseline.nera", &source, expected);
    }
}

#[test]
fn raw_two_cut_arena_checks_dynamic_inputs_and_returns_all_permissions() {
    for first in 1..=2 {
        for second in 3..=4 {
            let unit = spec_arena::unit(first, second, Mutation::None)
                .into_validated()
                .unwrap();
            let resolved = unit.resolve().unwrap();
            let verified = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
            assert!(
                verified.is_memory_checked_core0(),
                "{:#?}",
                verified.diagnostics()
            );
            assert!(unit.as_unit().specs.trust_entries().is_empty());
            let cfg = verified.functions()[&VirFunctionId::new(1)].cfg();
            assert_eq!(
                cfg.obligations()
                    .iter()
                    .filter(|o| matches!(
                        o.obligation().kind(),
                        ResourceObligationKind::PermissionJoinCompatible { .. }
                    ))
                    .count(),
                2
            );
            // Independent concrete expected result: 12 + 30 + untouched tail 7.
            assert_eq!(
                interpret(resolved.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(49)]
            );
            nera::backend::X86_64_UNKNOWN_LINUX_GNU
                .codegen_program(resolved.runtime())
                .unwrap();
        }
    }
}

#[test]
fn raw_arena_mutations_fail_at_resource_obligations() {
    for mutation in [
        Mutation::OutOfBounds,
        Mutation::OverlappingPermission,
        Mutation::Uninitialized,
        Mutation::UseAfterReturn,
    ] {
        let unit = spec_arena::unit(1, 3, mutation).into_validated().unwrap();
        let verified =
            verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
        assert!(!verified.is_memory_checked_core0(), "{mutation:?}");
        assert!(
            verified.functions()[&VirFunctionId::new(1)]
                .cfg()
                .obligations()
                .iter()
                .any(|o| {
                    let obligation = o.obligation();
                    obligation.status() == ObligationStatus::Refuted
                        && match mutation {
                            Mutation::OutOfBounds => matches!(
                                obligation.kind(),
                                ResourceObligationKind::PermissionSplitPointInRange { .. }
                            ),
                            Mutation::OverlappingPermission => matches!(
                                obligation.kind(),
                                ResourceObligationKind::PermissionCoversAccess { .. }
                            ),
                            Mutation::Uninitialized => matches!(
                                obligation.kind(),
                                ResourceObligationKind::MemoryInitialized { .. }
                            ),
                            Mutation::UseAfterReturn => matches!(
                                obligation.kind(),
                                ResourceObligationKind::PermissionAvailable { .. }
                            ),
                            _ => unreachable!(),
                        }
                }),
            "{mutation:?}: {:#?}",
            verified.diagnostics()
        );
    }
}

#[test]
fn raw_dynamic_initialization_precision_gap_stays_unproved() {
    let unit = spec_arena::unit(1, 3, Mutation::DynamicInitialization)
        .into_validated()
        .unwrap();
    let verified = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert!(!verified.is_memory_checked_core0());
    assert!(
        verified.functions()[&VirFunctionId::new(1)]
            .cfg()
            .obligations()
            .iter()
            .any(|o| {
                matches!(
                    o.obligation().kind(),
                    ResourceObligationKind::MemoryInitialized { .. }
                ) && o.obligation().status() == ObligationStatus::Unknown
            })
    );
}

#[test]
fn scalar_preconditions_are_not_unchecked_assumptions_at_the_caller() {
    let unit = spec_arena::unit(1, 3, Mutation::CallerPrecondition)
        .into_validated()
        .unwrap();
    let verified = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert!(!verified.is_memory_checked_core0());
    assert!(
        !verified.functions()[&VirFunctionId::new(0)]
            .cfg()
            .all_obligations_proven()
    );
}

#[test]
fn proof_blocks_remain_gated_after_local_assert_is_opened() {
    let statement = "proof { assert first < second; }";
    let source = spec_arena::SOURCE.replace(
        "let parent =",
        &format!("{statement}\n                let parent ="),
    );
    let output = analyze(&SourceFile::from_text("spec-arena-target.nera", &source));
    assert_eq!(output.status(), FrontendStatus::Unsupported);
    assert!(output.vir().is_none());
    assert!(
        output
            .issues()
            .iter()
            .any(|issue| issue.kind() == FrontendIssueKind::Unsupported)
    );
}

#[test]
fn measure_spec_arena_baseline_when_requested() {
    if std::env::var_os("NERA_SPEC_BASELINE_MEASURE").is_none() {
        return;
    }
    let source = frontend_checks::accepted("spec-arena-baseline.nera", spec_arena::SOURCE);
    let raw = spec_arena::unit(1, 3, Mutation::None)
        .into_validated()
        .unwrap();
    let dynamic = spec_arena::unit(1, 3, Mutation::DynamicInitialization)
        .into_validated()
        .unwrap();
    println!(
        "case,sample,checked,relation_queries,block_visits,refinement_visits,obligations,verify_us"
    );
    for (name, unit, expected) in [
        ("source", source.vir().unwrap(), true),
        ("raw", &raw, true),
        ("raw-dynamic", &dynamic, false),
    ] {
        let resolved = unit.resolve().unwrap();
        for sample in 0..5 {
            let start = std::time::Instant::now();
            let verified = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
            let elapsed = start.elapsed().as_micros();
            assert_eq!(verified.is_memory_checked_core0(), expected);
            let functions: Vec<_> = verified.functions().values().collect();
            let queries: usize = functions
                .iter()
                .map(|f| f.cfg().relation_queries().len())
                .sum();
            let visits: u64 = functions.iter().map(|f| f.cfg().block_visits()).sum();
            let refinements: u64 = functions
                .iter()
                .map(|f| f.cfg().refinement_block_visits())
                .sum();
            let obligations: usize = functions.iter().map(|f| f.cfg().obligations().len()).sum();
            println!(
                "{name},{sample},{expected},{queries},{visits},{refinements},{obligations},{elapsed}"
            );
        }
    }
}
