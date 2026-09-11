use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, VirRuntimeValue, analyze, interpret,
    verify_program,
};

#[path = "../src/bin/fuzz_support/borrow_cases.rs"]
mod borrow_cases;

const MATRIX: &str = include_str!("../spec/cases/verify/borrow-acceptance.nera");

fn accepted(source: &str) -> nera::FrontendOutput {
    let file = SourceFile::from_text("borrow-acceptance.nera", source);
    let output = analyze(&file);
    assert_eq!(output, analyze(&file), "HIR/VIR and end-plan replay");
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{source}\n{:#?}",
        output.issues()
    );
    output
}

#[test]
fn combined_borrow_matrix_is_checked_and_deterministic() {
    let output = accepted(MATRIX);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let first = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert_eq!(
        first,
        verify_program(&resolved, CfgAnalysisConfig::default()).unwrap(),
        "findings, origins, obligations and guarded states replay"
    );
    assert!(
        first.is_memory_checked_core0(),
        "{:#?}",
        first.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(19)]
    );
}

#[test]
fn generated_borrow_cfg_loop_call_families_keep_both_outcomes() {
    for ordinal in 0..borrow_cases::FAMILY_COUNT * 8 {
        let source = borrow_cases::source(ordinal, ordinal.wrapping_mul(0x9e37_79b9));
        let output = accepted(&source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let first = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert_eq!(
            first,
            verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
        );
        assert_eq!(
            first.is_memory_checked_core0(),
            borrow_cases::expected_checked(ordinal),
            "family {}: {source}\n{:#?}",
            ordinal % borrow_cases::FAMILY_COUNT,
            first.diagnostics()
        );
        if first.is_memory_checked_core0() {
            interpret(resolved.runtime()).expect("only checked inputs enter differential");
        } else {
            assert!(!first.diagnostics().is_empty());
        }
    }
}

#[test]
fn a_safe_borrow_execution_cannot_discharge_an_unvisited_branch() {
    let output = accepted(&borrow_cases::source(6, 22));
    let resolved = output.vir().unwrap().resolve().unwrap();
    let first = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!first.is_memory_checked_core0());
    // Deliberately unverified observation, not a checked differential input.
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(23)]
    );
    assert_eq!(
        first,
        verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
    );
}

#[test]
fn exhausted_borrow_budgets_never_grant_call_or_reborrow_authority() {
    let output = accepted(MATRIX);
    let resolved = output.vir().unwrap().resolve().unwrap();
    for config in [
        CfgAnalysisConfig {
            max_active_loans_per_case: 0,
            ..CfgAnalysisConfig::default()
        },
        CfgAnalysisConfig {
            max_aliases_per_loan: 0,
            ..CfgAnalysisConfig::default()
        },
        CfgAnalysisConfig {
            max_reborrow_depth: 0,
            ..CfgAnalysisConfig::default()
        },
        CfgAnalysisConfig {
            max_region_constraints_per_function: 0,
            ..CfgAnalysisConfig::default()
        },
        CfgAnalysisConfig {
            max_block_visits: 1,
            ..CfgAnalysisConfig::default()
        },
    ] {
        let first = verify_program(&resolved, config);
        assert_eq!(first, verify_program(&resolved, config));
        if let Ok(result) = first {
            assert!(!result.is_memory_checked_core0());
            assert!(!result.diagnostics().is_empty());
        }
    }
}

#[test]
fn call_restoration_does_not_end_a_child_with_a_later_use() {
    let output = accepted(
        "fn main() -> u64 {
        let mut value = 1; let parent = &mut value; let child = &mut *parent;
        bump(child); *parent = 0; return *child;
    } fn bump(r: &mut u64) { *r = *r + 1; return; }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!result.is_memory_checked_core0());
    assert!(interpret(resolved.runtime()).is_err());
}

#[test]
fn returned_slice_length_is_independently_revalidated() {
    let output = accepted(
        "fn main() -> u64 {
        let values = [1, 2, 3]; let r = identity(&values[..]); return r[0];
    } fn identity(r: &[u64]) -> &[u64] { let other = 1usize; return r; }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    let mut unit = output.vir().unwrap().as_unit().clone();
    let body = &mut unit.runtime.functions[1];
    let other = body
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match instruction.instruction {
            nera::VirInstruction::Constant {
                result,
                value: nera::VirConstant::U64(1),
            } => Some(result.id),
            _ => None,
        })
        .unwrap();
    for block in &mut body.blocks {
        if let nera::VirTerminator::Return { values } = &mut block.terminator.terminator {
            values[1] = other;
        }
    }
    assert!(
        unit.into_validated().is_err(),
        "changing a signature-preserved view length is not identity"
    );
}

#[test]
fn call_region_metadata_is_ghost_non_interfering() {
    let output = accepted(MATRIX);
    let baseline = output.vir().unwrap();
    let mut enriched = baseline.as_unit().clone();
    let mut regions = enriched.borrows.regions().to_vec();
    for region in &mut regions {
        if region.origin == nera::VirBorrowRegionOrigin::Inferred {
            region.origin = nera::VirBorrowRegionOrigin::Lexical;
        }
    }
    enriched.borrows =
        nera::VirBorrowEnvironment::from_tables(regions, enriched.borrows.constraints().to_vec());
    let enriched = enriched.into_validated().unwrap();
    assert_ne!(baseline.stable_dump(), enriched.stable_dump());
    let baseline = baseline.resolve().unwrap();
    let enriched = enriched.resolve().unwrap();
    for resolved in [&baseline, &enriched] {
        assert!(
            verify_program(resolved, CfgAnalysisConfig::default())
                .unwrap()
                .is_memory_checked_core0()
        );
    }
    assert_eq!(
        interpret(baseline.runtime()).unwrap(),
        interpret(enriched.runtime()).unwrap()
    );
    let target = nera::backend::X86_64_UNKNOWN_LINUX_GNU;
    assert_eq!(
        target.plan_program(baseline.runtime()).unwrap(),
        target.plan_program(enriched.runtime()).unwrap()
    );
    assert_eq!(
        target.codegen_program(baseline.runtime()).unwrap(),
        target.codegen_program(enriched.runtime()).unwrap()
    );
}

#[test]
fn signature_relations_follow_the_current_supported_boundary() {
    for source in [
        "fn select(a: &u64, b: &u64, flag: bool) -> &u64 { if flag { return a; } return b; }",
        "fn local(r: &u64) -> &u64 { let value = 1; return &value; }",
        "struct Holder { value: &u64, } fn read(r: &Holder) -> u64 { return *r.value; }",
    ] {
        let output = analyze(&SourceFile::from_text("deferred.nera", source));
        assert_ne!(
            output.status(),
            FrontendStatus::AcceptedProposal,
            "{source}"
        );
        assert!(!output.issues().is_empty());
    }
    accepted("fn child(r: &mut u64) -> &mut u64 { return &mut *r; }");
    let output = accepted(
        "fn main() -> u64 { let values = [1, 2]; return read(&values[..]); }
        fn read(r: &[u64]) -> u64 { return r[0]; }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert!(
        !verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0(),
        "one nonempty caller cannot become an unconditional callee length premise"
    );
}

#[test]
fn loop_scope_exit_restores_array_before_a_later_slice() {
    let output = accepted(
        "fn main() -> u64 {
        let mut values = [1, 2, 3];
        { let parent = &mut values[1]; for i in 0..3 { *parent = *parent + 1; } }
        let view = &values[..]; return view[1];
    }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        result.is_memory_checked_core0(),
        "{:#?}",
        result.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(5)]
    );
}
