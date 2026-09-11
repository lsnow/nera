use nera::backend::X86_64_UNKNOWN_LINUX_GNU;
use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, VirExecutionErrorKind, VirInstruction,
    VirLoanRange, VirRuntimeValue, VirValidationErrorKind, analyze, interpret, verify_program,
};

fn accepted(name: &str, source: &str) -> nera::FrontendOutput {
    let output = analyze(&SourceFile::from_text(name, source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{name}: {:#?}",
        output.issues()
    );
    output
}

fn assert_checked_result(output: &nera::FrontendOutput, expected: u64) {
    let vir = output.vir().expect("accepted slice source has VIR");
    let resolved = vir.resolve().expect("safe slice VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("safe slice verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("safe slice executes")
            .values(),
        [VirRuntimeValue::U64(expected)]
    );
    X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("safe slice reaches native planning");
}

#[test]
fn shared_slice_local_copy_and_annotation_preserve_length_and_authority() {
    let output = accepted(
        "shared-safe-slice.nera",
        "fn main() -> u64 {
             let values = [10, 20, 30, 40];
             let view: &[u64] = &values[1..3];
             let copied = view;
             return copied[0] + view[1];
         }",
    );
    let instructions = output.vir().expect("VIR").runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.instruction)
        .collect::<Vec<_>>();
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction, VirInstruction::SliceAddress { .. }))
    );
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction, VirInstruction::LoanAliasShared { .. }))
    );
    assert_checked_result(&output, 50);
}

#[test]
fn mutable_constant_subobjects_are_disjoint_and_restore_the_owner() {
    let output = accepted(
        "mutable-safe-slices.nera",
        "fn main() -> u64 {
             let mut values = [1, 2, 3, 4];
             let left = &mut values[..2];
             let right = &mut values[2..];
             left[0] = 7;
             right[0] = 9;
             return values[0] + values[2];
         }",
    );
    let ranges = output.vir().expect("VIR").runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction.instruction {
            VirInstruction::LoanBegin { effect, .. } => Some(effect.range),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        ranges,
        [
            VirLoanRange {
                start_bytes: 0,
                end_bytes: 16,
            },
            VirLoanRange {
                start_bytes: 16,
                end_bytes: 32,
            },
        ]
    );
    assert_checked_result(&output, 16);
}

#[test]
fn shared_subslices_can_coexist_and_slice_backed_index_is_checked() {
    let output = accepted(
        "shared-subslices.nera",
        "fn main() -> u64 {
             let values = [2, 4, 6, 8];
             let whole = &values[..];
             let left = &whole[..2];
             let right = &whole[2..];
             return left[1] + right[0];
         }",
    );
    let reborrows = output.vir().expect("VIR").runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter(|instruction| {
            matches!(instruction.instruction, VirInstruction::LoanReborrow { .. })
        })
        .count();
    assert_eq!(reborrows, 2);
    assert_checked_result(&output, 10);
}

#[test]
fn dynamic_slice_bounds_are_evaluated_once_and_use_a_conservative_envelope() {
    let output = accepted(
        "dynamic-safe-slice.nera",
        "fn main() -> u64 {
             let values = [10, 20, 30, 40];
             let view = &values[begin()..end()];
             return view[index()];
         }
         fn begin() -> usize { return 1usize; }
         fn end() -> usize { return 3usize; }
         fn index() -> usize { return 1usize; }",
    );
    let function = &output.vir().expect("VIR").runtime().functions[0];
    let instructions = function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect::<Vec<_>>();
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(instruction.instruction, VirInstruction::Call { .. }))
            .count(),
        3
    );
    assert!(instructions.iter().any(|instruction| matches!(
        instruction.instruction,
        VirInstruction::LoanBegin {
            effect,
            ..
        } if effect.range == VirLoanRange { start_bytes: 0, end_bytes: 32 }
    )));
    let resolved = output.vir().expect("VIR").resolve().expect("VIR resolves");
    assert_eq!(
        interpret(resolved.runtime())
            .expect("dynamic safe slice executes")
            .values(),
        [VirRuntimeValue::U64(30)]
    );
}

#[test]
fn slice_of_a_dynamically_selected_array_uses_the_complete_candidate_envelope() {
    let output = accepted(
        "dynamic-array-slice.nera",
        "fn main() -> u64 {
             let values = [[1, 2], [3, 4]];
             let row = 1usize;
             let view = &values[row][..];
             return view[0];
         }",
    );
    assert!(
        output.vir().expect("VIR").runtime().functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .any(|instruction| matches!(
                instruction.instruction,
                VirInstruction::LoanBegin {
                    effect,
                    ..
                } if effect.range == VirLoanRange { start_bytes: 0, end_bytes: 32 }
            ))
    );
    assert_checked_result(&output, 3);
}

#[test]
fn empty_one_past_view_is_valid_but_cannot_be_indexed() {
    let empty = accepted(
        "empty-safe-slice.nera",
        "fn main() -> u64 {
             let values = [1, 2];
             let empty = &values[2..2];
             return 7;
         }",
    );
    assert_checked_result(&empty, 7);

    let indexed = accepted(
        "indexed-empty-safe-slice.nera",
        "fn main() -> u64 {
             let values = [1, 2];
             let empty = &values[2..2];
             return empty[0];
         }",
    );
    let resolved = indexed.vir().expect("VIR").resolve().expect("VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("empty slice verification converges");
    assert!(!verification.is_memory_checked_core0());
    assert!(matches!(
        interpret(resolved.runtime())
            .expect_err("empty slice cannot be indexed")
            .kind(),
        VirExecutionErrorKind::IndexOutOfBounds {
            index: 0,
            length: 0
        }
    ));
}

#[test]
fn dynamic_out_of_bounds_slice_is_not_promoted_to_a_safe_view() {
    let output = accepted(
        "out-of-bounds-safe-slice.nera",
        "fn main() -> u64 {
             let values = [1, 2];
             let end = 3usize;
             let view = &values[..end];
             return 0;
         }",
    );
    let resolved = output.vir().expect("VIR").resolve().expect("VIR resolves");
    assert!(
        !verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("range verification converges")
            .is_memory_checked_core0()
    );
    assert!(matches!(
        interpret(resolved.runtime())
            .expect_err("out-of-bounds view creation must fault")
            .kind(),
        VirExecutionErrorKind::InvalidSliceRange {
            start: 0,
            end: 3,
            length: 2
        }
    ));
}

#[test]
fn evaluated_constant_slice_ranges_use_actual_disjointness() {
    let output = accepted(
        "dynamic-mutable-safe-slices.nera",
        "fn main() -> u64 {
             let mut values = [1, 2, 3, 4];
             let begin = 0usize;
             let middle = 2usize;
             let end = 4usize;
             let left = &mut values[begin..middle];
             let right = &mut values[middle..end];
             left[0] = 7;
             right[0] = 9;
             return 0;
         }",
    );
    let resolved = output.vir().expect("VIR").resolve().expect("VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("dynamic overlap analysis converges");
    assert!(verification.is_memory_checked_core0());
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(0)]
    );
}

#[test]
fn safe_slice_surface_and_storage_boundaries_fail_closed() {
    for (name, source, expected) in [
        (
            "bare-slice-local.nera",
            "fn main() -> u64 { let value: [u64] = [1, 2]; return 0; }",
            FrontendStatus::Unsupported,
        ),
        (
            "slice-in-aggregate.nera",
            "struct View { value: &[u64], } fn main() -> u64 { return 0; }",
            FrontendStatus::Unsupported,
        ),
        (
            "unborrowed-range.nera",
            "fn main() -> u64 { let values = [1, 2]; let view = values[..]; return 0; }",
            FrontendStatus::Unsupported,
        ),
        (
            "inclusive-range.nera",
            "fn main() -> u64 { let values = [1, 2]; let view = &values[0..=1]; return 0; }",
            FrontendStatus::Unsupported,
        ),
        (
            "mutable-from-shared-slice.nera",
            "fn main() -> u64 { let values = [1, 2]; let shared = &values[..]; let invalid = &mut shared[..]; return 0; }",
            FrontendStatus::Invalid,
        ),
    ] {
        let output = analyze(&SourceFile::from_text(name, source));
        assert_eq!(output.status(), expected, "{name}: {:#?}", output.issues());
    }
}

#[test]
fn slice_address_schema_rejects_a_forged_stride() {
    let output = accepted(
        "slice-address-schema.nera",
        "fn main() -> u64 { let values = [1, 2]; let view = &values[..]; return view[0]; }",
    );
    let mut forged = output.vir().expect("VIR").as_unit().clone();
    let stride = forged.runtime.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .find_map(|instruction| match &mut instruction.instruction {
            VirInstruction::SliceAddress { stride_bytes, .. } => Some(stride_bytes),
            _ => None,
        })
        .expect("surface slice emits SliceAddress");
    *stride = 1;
    assert_eq!(
        forged
            .validate()
            .expect_err("a forged slice stride must be rejected")
            .kind(),
        &VirValidationErrorKind::InvalidSliceRange
    );
}
