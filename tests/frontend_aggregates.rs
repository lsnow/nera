use nera::{
    CfgAnalysisConfig, FrontendIssueKind, FrontendOutput, FrontendStatus, HirTypeKind, SourceFile,
    VirExecutionErrorKind, VirInstruction, VirRuntimeValue, analyze, interpret, verify_program,
};

fn lower(name: &str, source: &str) -> FrontendOutput {
    analyze(&SourceFile::from_text(name, source))
}

fn accepted(name: &str, source: &str) -> FrontendOutput {
    let output = lower(name, source);
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{name}: {:?}",
        output.issues()
    );
    output
}

#[test]
fn checked_in_surface_slice_reaches_every_runtime_consumer() {
    let source = include_str!("../spec/cases/aggregate/surface.nera");
    let output = accepted("spec/cases/aggregate/surface.nera", source);
    let ast = output.ast().expect("aggregate source has AST");
    assert_eq!(ast.structs().len(), 1);
    assert_eq!(ast.structs()[0].fields.len(), 4);

    let hir = output.hir().expect("aggregate source has typed HIR");
    let record = hir
        .types()
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Record"))
        .expect("nominal Record type");
    assert!(matches!(record.kind, HirTypeKind::Struct { .. }));
    let layout = hir
        .layout_of(record.id)
        .expect("Record has concrete layout");
    assert_eq!(layout.size_bytes, 56);
    assert_eq!(
        layout
            .fields
            .iter()
            .map(|field| field.offset_bytes)
            .collect::<Vec<_>>(),
        [0, 8, 16, 32]
    );

    let vir = output.vir().expect("aggregate source has validated VIR");
    assert_eq!(
        vir.stable_dump(),
        include_str!("../spec/cases/aggregate/surface.vir")
    );
    let entry = &vir.runtime().functions[0];
    let calls = entry
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match &instruction.instruction {
            VirInstruction::Call { target, .. } => Some(target.symbol.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(calls, ["seed", "index"]);
    assert!(
        entry
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .any(|instruction| matches!(
                instruction.instruction,
                VirInstruction::TupleElementAddress { .. }
            ))
    );

    let resolved = vir.resolve().expect("aggregate VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("aggregate surface reaches whole-program verification");
    assert!(
        verification.is_memory_checked_core0(),
        "the closed index() body proves its constant return is in bounds"
    );
    let execution = interpret(resolved.runtime()).expect("aggregate source executes");
    assert_eq!(execution.values(), [VirRuntimeValue::U64(26)]);
}

#[test]
fn bounded_runtime_dynamic_aggregate_places_are_memory_checked() {
    let output = accepted(
        "bounded-dynamic-object.nera",
        include_str!("../spec/cases/aggregate/bounded-dynamic-object.nera"),
    );
    let vir = output.vir().expect("bounded aggregate source has VIR");
    let resolved = vir.resolve().expect("bounded aggregate VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("bounded aggregate source analyzes");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("bounded aggregate source executes")
            .values(),
        [VirRuntimeValue::U64(17)]
    );
}

#[test]
fn runtime_dynamic_index_can_replace_and_read_a_complete_object() {
    let source = include_str!("../spec/cases/aggregate/dynamic-object.nera");
    let output = accepted("spec/cases/aggregate/dynamic-object.nera", source);
    let vir = output.vir().expect("dynamic object source has VIR");
    let calls = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match &instruction.instruction {
            VirInstruction::Call { target, .. } => Some(target.symbol.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(calls, ["next", "next"]);
    let resolved = vir.resolve().expect("dynamic object VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("dynamic object source reaches whole-program verification");
    assert!(
        verification.is_memory_checked_core0(),
        "the closed next() body proves its constant return is in bounds"
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("dynamic object source executes")
            .values(),
        [VirRuntimeValue::U64(17)]
    );
}

#[test]
fn constructor_operands_follow_source_order() {
    let output = accepted(
        "aggregate-source-order.nera",
        "struct Pair {
             left: u64,
             right: u64,
         }

         fn main() -> u64 {
             let pair = Pair { right: second(), left: first() };
             return pair.left + pair.right;
         }

         fn first() -> u64 { return 1; }
         fn second() -> u64 { return 2; }",
    );
    let calls = output.vir().expect("source-order VIR").runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match &instruction.instruction {
            VirInstruction::Call { target, .. } => Some(target.symbol.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(calls, ["second", "first"]);
}

#[test]
fn aggregate_abi_direct_and_indirect_values_are_verified_and_executable() {
    for (name, source) in [
        (
            "abi-direct.nera",
            include_str!("../spec/cases/aggregate/abi-direct.nera"),
        ),
        (
            "abi-indirect.nera",
            include_str!("../spec/cases/aggregate/abi-indirect.nera"),
        ),
        (
            "abi-recursive.nera",
            include_str!("../spec/cases/aggregate/abi-recursive.nera"),
        ),
        (
            "abi-register-stack.nera",
            include_str!("../spec/cases/aggregate/abi-register-stack.nera"),
        ),
    ] {
        let output = accepted(name, source);
        let resolved = output
            .vir()
            .expect("aggregate ABI source has VIR")
            .resolve()
            .expect("aggregate ABI VIR resolves");
        let verification = verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("aggregate ABI source analyzes");
        assert!(
            verification.is_memory_checked_core0(),
            "{name}: {:?}",
            verification.diagnostics()
        );
        assert_eq!(
            interpret(resolved.runtime())
                .expect("aggregate ABI source executes")
                .values(),
            [VirRuntimeValue::U64(42)],
            "{name}"
        );
    }
}

#[test]
fn aggregate_surface_errors_fail_closed_at_their_owner() {
    let cases = [
        (
            "missing-field.nera",
            FrontendStatus::Invalid,
            "struct Pair { left: u64, right: u64, }
             fn main() -> u64 {
                 let pair = Pair { left: 1 };
                 return pair.left;
             }",
        ),
        (
            "duplicate-field.nera",
            FrontendStatus::Invalid,
            "struct Pair { left: u64, right: u64, }
             fn main() -> u64 {
                 let pair = Pair { left: 1, left: 2, right: 3 };
                 return pair.right;
             }",
        ),
        (
            "foreign-field.nera",
            FrontendStatus::Invalid,
            "struct Pair { left: u64, }
             fn main() -> u64 {
                 let pair = Pair { other: 1 };
                 return 0;
             }",
        ),
        (
            "wrong-field-type.nera",
            FrontendStatus::Invalid,
            "struct Pair { left: u64, }
             fn main() -> u64 {
                 let pair = Pair { left: true };
                 return 0;
             }",
        ),
        (
            "constant-index-oob.nera",
            FrontendStatus::Invalid,
            "fn main() -> u64 {
                 let values = [1, 2];
                 return values[2];
             }",
        ),
        (
            "aggregate-budget.nera",
            FrontendStatus::Unsupported,
            "fn main() -> u64 {
                 let values = [0; 513];
                 return values[0];
             }",
        ),
    ];
    for (name, expected, source) in cases {
        let output = lower(name, source);
        assert_eq!(output.status(), expected, "{name}: {:?}", output.issues());
        assert!(output.hir().is_none(), "{name}");
        assert!(output.vir().is_none(), "{name}");
        assert!(matches!(
            output.issues()[0].kind(),
            FrontendIssueKind::Elaboration | FrontendIssueKind::Unsupported
        ));
    }
}

#[test]
fn dynamic_out_of_bounds_is_not_misclassified_as_a_frontend_error() {
    let output = accepted(
        "dynamic-index-oob.nera",
        "fn main() -> u64 {
             let values = [1, 2];
             let index = 3usize;
             return values[index];
         }",
    );
    let vir = output.vir().expect("dynamic OOB source has structural VIR");
    let resolved = vir.resolve().expect("dynamic OOB VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("dynamic OOB reaches verifier");
    assert!(!verification.is_memory_checked_core0());
    let error = interpret(resolved.runtime()).expect_err("dynamic OOB execution must fault");
    assert!(
        matches!(error.kind(), VirExecutionErrorKind::IndexOutOfBounds { .. }),
        "unexpected dynamic OOB fault: {:?}",
        error.kind()
    );
}
