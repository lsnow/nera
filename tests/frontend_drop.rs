use nera::backend::X86_64_UNKNOWN_LINUX_GNU;
use nera::{
    CfgAnalysisConfig, FrontendStatus, ObligationStatus, ResourceObligationKind, SourceFile,
    VirInstruction, VirRuntimeValue, analyze, interpret, verify_program,
};

fn accepted(name: &str, source: &str) -> nera::FrontendOutput {
    let output = analyze(&SourceFile::from_text(name, source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{name}: {:?}",
        output.issues()
    );
    output
}

#[test]
fn builtin_drop_covers_conditional_free_partial_move_and_nested_scope() {
    let source = include_str!("../spec/cases/verify/drop-scope.nera");
    let output = accepted("drop-scope.nera", source);
    let vir = output.vir().expect("drop-scope source has VIR");
    let instructions = vir
        .runtime()
        .functions
        .iter()
        .flat_map(|function| &function.blocks)
        .flat_map(|block| &block.instructions)
        .collect::<Vec<_>>();
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction.instruction, VirInstruction::DropOwn { .. }))
    );
    assert!(
        instructions.iter().any(|instruction| matches!(
            instruction.instruction,
            VirInstruction::ObjectDrop { .. }
        ))
    );

    let resolved = vir.resolve().expect("drop-scope VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("drop-scope verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
    assert!(verification.functions().values().any(|function| {
        function.cfg().obligations().iter().any(|record| {
            matches!(
                record.obligation().kind(),
                ResourceObligationKind::OwnershipConserved { .. }
            ) && record.obligation().status() == ObligationStatus::Proven
        })
    }));
    assert!(verification.functions().values().any(|function| {
        function
            .cfg()
            .blocks()
            .values()
            .any(|block| block.entry_conditional_state().cases().len() > 1)
    }));

    let budgeted = verify_program(
        &resolved,
        CfgAnalysisConfig {
            max_guarded_cases_per_block: 1,
            ..CfgAnalysisConfig::default()
        },
    )
    .expect("single-case drop analysis still converges");
    assert!(!budgeted.is_memory_checked_core0());
    assert!(budgeted.functions().values().any(|function| {
        function.cfg().obligations().iter().any(|record| {
            matches!(
                record.obligation().kind(),
                ResourceObligationKind::DropFlagKnown { .. }
            ) && record.obligation().status() == ObligationStatus::Unknown
        })
    }));
    assert_eq!(
        interpret(resolved.runtime())
            .expect("drop-scope program executes")
            .values(),
        [VirRuntimeValue::U64(16)]
    );

    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("drop effects lower to native code");
    let assembly = X86_64_UNKNOWN_LINUX_GNU
        .emit_assembly(&machine)
        .expect("drop effects emit GNU assembly");
    assert!(assembly.contains("call free@PLT"));
}

#[test]
fn ownership_conservation_rejects_a_hand_authored_leak() {
    let output = accepted(
        "leak.nera",
        "fn main() -> u64 { let owner = alloc<u64>(1); return 0; }",
    );
    let mut unit = output.vir().expect("leak source has VIR").as_unit().clone();
    for block in &mut unit.runtime.functions[0].blocks {
        block.instructions.retain(|instruction| {
            !matches!(instruction.instruction, VirInstruction::DropOwn { .. })
        });
    }
    unit.rebuild_source_map_from_runtime("leak-mutation.nera", 59);
    let validated = unit
        .into_validated()
        .expect("removing cleanup remains structurally valid VIR");
    let verification = verify_program(
        &validated.resolve().expect("leaking VIR resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("leak verification converges");
    assert!(!verification.is_memory_checked_core0());
    assert!(verification.functions().values().any(|function| {
        function.cfg().obligations().iter().any(|record| {
            matches!(
                record.obligation().kind(),
                ResourceObligationKind::OwnershipConserved { .. }
            ) && record.obligation().status() == ObligationStatus::Refuted
        })
    }));
}
