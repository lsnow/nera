use nera::{
    CfgAnalysisConfig, FrontendStatus, GuardedStatePrecisionLoss, ObligationStatus,
    ResourceObligationKind, SourceFile, VirConstant, VirExecutionErrorKind, VirInstruction,
    VirRuntimeValue, analyze, interpret, verify_program,
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
fn source_resource_matrix_is_checked_and_deterministic() {
    let source = include_str!("../spec/cases/verify/resource-acceptance.nera");
    let output = accepted("resource-acceptance.nera", source);
    let resolved = output
        .vir()
        .expect("resource acceptance source has VIR")
        .resolve()
        .expect("resource acceptance VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("resource acceptance verification converges");
    assert_eq!(
        verification,
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("resource acceptance verification replays")
    );
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:#?}",
        verification.diagnostics()
    );
    assert!(verification.functions().values().any(|function| {
        function
            .cfg()
            .blocks()
            .values()
            .any(|block| block.entry_conditional_state().cases().len() > 1)
    }));
    assert_eq!(
        interpret(resolved.runtime())
            .expect("resource acceptance source executes")
            .values(),
        [VirRuntimeValue::U64(79)]
    );
}

#[test]
fn one_safe_execution_does_not_promote_an_unsafe_alternative() {
    let source = include_str!("../spec/cases/verify/conditional-uaf.nera");
    let output = accepted("one-safe-execution.nera", source);
    let resolved = output
        .vir()
        .expect("unsafe-alternative source has VIR")
        .resolve()
        .expect("unsafe-alternative VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("unsafe-alternative verification converges");
    assert!(!verification.is_memory_checked_core0());
    assert!(verification.functions().values().any(|function| {
        function.cfg().obligations().iter().any(|record| {
            record.obligation().status() != ObligationStatus::Proven
                && matches!(
                    record.obligation().kind(),
                    ResourceObligationKind::AllocationLive { .. }
                        | ResourceObligationKind::PermissionAvailable { .. }
                )
        })
    }));
    assert_eq!(
        interpret(resolved.runtime())
            .expect("the selected runtime path is safe but remains unverified")
            .values(),
        [VirRuntimeValue::U64(23)]
    );
}

#[test]
fn wrong_drop_flag_and_double_drop_mutations_fail_closed() {
    let source = "fn main() -> u64 {
        let owner = alloc<u64>(1);
        *owner = 31;
        return *owner;
    }";
    let output = accepted("drop-mutations.nera", source);
    let original = output
        .vir()
        .expect("drop mutation source has VIR")
        .as_unit();

    let mut wrong_flag = original.clone();
    let drop_condition = wrong_flag.runtime.functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match instruction.instruction {
            VirInstruction::DropOwn { condition, .. } => Some(condition),
            _ => None,
        })
        .expect("implicit scalar drop exists");
    let flag = wrong_flag.runtime.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .find(|instruction| {
            matches!(
                instruction.instruction,
                VirInstruction::Constant { result, .. } if result.id == drop_condition
            )
        })
        .expect("drop flag definition exists");
    let VirInstruction::Constant { value, .. } = &mut flag.instruction else {
        unreachable!();
    };
    *value = VirConstant::Bool(false);
    let wrong_flag = wrong_flag
        .into_validated()
        .expect("wrong drop flag remains structurally valid");
    let wrong_flag = wrong_flag.resolve().expect("wrong drop flag VIR resolves");
    let verification = verify_program(&wrong_flag, CfgAnalysisConfig::default())
        .expect("wrong drop flag verification converges");
    assert!(!verification.is_memory_checked_core0());
    assert!(verification.functions().values().any(|function| {
        function.cfg().obligations().iter().any(|record| {
            matches!(
                record.obligation().kind(),
                ResourceObligationKind::OwnershipConserved { .. }
            ) && record.obligation().status() != ObligationStatus::Proven
        })
    }));

    let mut double_drop = original.clone();
    let function = &mut double_drop.runtime.functions[0];
    let (block_index, drop_index) = function
        .blocks
        .iter()
        .enumerate()
        .find_map(|(block_index, block)| {
            block
                .instructions
                .iter()
                .position(|instruction| {
                    matches!(instruction.instruction, VirInstruction::DropOwn { .. })
                })
                .map(|drop_index| (block_index, drop_index))
        })
        .expect("implicit scalar drop exists");
    let duplicate = function.blocks[block_index].instructions[drop_index].clone();
    function.blocks[block_index]
        .instructions
        .insert(drop_index + 1, duplicate);
    double_drop.rebuild_source_map_from_runtime("double-drop-mutation.nera", source.len());
    let double_drop = double_drop
        .into_validated()
        .expect("double drop remains structurally valid");
    let double_drop = double_drop.resolve().expect("double drop VIR resolves");
    let verification = verify_program(&double_drop, CfgAnalysisConfig::default())
        .expect("double drop verification converges");
    assert!(!verification.is_memory_checked_core0());
    assert!(verification.functions().values().any(|function| {
        function.cfg().obligations().iter().any(|record| {
            record.obligation().status() != ObligationStatus::Proven
                && matches!(
                    record.obligation().kind(),
                    ResourceObligationKind::AllocationLive { .. }
                        | ResourceObligationKind::PermissionAvailable { .. }
                )
        })
    }));
    assert!(matches!(
        interpret(double_drop.runtime())
            .expect_err("double drop must fault")
            .kind(),
        VirExecutionErrorKind::UseAfterFree { .. }
            | VirExecutionErrorKind::DoubleFree { .. }
            | VirExecutionErrorKind::PermissionAlreadyConsumed(_)
    ));
}

#[test]
fn precision_budgets_are_deterministic_and_never_grant_authority() {
    let source = include_str!("../spec/cases/verify/resource-acceptance.nera");
    let output = accepted("resource-budget.nera", source);
    let resolved = output
        .vir()
        .expect("resource budget source has VIR")
        .resolve()
        .expect("resource budget VIR resolves");
    for config in [
        CfgAnalysisConfig {
            max_guarded_cases_per_block: 1,
            ..CfgAnalysisConfig::default()
        },
        CfgAnalysisConfig {
            max_guard_atoms_per_case: 0,
            ..CfgAnalysisConfig::default()
        },
    ] {
        let first = verify_program(&resolved, config).expect("budgeted verification converges");
        let second = verify_program(&resolved, config).expect("budgeted verification replays");
        assert_eq!(first, second);
        assert!(!first.is_memory_checked_core0());
        assert!(first.functions().values().any(|function| {
            function
                .cfg()
                .guarded_precision_losses()
                .values()
                .any(|losses| {
                    losses.contains(&GuardedStatePrecisionLoss::CaseBudget)
                        || losses.contains(&GuardedStatePrecisionLoss::GuardAtomBudget)
                })
        }));
        assert!(first.functions().values().any(|function| {
            function
                .cfg()
                .obligations()
                .iter()
                .any(|record| record.obligation().status() != ObligationStatus::Proven)
        }));
    }
}
