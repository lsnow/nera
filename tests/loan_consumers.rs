#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
use nera::backend::X86_64SystemToolchain;
use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64InstructionPlan, X86_64PlanningErrorKind};
use nera::{
    CfgAnalysisConfig, SpannedVirTerminator, VirBasicBlock, VirBlockId, VirBlockTarget,
    VirBorrowEnvironment, VirBorrowRegionOrigin, VirBorrowRegionScope, VirConstant,
    VirExecutionErrorKind, VirInstruction, VirInterpreterConfig, VirLoanId, VirLoanKind,
    VirTargetDataLayout, VirTerminator, VirType, VirValueId, interpret, interpret_with_config,
    verify_program,
};

#[path = "support/loan_program.rs"]
mod loan_program;

fn execution_error(unit: nera::VirUnit, config: VirInterpreterConfig) -> VirExecutionErrorKind {
    let validated = unit.into_validated().expect("loan fixture validates");
    let resolved = validated.resolve().expect("loan fixture resolves");
    interpret_with_config(resolved.runtime(), config)
        .expect_err("fixture must fault in the runtime loan shadow")
        .kind()
        .clone()
}

fn nested_reborrow() -> nera::VirUnit {
    let mut instructions = loan_program::allocation_prefix();
    instructions.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::LoanReborrow {
                effect: loan_program::effect(1, VirLoanKind::Shared, 1, Some(0), 4, 5),
                reference_result: loan_program::pointer(6),
                permission_result: loan_program::permission(7),
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::Load {
                result: loan_program::value(8, VirType::U64),
                pointer: VirValueId::new(6),
                permission: VirValueId::new(7),
                access: loan_program::U64_ACCESS,
            },
        ),
        loan_program::spanned(
            7,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(1, VirLoanKind::Shared, 1, Some(0), 6, 7),
            },
        ),
        loan_program::spanned(
            8,
            VirInstruction::Store {
                pointer: VirValueId::new(4),
                value: VirValueId::new(3),
                permission: VirValueId::new(5),
                access: loan_program::U64_ACCESS,
            },
        ),
        loan_program::spanned(
            9,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 4, 5),
            },
        ),
        loan_program::spanned(
            10,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);
    loan_program::unit(instructions, 2)
}

#[test]
fn verified_shared_and_mutable_lifecycles_reach_interpreter_and_native() {
    let shared = loan_program::shared_lifecycle()
        .into_validated()
        .expect("shared lifecycle validates");
    let shared = shared.resolve().expect("shared lifecycle resolves");
    assert!(
        verify_program(&shared, CfgAnalysisConfig::default())
            .expect("shared lifecycle verifies")
            .is_memory_checked_core0()
    );
    interpret(shared.runtime()).expect("shared aliases execute and end");
    let shared_plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(shared.runtime())
        .expect("shared loan lowers to a native plan");
    let plans = shared_plan.functions()[0].blocks()[0].instructions();
    assert_eq!(
        plans
            .iter()
            .filter(|plan| plan == &&X86_64InstructionPlan::LoanReference)
            .count(),
        2
    );
    assert_eq!(
        plans
            .iter()
            .filter(|plan| plan == &&X86_64InstructionPlan::ErasedLoan)
            .count(),
        2
    );
    X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(shared.runtime())
        .expect("reference pointer copies are selectable");

    let mut mutable = loan_program::allocation_prefix();
    mutable.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::Store {
                pointer: VirValueId::new(4),
                value: VirValueId::new(3),
                permission: VirValueId::new(5),
                access: loan_program::U64_ACCESS,
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 4, 5),
            },
        ),
        loan_program::spanned(
            7,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);
    let mutable = loan_program::unit(mutable, 1)
        .into_validated()
        .expect("mutable lifecycle validates");
    let mutable = mutable.resolve().expect("mutable lifecycle resolves");
    assert!(
        verify_program(&mutable, CfgAnalysisConfig::default())
            .expect("mutable lifecycle verifies")
            .is_memory_checked_core0()
    );
    interpret(mutable.runtime()).expect("mutable reference store executes");

    let nested = nested_reborrow()
        .into_validated()
        .expect("nested reborrow validates");
    let nested = nested.resolve().expect("nested reborrow resolves");
    assert!(
        verify_program(&nested, CfgAnalysisConfig::default())
            .expect("nested reborrow verifies")
            .is_memory_checked_core0()
    );
    interpret(nested.runtime()).expect("ending a child restores its parent authority");
}

#[test]
fn runtime_shadow_faults_on_borrowed_free_double_end_and_missing_end() {
    let mut borrowed_free = loan_program::allocation_prefix();
    borrowed_free.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);
    assert_eq!(
        execution_error(
            loan_program::unit(borrowed_free, 1),
            VirInterpreterConfig::default()
        ),
        VirExecutionErrorKind::LoanAccessConflict {
            loan: VirLoanId::new(0),
            permission: VirValueId::new(2),
        }
    );

    let mut double_end = loan_program::allocation_prefix();
    double_end.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 4, 5),
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 4, 5),
            },
        ),
    ]);
    assert_eq!(
        execution_error(
            loan_program::unit(double_end, 1),
            VirInterpreterConfig::default()
        ),
        VirExecutionErrorKind::LoanInactive {
            loan: VirLoanId::new(0)
        }
    );

    let mut missing_end = loan_program::allocation_prefix();
    missing_end.push(loan_program::spanned(
        4,
        VirInstruction::LoanBegin {
            effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
            reference_result: loan_program::pointer(4),
            permission_result: loan_program::permission(5),
        },
    ));
    assert_eq!(
        execution_error(
            loan_program::unit(missing_end, 1),
            VirInterpreterConfig::default()
        ),
        VirExecutionErrorKind::LoanNotEnded {
            loan: VirLoanId::new(0)
        }
    );
}

#[test]
fn runtime_shadow_rejects_wrong_parent_and_dynamic_range_mismatch() {
    let mut wrong_parent = loan_program::allocation_prefix();
    wrong_parent.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(1, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: loan_program::pointer(6),
                permission_result: loan_program::permission(7),
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::LoanReborrow {
                effect: loan_program::effect(2, VirLoanKind::Shared, 1, Some(0), 6, 7),
                reference_result: loan_program::pointer(8),
                permission_result: loan_program::permission(9),
            },
        ),
    ]);
    assert_eq!(
        execution_error(
            loan_program::unit(wrong_parent, 2),
            VirInterpreterConfig::default()
        ),
        VirExecutionErrorKind::LoanParentMismatch {
            loan: VirLoanId::new(2),
            parent: VirLoanId::new(0),
        }
    );

    let mut wrong_range = loan_program::allocation_prefix();
    wrong_range.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::Constant {
                result: loan_program::value(6, VirType::U64),
                value: VirConstant::U64(8),
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::PointerOffset {
                result: loan_program::pointer(7),
                base: VirValueId::new(4),
                delta_bytes: VirValueId::new(6),
            },
        ),
        loan_program::spanned(
            7,
            VirInstruction::LoanReborrow {
                effect: loan_program::effect(1, VirLoanKind::Shared, 1, Some(0), 7, 5),
                reference_result: loan_program::pointer(8),
                permission_result: loan_program::permission(9),
            },
        ),
    ]);
    assert_eq!(
        execution_error(
            loan_program::unit(wrong_range, 2),
            VirInterpreterConfig::default()
        ),
        VirExecutionErrorKind::LoanRangeViolation {
            loan: VirLoanId::new(1)
        }
    );
}

#[test]
fn runtime_shadow_limits_fail_before_granting_authority() {
    assert_eq!(
        execution_error(
            loan_program::shared_lifecycle(),
            VirInterpreterConfig {
                max_active_loans: 0,
                ..VirInterpreterConfig::default()
            }
        ),
        VirExecutionErrorKind::ActiveLoanLimitExceeded { limit: 0 }
    );
    assert_eq!(
        execution_error(
            loan_program::shared_lifecycle(),
            VirInterpreterConfig {
                max_aliases_per_loan: 1,
                ..VirInterpreterConfig::default()
            }
        ),
        VirExecutionErrorKind::LoanAliasLimitExceeded {
            loan: VirLoanId::new(0),
            limit: 1,
        }
    );
    assert_eq!(
        execution_error(
            nested_reborrow(),
            VirInterpreterConfig {
                max_reborrow_depth: 0,
                ..VirInterpreterConfig::default()
            }
        ),
        VirExecutionErrorKind::LoanReborrowDepthLimitExceeded {
            loan: VirLoanId::new(1),
            limit: 0,
        }
    );
}

#[test]
fn permission_move_preserves_hidden_runtime_authority() {
    let mut instructions = loan_program::allocation_prefix();
    instructions.extend([
        loan_program::spanned(
            4,
            VirInstruction::LoanBegin {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 1, 2),
                reference_result: loan_program::pointer(4),
                permission_result: loan_program::permission(5),
            },
        ),
        loan_program::spanned(
            5,
            VirInstruction::PermissionMove {
                result: loan_program::permission(6),
                source: VirValueId::new(5),
            },
        ),
        loan_program::spanned(
            6,
            VirInstruction::Store {
                pointer: VirValueId::new(4),
                value: VirValueId::new(3),
                permission: VirValueId::new(6),
                access: loan_program::U64_ACCESS,
            },
        ),
        loan_program::spanned(
            7,
            VirInstruction::LoanEnd {
                effect: loan_program::effect(0, VirLoanKind::Mutable, 0, None, 4, 6),
            },
        ),
        loan_program::spanned(
            8,
            VirInstruction::Free {
                pointer: VirValueId::new(1),
                permission: VirValueId::new(2),
            },
        ),
    ]);
    let validated = loan_program::unit(instructions, 1)
        .into_validated()
        .expect("permission-move loan validates");
    let resolved = validated.resolve().expect("permission-move loan resolves");
    interpret(resolved.runtime()).expect("moved authority can access and end its loan");
}

#[test]
fn block_arguments_rename_hidden_runtime_authority() {
    let mut first_instructions = loan_program::allocation_prefix();
    first_instructions.push(loan_program::spanned(
        4,
        VirInstruction::LoanBegin {
            effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 1, 2),
            reference_result: loan_program::pointer(4),
            permission_result: loan_program::permission(5),
        },
    ));
    let mut unit = loan_program::unit(first_instructions.clone(), 1);
    let original = unit.runtime.functions[0].blocks[0].clone();
    unit.runtime.functions[0].blocks = vec![
        VirBasicBlock {
            id: VirBlockId::new(0),
            parameters: Vec::new(),
            instructions: first_instructions,
            terminator: SpannedVirTerminator {
                terminator: VirTerminator::Jump {
                    target: VirBlockTarget {
                        block: VirBlockId::new(1),
                        arguments: vec![
                            VirValueId::new(4),
                            VirValueId::new(5),
                            VirValueId::new(1),
                            VirValueId::new(2),
                        ],
                    },
                },
                source_span: original.terminator.source_span,
            },
            source_span: original.source_span,
        },
        VirBasicBlock {
            id: VirBlockId::new(1),
            parameters: vec![
                loan_program::pointer(10),
                loan_program::permission(11),
                loan_program::pointer(12),
                loan_program::permission(13),
            ],
            instructions: vec![
                loan_program::spanned(
                    5,
                    VirInstruction::LoanEnd {
                        effect: loan_program::effect(0, VirLoanKind::Shared, 0, None, 10, 11),
                    },
                ),
                loan_program::spanned(
                    6,
                    VirInstruction::Free {
                        pointer: VirValueId::new(12),
                        permission: VirValueId::new(13),
                    },
                ),
            ],
            terminator: original.terminator,
            source_span: original.source_span,
        },
    ];
    let mut regions = unit.borrows.regions().to_vec();
    regions[0].scope = VirBorrowRegionScope::Blocks(vec![VirBlockId::new(0), VirBlockId::new(1)]);
    unit.borrows = VirBorrowEnvironment::from_tables(regions, unit.borrows.constraints().to_vec());
    unit.rebuild_source_map_from_runtime("block-authority.nera", 128);

    let validated = unit.into_validated().expect("two-block loan validates");
    let resolved = validated.resolve().expect("two-block loan resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("two-block loan verifies")
            .is_memory_checked_core0()
    );
    interpret(resolved.runtime()).expect("block parameter keeps the dynamic authority token");
}

#[test]
fn verified_region_metadata_is_non_interfering_for_runtime_and_native() {
    let baseline = loan_program::shared_lifecycle();
    let mut enriched = baseline.clone();
    let mut regions = enriched.borrows.regions().to_vec();
    regions[0].origin = VirBorrowRegionOrigin::Lexical;
    enriched.borrows =
        VirBorrowEnvironment::from_tables(regions, enriched.borrows.constraints().to_vec());
    assert_ne!(baseline.stable_dump(), enriched.stable_dump());

    let baseline = baseline
        .into_validated()
        .expect("baseline loan unit validates");
    let enriched = enriched
        .into_validated()
        .expect("metadata-enriched loan unit validates");
    let baseline = baseline.resolve().expect("baseline resolves");
    let enriched = enriched.resolve().expect("enriched resolves");
    assert!(
        verify_program(&baseline, CfgAnalysisConfig::default())
            .expect("baseline verifies")
            .is_memory_checked_core0()
    );
    assert!(
        verify_program(&enriched, CfgAnalysisConfig::default())
            .expect("enriched verifies")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(baseline.runtime()).expect("baseline executes"),
        interpret(enriched.runtime()).expect("enriched executes")
    );
    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU
            .plan_program(baseline.runtime())
            .expect("baseline plans"),
        X86_64_UNKNOWN_LINUX_GNU
            .plan_program(enriched.runtime())
            .expect("enriched plans")
    );
    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(baseline.runtime())
            .expect("baseline lowers"),
        X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(enriched.runtime())
            .expect("enriched lowers")
    );
}

#[test]
fn loan_erasure_does_not_bypass_the_native_target_boundary() {
    let mut foreign = loan_program::shared_lifecycle();
    foreign.memory.target = VirTargetDataLayout {
        usize_size_bytes: 4,
        usize_alignment: 4,
        ..foreign.memory.target
    };
    let foreign = foreign
        .into_validated()
        .expect("foreign abstract target is structurally valid");
    let foreign = foreign.resolve().expect("foreign target resolves");
    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU
            .plan_program(foreign.runtime())
            .expect_err("x86_64 backend still rejects a foreign layout")
            .kind(),
        &X86_64PlanningErrorKind::UnsupportedMemoryTarget
    );
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
fn verified_loan_execution_matches_a_real_native_process() {
    use std::process::Command;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_ARTIFACT: AtomicU64 = AtomicU64::new(0);

    let validated = loan_program::shared_lifecycle()
        .into_validated()
        .expect("native loan fixture validates");
    let resolved = validated.resolve().expect("native loan fixture resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("native loan fixture verifies first")
            .is_memory_checked_core0()
    );
    let execution = interpret(resolved.runtime()).expect("loan fixture interprets");
    assert!(execution.values().is_empty());

    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("verified loan fixture lowers");
    let assembly = X86_64_UNKNOWN_LINUX_GNU
        .emit_assembly(&machine)
        .expect("verified loan assembly emits");
    let artifact = std::env::temp_dir().join(format!(
        "nera-stage725-{}-{}",
        std::process::id(),
        NEXT_ARTIFACT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&artifact).expect("unique native artifact directory is created");
    let executable = artifact.join("loan-program");
    X86_64SystemToolchain::default()
        .build_executable(&assembly, &executable)
        .expect("system assembler and linker accept the erased loan program");
    let status = Command::new(&executable)
        .status()
        .expect("native loan executable starts");
    assert_eq!(status.code(), Some(0));
    std::fs::remove_dir_all(&artifact).expect("native loan artifact is removed");
}
