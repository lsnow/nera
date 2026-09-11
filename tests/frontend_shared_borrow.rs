use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64InstructionPlan};
use nera::{
    CfgAnalysisConfig, FrontendStatus, HirRegionOrigin, SourceFile, VirExecutionErrorKind,
    VirGeneratedReason, VirInstruction, VirLoanRange, VirOriginKind, VirRuntimeValue, analyze,
    interpret, verify_program,
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
fn local_shared_borrow_alias_reaches_every_runtime_consumer() {
    let source = "fn main() -> u64 {
        let value = 41;
        let borrowed: &u64 = &value;
        let alias = borrowed;
        return *alias + *borrowed;
    }";
    let output = accepted("local-shared-alias.nera", source);
    let hir = output.hir().expect("accepted source has typed HIR");
    assert_eq!(hir.regions().len(), 1);
    assert!(matches!(
        hir.regions()[0].origin,
        HirRegionOrigin::Inferred { .. }
    ));

    let vir = output.vir().expect("accepted source has validated VIR");
    assert_eq!(vir.as_unit().borrows.regions().len(), 1);
    let instructions = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect::<Vec<_>>();
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(
                instruction.instruction,
                VirInstruction::LoanBegin { .. }
            ))
            .count(),
        1
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(
                instruction.instruction,
                VirInstruction::LoanAliasShared { .. }
            ))
            .count(),
        1
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(instruction.instruction, VirInstruction::LoanEnd { .. }))
            .count(),
        2
    );
    for instruction in instructions.iter().filter(|instruction| {
        matches!(
            instruction.instruction,
            VirInstruction::LoanBegin { .. }
                | VirInstruction::LoanAliasShared { .. }
                | VirInstruction::LoanEnd { .. }
        )
    }) {
        let effect = match &instruction.instruction {
            VirInstruction::LoanBegin { effect, .. }
            | VirInstruction::LoanAliasShared { effect, .. }
            | VirInstruction::LoanEnd { effect } => effect,
            _ => unreachable!(),
        };
        assert!(matches!(
            vir.as_unit()
                .source_map
                .origin(effect.origin)
                .map(|origin| &origin.kind),
            Some(VirOriginKind::Generated {
                reason: VirGeneratedReason::LoanEffect,
                ..
            })
        ));
    }

    let resolved = vir.resolve().expect("shared-borrow VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("shared-borrow verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("shared aliases execute")
            .values(),
        [VirRuntimeValue::U64(82)]
    );
    let native = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("source-generated loans reach native planning");
    let plans = native.functions()[0]
        .blocks()
        .iter()
        .flat_map(|block| block.instructions())
        .collect::<Vec<_>>();
    assert_eq!(
        plans
            .iter()
            .filter(|plan| plan == &&&X86_64InstructionPlan::LoanReference)
            .count(),
        2
    );
}

#[test]
fn overlapping_shared_subobject_borrows_and_field_auto_deref_are_safe() {
    let source = "struct Pair { left: u64, right: u64, }
        fn main() -> u64 {
            let pair = Pair { left: 3, right: 5 };
            let whole = &pair;
            let left = &pair.left;
            let alias = whole;
            return alias.right + *left;
        }";
    let output = accepted("overlapping-shared.nera", source);
    let vir = output.vir().expect("overlapping shared source has VIR");
    let mut begin_ranges = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction.instruction {
            VirInstruction::LoanBegin { ref effect, .. } => Some(effect.range),
            _ => None,
        })
        .collect::<Vec<_>>();
    begin_ranges.sort_by_key(|range| (range.start_bytes, range.end_bytes));
    assert_eq!(
        begin_ranges,
        [
            VirLoanRange {
                start_bytes: 0,
                end_bytes: 8,
            },
            VirLoanRange {
                start_bytes: 0,
                end_bytes: 16,
            },
        ]
    );

    let resolved = vir.resolve().expect("overlapping shared VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("overlapping shared verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("overlapping shared loans execute")
            .values(),
        [VirRuntimeValue::U64(8)]
    );
}

#[test]
fn lexical_end_restores_owner_write_authority() {
    let source = "fn main() -> u64 {
        let mut value = 1;
        {
            let borrowed = &value;
            let copy = value;
            let seen = *borrowed + copy;
        }
        value = 2;
        return value;
    }";
    let output = accepted("lexical-shared-end.nera", source);
    let vir = output.vir().expect("lexical shared source has VIR");
    let instructions = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.instruction)
        .collect::<Vec<_>>();
    let end = instructions
        .iter()
        .position(|instruction| matches!(instruction, VirInstruction::LoanEnd { .. }))
        .expect("nested scope emits a loan end");
    let update = instructions
        .iter()
        .rposition(|instruction| matches!(instruction, VirInstruction::Store { .. }))
        .expect("owner update lowers to a store");
    assert!(end < update);

    let resolved = vir.resolve().expect("lexical shared VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("lexical shared verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("owner write after lexical end executes")
            .values(),
        [VirRuntimeValue::U64(2)]
    );
}

#[test]
fn owner_write_and_free_remain_refuted_while_shared_borrow_is_live() {
    let cases = [
        (
            "borrowed-write.nera",
            "fn main() -> u64 {
                let mut value = 1;
                let borrowed = &value;
                value = 2;
                return *borrowed;
            }",
        ),
        (
            "borrowed-free.nera",
            "fn main() -> u64 {
                let owner = alloc<u64>(1);
                *owner = 7;
                let borrowed = &*owner;
                free(owner);
                return *borrowed;
            }",
        ),
    ];

    for (name, source) in cases {
        let output = accepted(name, source);
        let resolved = output
            .vir()
            .expect("conflicting source has VIR")
            .resolve()
            .expect("conflicting VIR resolves");
        let verification = verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("conflicting verification converges");
        assert!(
            !verification.is_memory_checked_core0(),
            "{name} must not verify"
        );
        assert!(matches!(
            interpret(resolved.runtime())
                .expect_err("the concrete conflicting path must fault")
                .kind(),
            VirExecutionErrorKind::LoanAccessConflict { .. }
        ));
    }
}

#[test]
fn dynamic_index_borrow_uses_the_bounded_array_candidate_range() {
    let source = "fn main() -> u64 {
        let values = [3, 5];
        let index = 1usize;
        let borrowed = &values[index];
        return *borrowed;
    }";
    let output = accepted("dynamic-borrow.nera", source);
    let vir = output.vir().expect("dynamic borrow has VIR");
    let effect = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match instruction.instruction {
            VirInstruction::LoanBegin { effect, .. } => Some(effect),
            _ => None,
        })
        .expect("dynamic borrow emits a loan");
    assert_eq!(
        effect.range,
        VirLoanRange {
            start_bytes: 0,
            end_bytes: 16,
        }
    );
    let resolved = vir.resolve().expect("dynamic borrow VIR resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("dynamic borrow verification converges")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("dynamic borrow executes")
            .values(),
        [VirRuntimeValue::U64(5)]
    );
}

#[test]
fn shared_borrows_follow_branch_early_exit_and_loop_cfg() {
    let cases = [
        (
            "branch-borrow.nera",
            "fn main() -> u64 {
                let value = 7;
                if true {
                    let borrowed = &value;
                    return *borrowed;
                }
                return 0;
            }",
            7,
        ),
        (
            "loop-borrow.nera",
            "fn main() -> u64 {
                let mut value = 7;
                let mut total = 0;
                for index in 0..2 {
                    let borrowed = &value;
                    total = total + *borrowed + index;
                    value = value + 1;
                }
                return total;
            }",
            16,
        ),
        (
            "continue-borrow.nera",
            "fn main() -> u64 {
                let value = 7;
                let mut total = 0;
                for index in 0..3 {
                    let borrowed = &value;
                    if index == 0 {
                        continue;
                    }
                    total = total + *borrowed;
                }
                return total;
            }",
            14,
        ),
        (
            "while-borrow.nera",
            "fn main() -> u64 {
                let mut value = 1;
                let mut total = 0;
                while value < 3 {
                    let borrowed = &value;
                    total = total + *borrowed;
                    value = value + 1;
                }
                return total;
            }",
            3,
        ),
        (
            "match-borrow.nera",
            "fn main() -> u64 {
                let mut value = 5;
                let mut total = 0;
                match value == 5 {
                    true => {
                        let borrowed = &value;
                        total = *borrowed;
                    },
                    false => {
                        let borrowed = &value;
                        total = *borrowed + 1;
                    },
                }
                value = 7;
                return total + value;
            }",
            12,
        ),
    ];

    for (name, source, expected) in cases {
        let output = accepted(name, source);
        let resolved = output
            .vir()
            .expect("borrow CFG has VIR")
            .resolve()
            .expect("borrow CFG resolves");
        let verification = verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("borrow CFG verification converges");
        assert!(
            verification.is_memory_checked_core0(),
            "{name}: {:#?}",
            verification.diagnostics()
        );
        assert_eq!(
            interpret(resolved.runtime())
                .expect("borrow CFG executes")
                .values(),
            [VirRuntimeValue::U64(expected)]
        );
        X86_64_UNKNOWN_LINUX_GNU
            .plan_program(resolved.runtime())
            .expect("borrow CFG reaches native planning");
    }
}

#[test]
fn mutable_borrow_is_a_stable_loop_carried_resource() {
    let output = accepted(
        "loop-carried-mutable-borrow.nera",
        "fn main() -> u64 {
            let mut value = 0;
            let borrowed = &mut value;
            for index in 0..3 {
                let child = &mut *borrowed;
                *child = *child + index;
                *borrowed = *borrowed + 1;
            }
            return *borrowed;
        }",
    );
    let resolved = output
        .vir()
        .expect("loop-carried borrow has VIR")
        .resolve()
        .expect("loop-carried borrow resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("loop-carried borrow verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("loop-carried mutable borrow executes")
            .values(),
        [VirRuntimeValue::U64(6)]
    );
    X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("loop-carried mutable borrow reaches native planning");
}
