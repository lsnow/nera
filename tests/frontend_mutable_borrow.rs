use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64InstructionPlan};
use nera::{
    CfgAnalysisConfig, FrontendStatus, HirMutability, HirTypeKind, SourceFile, ValueCapability,
    VirExecutionErrorKind, VirInstruction, VirLoanKind, VirLoanRange, VirRuntimeValue, analyze,
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
fn local_mutable_borrow_moves_once_and_reaches_every_runtime_consumer() {
    let source = "fn main() -> u64 {
        let mut value = 7;
        let unique: &mut u64 = &mut value;
        *unique = 41;
        let moved: &mut u64 = unique;
        *moved = 42;
        return *moved;
    }";
    let output = accepted("local-mutable-borrow.nera", source);
    let hir = output.hir().expect("accepted source has typed HIR");
    let mutable_reference = hir
        .types()
        .iter()
        .find(|definition| {
            matches!(
                definition.kind,
                HirTypeKind::Reference {
                    mutability: HirMutability::Mutable,
                    ..
                }
            )
        })
        .expect("mutable reference type is interned");
    assert_eq!(
        hir.type_capabilities(mutable_reference.id)
            .expect("mutable reference capabilities")
            .value,
        ValueCapability::MoveOnly
    );

    let vir = output.vir().expect("accepted source has validated VIR");
    let instructions = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.instruction)
        .collect::<Vec<_>>();
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(
                instruction,
                VirInstruction::LoanBegin { effect, .. }
                    if effect.kind == VirLoanKind::Mutable
            ))
            .count(),
        1
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(instruction, VirInstruction::PermissionMove { .. }))
            .count(),
        1
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(instruction, VirInstruction::LoanAliasShared { .. }))
            .count(),
        0
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(instruction, VirInstruction::LoanEnd { .. }))
            .count(),
        1
    );

    let resolved = vir.resolve().expect("mutable-borrow VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("mutable-borrow verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("mutable reference writes execute")
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    let native = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("mutable reference reaches native planning");
    assert!(
        native.functions()[0]
            .blocks()
            .iter()
            .flat_map(|block| block.instructions())
            .any(|plan| plan == &X86_64InstructionPlan::LoanReference)
    );
}

#[test]
fn mutable_subobject_borrow_allows_disjoint_owner_access_and_restores_parent() {
    let source = "struct Pair { left: u64, right: u64, }
        fn main() -> u64 {
            let mut pair = Pair { left: 3, right: 5 };
            {
                let left = &mut pair.left;
                *left = 7;
                let during = *left + pair.right;
            }
            pair.left = pair.left + 1;
            return pair.left + pair.right;
        }";
    let output = accepted("mutable-subobject.nera", source);
    let vir = output.vir().expect("mutable subobject source has VIR");
    let begin = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match &instruction.instruction {
            VirInstruction::LoanBegin { effect, .. } => Some(effect),
            _ => None,
        })
        .expect("mutable loan begins");
    assert_eq!(begin.kind, VirLoanKind::Mutable);
    assert_eq!(
        begin.range,
        VirLoanRange {
            start_bytes: 0,
            end_bytes: 8,
        }
    );

    let resolved = vir.resolve().expect("mutable subobject VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("mutable subobject verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("disjoint access and restored owner execute")
            .values(),
        [VirRuntimeValue::U64(13)]
    );
}

#[test]
fn mutable_reference_updates_bool_and_whole_aggregate_values() {
    let cases = [
        (
            "mutable-bool.nera",
            "fn main() -> bool {
                let mut flag = true;
                let unique = &mut flag;
                *unique = false;
                return *unique;
            }",
            VirRuntimeValue::Bool(false),
        ),
        (
            "mutable-whole-aggregate.nera",
            "struct Pair { left: u64, right: u64, }
             fn main() -> u64 {
                let mut pair = Pair { left: 1, right: 2 };
                let unique: &mut Pair = &mut pair;
                *unique = Pair { left: 5, right: 7 };
                unique.left = 6;
                return unique.left + unique.right;
             }",
            VirRuntimeValue::U64(13),
        ),
    ];

    for (name, source, expected) in cases {
        let output = accepted(name, source);
        let resolved = output
            .vir()
            .expect("typed mutable reference has VIR")
            .resolve()
            .expect("typed mutable-reference VIR resolves");
        assert!(
            verify_program(&resolved, CfgAnalysisConfig::default())
                .expect("typed mutable-reference verification converges")
                .is_memory_checked_core0(),
            "{name}"
        );
        assert_eq!(
            interpret(resolved.runtime())
                .expect("typed mutable-reference update executes")
                .values(),
            [expected],
            "{name}"
        );
    }
}

#[test]
fn active_mutable_loan_rejects_owner_access_and_overlapping_loans() {
    let cases = [
        (
            "mutable-owner-read.nera",
            "fn main() -> u64 {
                let mut value = 1;
                let unique = &mut value;
                let bypass = value;
                return *unique + bypass;
            }",
        ),
        (
            "mutable-owner-write.nera",
            "fn main() -> u64 {
                let mut value = 1;
                let unique = &mut value;
                value = 2;
                return *unique;
            }",
        ),
        (
            "mutable-overlapping-shared.nera",
            "fn main() -> u64 {
                let mut value = 1;
                let unique = &mut value;
                let shared = &value;
                return *unique + *shared;
            }",
        ),
        (
            "mutable-overlapping-mutable.nera",
            "fn main() -> u64 {
                let mut value = 1;
                let first = &mut value;
                let second = &mut value;
                return *first + *second;
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
        let error =
            interpret(resolved.runtime()).expect_err("the concrete conflicting path must fault");
        assert!(
            matches!(
                error.kind(),
                VirExecutionErrorKind::LoanAccessConflict { .. }
                    | VirExecutionErrorKind::LoanConflict { .. }
            ),
            "{name}: {error:?}"
        );
    }
}

#[test]
fn mutable_borrow_requires_a_writable_place_and_shared_reference_stays_read_only() {
    let cases = [
        (
            "immutable-mutable-borrow.nera",
            "fn main() -> u64 {
                let value = 1;
                let unique = &mut value;
                return *unique;
            }",
        ),
        (
            "shared-reference-write.nera",
            "fn main() -> u64 {
                let mut value = 1;
                let shared = &value;
                *shared = 2;
                return *shared;
            }",
        ),
    ];
    for (name, source) in cases {
        let output = analyze(&SourceFile::from_text(name, source));
        assert_eq!(
            output.status(),
            FrontendStatus::Invalid,
            "{name}: {:?}",
            output.issues()
        );
        assert!(output.vir().is_none());
    }
}

#[test]
fn mutable_reference_cannot_be_used_after_its_move() {
    let source = "fn main() -> u64 {
        let mut value = 1;
        let unique = &mut value;
        let moved = unique;
        return *unique + *moved;
    }";
    let output = analyze(&SourceFile::from_text(
        "mutable-use-after-move.nera",
        source,
    ));
    assert_eq!(
        output.status(),
        FrontendStatus::Invalid,
        "issues: {:?}",
        output.issues()
    );
    assert!(output.vir().is_none());
}

#[test]
fn mutable_borrow_from_owner_dereference_ends_before_free() {
    let source = "fn main() -> u64 {
        let owner = alloc<u64>(1);
        *owner = 1;
        {
            let unique = &mut *owner;
            *unique = 9;
        }
        let observed = *owner;
        free(owner);
        return observed;
    }";
    let output = accepted("mutable-owner-pointee.nera", source);
    let resolved = output
        .vir()
        .expect("owner-pointee borrow has VIR")
        .resolve()
        .expect("owner-pointee VIR resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("owner-pointee verification converges")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("owner-pointee mutation executes")
            .values(),
        [VirRuntimeValue::U64(9)]
    );
}
