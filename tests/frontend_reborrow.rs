use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64InstructionPlan};
use nera::{
    CfgAnalysisConfig, FrontendStatus, HirExpressionKind, HirProgram, HirProgramTables,
    HirProjectionKind, HirStatementKind, SourceFile, VirExecutionErrorKind, VirInstruction,
    VirLoanId, VirLoanKind, VirLoanRange, VirRuntimeValue, analyze, interpret, verify_program,
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

fn program_tables(program: &HirProgram) -> HirProgramTables {
    HirProgramTables {
        data_layout: program.data_layout(),
        entry_module: program.entry_module_id(),
        entry_function: program.entry_function_id(),
        modules: program.modules().to_vec(),
        types: program.types().to_vec(),
        type_capabilities: program.type_capability_table().to_vec(),
        layouts: program.layouts().to_vec(),
        fields: program.fields().to_vec(),
        variants: program.variants().to_vec(),
        generic_parameters: program.generic_parameters().to_vec(),
        regions: program.regions().to_vec(),
        region_constraints: program.region_constraints().to_vec(),
        functions: program.functions().to_vec(),
        contracts: program.contracts().to_vec(),
        predicates: program.predicates().to_vec(),
        specs: program.specs().clone(),
    }
}

#[test]
fn mutable_subobject_reborrow_has_explicit_hir_and_precise_vir_parent() {
    let source = "struct Pair { left: u64, right: u64, }
        fn main() -> u64 {
            let mut pair = Pair { left: 3, right: 5 };
            let parent = &mut pair;
            {
                let child = &mut parent.left;
                *child = 7;
            }
            parent.right = 11;
            return parent.left + parent.right;
        }";
    let output = accepted("mutable-subobject-reborrow.nera", source);
    let hir = output.hir().expect("accepted source has HIR");
    assert_eq!(hir.regions().len(), 2);
    assert_eq!(hir.region_constraints().len(), 1);
    assert_eq!(hir.region_constraints()[0].subregion, hir.regions()[1].id);
    assert_eq!(hir.region_constraints()[0].superregion, hir.regions()[0].id);

    let body = hir.functions()[0].body().expect("main has a body");
    let HirStatementKind::Block { block } = &body.root.statements[2].kind else {
        panic!("child reborrow is in a nested block");
    };
    let HirStatementKind::Let { value, .. } = &block.statements[0].kind else {
        panic!("nested block begins with child binding");
    };
    let HirExpressionKind::Borrow { place, .. } = &value.kind else {
        panic!("child initializer is an explicit HIR borrow");
    };
    assert!(matches!(
        place.projections.first().map(|projection| &projection.kind),
        Some(HirProjectionKind::Dereference)
    ));

    let vir = output.vir().expect("accepted source has VIR");
    let effects = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match &instruction.instruction {
            VirInstruction::LoanBegin { effect, .. }
            | VirInstruction::LoanReborrow { effect, .. } => Some(*effect),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(effects.len(), 2);
    assert_eq!(effects[0].loan, VirLoanId::new(0));
    assert_eq!(effects[0].parent, None);
    assert_eq!(effects[1].loan, VirLoanId::new(1));
    assert_eq!(effects[1].parent, Some(VirLoanId::new(0)));
    assert_eq!(effects[1].kind, VirLoanKind::Mutable);
    assert_eq!(
        effects[1].range,
        VirLoanRange {
            start_bytes: 0,
            end_bytes: 8,
        }
    );
    assert_eq!(vir.as_unit().borrows.constraints().len(), 1);

    let resolved = vir.resolve().expect("reborrow VIR resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("reborrow verification converges")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("child end restores parent")
            .values(),
        [VirRuntimeValue::U64(18)]
    );
    let native = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("verified reborrow reaches native planning");
    assert_eq!(
        native.functions()[0]
            .blocks()
            .iter()
            .flat_map(|block| block.instructions())
            .filter(|instruction| instruction == &&X86_64InstructionPlan::LoanReference)
            .count(),
        2
    );
}

#[test]
fn shared_child_aliases_end_before_the_shared_parent_is_restored() {
    let source = "fn main() -> u64 {
        let value = 21;
        let parent = &value;
        {
            let child = &*parent;
            let alias = child;
            let observed = *child + *alias;
        }
        return *parent;
    }";
    let output = accepted("shared-reborrow-alias.nera", source);
    let vir = output.vir().expect("shared reborrow has VIR");
    let instructions = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.instruction)
        .collect::<Vec<_>>();
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(instruction, VirInstruction::LoanReborrow { .. }))
            .count(),
        1
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(instruction, VirInstruction::LoanAliasShared { .. }))
            .count(),
        1
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(instruction, VirInstruction::LoanEnd { .. }))
            .count(),
        3
    );

    let resolved = vir.resolve().expect("shared reborrow VIR resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("shared reborrow verification converges")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("all child aliases end before parent use")
            .values(),
        [VirRuntimeValue::U64(21)]
    );
}

#[test]
fn nested_reborrow_restores_each_parent_in_order() {
    let source = "fn main() -> u64 {
        let mut value = 1;
        let parent = &mut value;
        {
            let child = &mut *parent;
            {
                let grandchild = &*child;
                let observed = *grandchild;
            }
            *child = 9;
        }
        return *parent;
    }";
    let output = accepted("nested-reborrow.nera", source);
    let hir = output.hir().expect("nested reborrow has HIR");
    assert_eq!(hir.regions().len(), 3);
    assert_eq!(hir.region_constraints().len(), 2);

    let vir = output.vir().expect("nested reborrow has VIR");
    let parents = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction.instruction {
            VirInstruction::LoanReborrow { effect, .. } => Some(effect.parent),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(parents, [Some(VirLoanId::new(0)), Some(VirLoanId::new(1))]);

    let resolved = vir.resolve().expect("nested reborrow VIR resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("nested reborrow verification converges")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("nested parents restore exactly")
            .values(),
        [VirRuntimeValue::U64(9)]
    );
}

#[test]
fn reborrow_range_remains_allocation_relative_for_an_offset_parent() {
    let source = "struct Pair { left: u64, right: u64, }
        fn main() -> u64 {
            let mut pair = Pair { left: 1, right: 2 };
            let parent = &mut pair.right;
            {
                let child = &mut *parent;
                *child = 9;
            }
            return *parent;
        }";
    let output = accepted("offset-parent-reborrow.nera", source);
    let vir = output.vir().expect("offset reborrow has VIR");
    let effects = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction.instruction {
            VirInstruction::LoanBegin { effect, .. }
            | VirInstruction::LoanReborrow { effect, .. } => Some(effect),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(effects.len(), 2);
    assert_eq!(
        effects[0].range,
        VirLoanRange {
            start_bytes: 8,
            end_bytes: 16,
        }
    );
    assert_eq!(effects[1].range, effects[0].range);

    let resolved = vir.resolve().expect("offset reborrow VIR resolves");
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("offset reborrow verification converges")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("offset child restores offset parent")
            .values(),
        [VirRuntimeValue::U64(9)]
    );
}

#[test]
fn parent_and_parent_sibling_access_are_rejected_while_child_is_active() {
    let cases = [
        (
            "suspended-parent-read.nera",
            "fn main() -> u64 {
                let mut value = 1;
                let parent = &mut value;
                let child = &mut *parent;
                let invalid = *parent;
                return *child + invalid;
            }",
        ),
        (
            "suspended-parent-sibling.nera",
            "struct Pair { left: u64, right: u64, }
             fn main() -> u64 {
                let mut pair = Pair { left: 1, right: 2 };
                let parent = &mut pair;
                let child = &mut parent.left;
                let invalid = parent.right;
                return *child + invalid;
             }",
        ),
    ];

    for (name, source) in cases {
        let output = accepted(name, source);
        let resolved = output
            .vir()
            .expect("conflicting reborrow has VIR")
            .resolve()
            .expect("conflicting reborrow VIR resolves");
        assert!(
            !verify_program(&resolved, CfgAnalysisConfig::default())
                .expect("conflicting verification converges")
                .is_memory_checked_core0(),
            "{name} must not verify"
        );
        assert!(matches!(
            interpret(resolved.runtime())
                .expect_err("suspended parent access must fault")
                .kind(),
            VirExecutionErrorKind::LoanAccessConflict { .. }
        ));
    }
}

#[test]
fn reborrow_cannot_strengthen_shared_parent_or_borrow_the_reference_binding() {
    let cases = [
        (
            "stronger-reborrow.nera",
            "fn main() -> u64 {
                let value = 1;
                let parent = &value;
                let child = &mut *parent;
                return *child;
            }",
            FrontendStatus::Invalid,
        ),
        (
            "reference-binding-borrow.nera",
            "fn main() -> u64 {
                let value = 1;
                let parent = &value;
                let nested = &parent;
                return value;
            }",
            FrontendStatus::Unsupported,
        ),
    ];
    for (name, source, expected) in cases {
        let output = analyze(&SourceFile::from_text(name, source));
        assert_eq!(output.status(), expected, "{name}: {:?}", output.issues());
        assert!(output.vir().is_none());
    }
}

#[test]
fn hir_reborrow_requires_an_explicit_region_inclusion_constraint() {
    let output = accepted(
        "reborrow-region-mutation.nera",
        "fn main() -> u64 {
            let value = 1;
            let parent = &value;
            let child = &*parent;
            return *child;
        }",
    );
    let mut tables = program_tables(output.hir().expect("reborrow has HIR"));
    tables.region_constraints.clear();
    let error = HirProgram::from_tables(tables)
        .expect_err("a reborrow without child <= parent must fail HIR validation");
    assert_eq!(error.table(), "expression");
    assert!(error.problem().contains("reborrow region"));
}
