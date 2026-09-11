use nera::{
    AbstractByteRange, AbstractValue, CfgAnalysisConfig, FrontendStatus, LoanActivity, SourceFile,
    VirFunctionId, VirInstruction, VirRuntimeValue, analyze, analyze_function_cfg, interpret,
    verify_program,
};

fn accepted(source: &str) -> nera::ValidatedVirUnit {
    let output = analyze(&SourceFile::from_text("footprint.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:#?}",
        output.issues()
    );
    output.vir().unwrap().clone()
}

#[test]
fn evaluated_selection_survives_source_assignment_nested_projection_and_storage() {
    let unit = accepted(include_str!("../spec/cases/verify/symbolic-footprint.nera"));
    let resolved = unit.resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        verification.is_memory_checked_core0(),
        "{:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(84)]
    );
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(1)).unwrap();
    let mut symbolic = 0;
    for block in &unit.runtime().functions[1].blocks {
        for (instruction, state) in block
            .instructions
            .iter()
            .zip(analysis.block(block.id).unwrap().instruction_states())
        {
            if let VirInstruction::LoanBegin {
                effect,
                permission_result,
                ..
            }
            | VirInstruction::LoanReborrow {
                effect,
                permission_result,
                ..
            }
            | VirInstruction::LoanAliasShared {
                effect,
                permission_result,
                ..
            } = instruction.instruction
            {
                let loan = state.loan(effect.loan).unwrap();
                let AbstractValue::Permission(permission) =
                    state.value(permission_result.id).unwrap()
                else {
                    panic!("permission")
                };
                assert_eq!(permission.range(), loan.actual_range());
                assert!(loan.footprint().is_some());
                if matches!(permission.range(), AbstractByteRange::Symbolic { .. }) {
                    symbolic += 1;
                    assert_ne!(permission.range(), AbstractByteRange::Exact(loan.range()));
                }
            }
        }
    }
    assert!(
        symbolic >= 2,
        "dynamic view and aliases must not receive an envelope permission"
    );
    assert!(analysis.returns().iter().all(|returned| {
        returned
            .state()
            .loans()
            .values()
            .all(|loan| loan.activity() == LoanActivity::Ended)
    }));
}

#[test]
fn dynamic_empty_one_past_view_can_end_without_element_access() {
    let unit = accepted(
        "fn main() -> u64 { return empty(2usize); }
        fn empty(index: usize) -> u64 { if index <= 2usize {
            let values = [1, 2]; let view = &values[index..index]; return 7;
        } return 0; }",
    );
    let resolved = unit.resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        verification.is_memory_checked_core0(),
        "{:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(7)]
    );
}

#[test]
fn forged_slice_length_cannot_grant_the_rest_of_the_envelope() {
    let unit = accepted(
        "fn main() -> u64 { let values = [10,20,30,40];
        let bogus = 3usize; let start = 1usize; let end = 2usize;
        let view = &values[start..end]; return view[2]; }",
    );
    let mut forged = unit.as_unit().clone();
    let function = &mut forged.runtime.functions[0];
    let length = function
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .find_map(|i| match i.instruction {
            VirInstruction::Constant {
                result,
                value: nera::VirConstant::U64(3),
            } => Some(result.id),
            _ => None,
        })
        .unwrap();
    let bounds = function
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.instructions)
        .find_map(|i| match &mut i.instruction {
            VirInstruction::IndexAddress {
                bounds: nera::VirIndexBounds::Slice { length },
                ..
            } => Some(length),
            _ => None,
        })
        .unwrap();
    *bounds = length;
    let forged = forged.into_validated().unwrap();
    let resolved = forged.resolve().unwrap();
    assert!(
        !verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    let fault = interpret(resolved.runtime()).unwrap_err();
    assert!(
        matches!(
            fault.kind(),
            nera::VirExecutionErrorKind::PointerDomainViolation {
                start_bytes: 24,
                end_bytes: 32,
                ..
            }
        ),
        "{fault:?}"
    );
}

#[test]
fn nested_dynamic_reborrow_ends_and_restores_its_parent() {
    let unit = accepted(
        "fn main() -> u64 { return select(1usize); }
        fn select(index: usize) -> u64 { if index < 2usize {
            let mut values = [1,2]; let parent = &mut values;
            let child = &mut parent[index]; *child = 42;
            return parent[1]; } return 0; }",
    );
    let resolved = unit.resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        verification.is_memory_checked_core0(),
        "{:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn losing_the_index_across_cfg_does_not_erase_the_loan_or_prevent_end() {
    let aliased = accepted(
        "fn main() -> u64 { return select(1usize, true); }
        fn select(index: usize, flag: bool) -> u64 { if index < 2usize {
            let values = [10,42]; let mut i = index; let reference = &values[i];
            i = 0usize; if flag { i = 1usize; }
            return *reference; } return 0; }",
    );
    // The immutable `index` still carries the exact value of the old `i`.
    // 7.4.9 can preserve that alias rather than discarding its scaled range.
    assert!(
        verify_program(&aliased.resolve().unwrap(), CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    let unit = accepted(
        "fn main() -> u64 { return select(true); }
        fn select(flag: bool) -> u64 { let mut i = input(); if i < 2usize {
            let values = [10,42]; let reference = &values[i];
            i = 0usize; if flag { i = 1usize; }
            return *reference; } return 0; }
        fn input() -> usize { return 1usize; }",
    );
    // Lowering also carries the evaluated selection as an internal scalar.
    // Erase every scalar export at the borrow-creation edge, while retaining
    // the already-evaluated pointer and its linear permission. This mutation
    // deliberately tests genuine symbol loss, not assignment to a source name.
    let mut raw = unit.as_unit().clone();
    let function = &mut raw.runtime.functions[1];
    let scalar_parameters = function
        .blocks
        .iter()
        .map(|b| {
            (
                b.id,
                b.parameters
                    .iter()
                    .map(|p| p.ty == nera::VirType::U64)
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    for block in &mut function.blocks {
        if !block
            .instructions
            .iter()
            .any(|i| matches!(i.instruction, VirInstruction::LoanBegin { .. }))
        {
            continue;
        }
        let zero = nera::VirValueId::new(10000);
        block.instructions.push(nera::SpannedVirInstruction {
            instruction: VirInstruction::Constant {
                result: nera::VirValue {
                    id: zero,
                    ty: nera::VirType::U64,
                },
                value: nera::VirConstant::U64(0),
            },
            source_span: block.terminator.source_span,
        });
        let rewrite = |target: &mut nera::VirBlockTarget| {
            for (argument, is_scalar) in target
                .arguments
                .iter_mut()
                .zip(&scalar_parameters[&target.block])
            {
                if *is_scalar {
                    *argument = zero;
                }
            }
        };
        match &mut block.terminator.terminator {
            nera::VirTerminator::Jump { target } => rewrite(target),
            nera::VirTerminator::Branch {
                then_target,
                else_target,
                ..
            } => {
                rewrite(then_target);
                rewrite(else_target);
            }
            _ => panic!("borrow edge must branch"),
        }
    }
    raw.rebuild_source_map_from_runtime("lost-selection.vir", 10000);
    let origin = |function| {
        raw.source_map
            .origin_at(nera::VirLocation::FunctionEntry { function })
            .unwrap()
            .id
    };
    raw.borrows = nera::VirBorrowEnvironment::from_tables(
        raw.borrows
            .regions()
            .iter()
            .cloned()
            .map(|mut r| {
                r.source_origin = origin(r.owner);
                r
            })
            .collect(),
        raw.borrows
            .constraints()
            .iter()
            .copied()
            .map(|mut c| {
                c.source_origin = origin(c.owner);
                c
            })
            .collect(),
    );
    let unit = raw.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(1)).unwrap();
    let mut lost = false;
    for block in &unit.runtime().functions[1].blocks {
        let entry = analysis.block(block.id).unwrap().entry_state();
        if entry.loans().values().any(|loan| {
            loan.activity() == LoanActivity::Active
                && loan.actual_range() == AbstractByteRange::Unknown
        }) {
            lost = true;
        }
    }
    assert!(
        lost,
        "unpassed SSA selection must lose precision, not its loan"
    );
    assert!(!analysis.all_obligations_proven());
    assert!(analysis.returns().iter().all(|returned| {
        returned
            .state()
            .loans()
            .values()
            .all(|loan| loan.activity() == LoanActivity::Ended)
    }));
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
}
