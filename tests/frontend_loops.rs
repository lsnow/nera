use nera::{
    FrontendStatus, HirLoopId, HirStatementKind, SourceFile, VirFunctionId, VirInstruction,
    VirRuntimeValue, VirTerminator, VirValidationErrorKind, analyze, analyze_function_cfg,
    interpret,
};

fn lower(name: &str, source: &str) -> nera::FrontendOutput {
    analyze(&SourceFile::from_text(name, source))
}

fn accepted(name: &str, source: &str) -> nera::FrontendOutput {
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
fn while_carries_scalar_pointer_and_permission_through_one_cfg() {
    let source = include_str!("../spec/cases/control-flow/while.nera");
    let output = accepted("while.nera", source);
    let program = output.vir().expect("accepted loop has VIR");
    let repeated = accepted("while.nera", source);
    assert_eq!(
        program.stable_dump(),
        repeated.vir().expect("repeated loop has VIR").stable_dump()
    );

    let function = &program.runtime().functions[0];
    let VirTerminator::Jump { target: entry_edge } = &function.blocks[0].terminator.terminator
    else {
        panic!("loop predecessor must jump to its header");
    };
    let header = function
        .blocks
        .iter()
        .find(|block| block.id == entry_edge.block)
        .expect("header exists");
    assert!(matches!(
        header.terminator.terminator,
        VirTerminator::Branch { .. }
    ));
    assert!(
        header.parameters.len() >= 3,
        "counter plus pointer/permission"
    );
    assert!(function.blocks.iter().any(|block| {
        matches!(
            &block.terminator.terminator,
            VirTerminator::Jump { target } if target.block == header.id && block.id != function.entry
        )
    }));

    let execution =
        interpret(program.resolve().expect("loop VIR resolves").runtime()).expect("loop runs");
    assert_eq!(execution.values(), [VirRuntimeValue::U64(3)]);
    let verification = analyze_function_cfg(
        &program.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("loop reaches verifier fixed point");
    assert!(
        verification.all_obligations_proven(),
        "safe loop obligations: {:#?}",
        verification.obligations()
    );

    let mut malformed = program.as_unit().clone();
    let function = &mut malformed.runtime.functions[0];
    let header = entry_edge.block;
    let back_edge = function
        .blocks
        .iter_mut()
        .find_map(|block| match &mut block.terminator.terminator {
            VirTerminator::Jump { target }
                if target.block == header && block.id != function.entry =>
            {
                Some(target)
            }
            _ => None,
        })
        .expect("generated loop has a back edge");
    back_edge.arguments.pop();
    assert!(matches!(
        malformed
            .validate()
            .expect_err("back-edge arity mutation must fail")
            .kind(),
        VirValidationErrorKind::ArityMismatch { .. }
    ));

    let mut malformed = program.as_unit().clone();
    let function = &mut malformed.runtime.functions[0];
    let back_edge = function
        .blocks
        .iter_mut()
        .find_map(|block| match &mut block.terminator.terminator {
            VirTerminator::Jump { target }
                if target.block == header && block.id != function.entry =>
            {
                Some(target)
            }
            _ => None,
        })
        .expect("generated loop has a back edge");
    back_edge.arguments.swap(0, 1);
    assert!(matches!(
        malformed
            .validate()
            .expect_err("back-edge type mutation must fail")
            .kind(),
        VirValidationErrorKind::TypeMismatch { .. }
    ));
}

#[test]
fn zero_and_multiple_iterations_evaluate_the_header_condition_once_per_visit() {
    let output = accepted(
        "iterations.nera",
        "fn iterations() -> u64 {
             let mut counter = 0;
             while false { counter = counter + 100; }
             while counter < 3 { counter = counter + 1; }
             return counter;
         }",
    );
    let program = output.vir().expect("accepted loop has VIR");
    let comparisons = program.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter(|instruction| matches!(instruction.instruction, VirInstruction::Compare { .. }))
        .count();
    assert_eq!(
        comparisons, 1,
        "one comparison instruction is placed in its header"
    );
    let execution =
        interpret(program.resolve().expect("VIR resolves").runtime()).expect("loops execute");
    assert_eq!(execution.values(), [VirRuntimeValue::U64(3)]);
}

#[test]
fn nested_break_and_continue_bind_to_the_innermost_loop() {
    let output = accepted(
        "nested-loop.nera",
        include_str!("../spec/cases/control-flow/nested-loop.nera"),
    );
    let hir = output.hir().expect("accepted loop has HIR");
    let root = &hir.entry_function().body().expect("body").root;
    let HirStatementKind::While {
        loop_id: outer,
        body: outer_body,
        ..
    } = &root.statements[2].kind
    else {
        panic!("outer loop");
    };
    let HirStatementKind::While {
        loop_id: inner,
        body: inner_body,
        ..
    } = &outer_body.statements[2].kind
    else {
        panic!("inner loop");
    };
    assert_eq!(*outer, HirLoopId::new(0));
    assert_eq!(*inner, HirLoopId::new(1));
    let HirStatementKind::If { then_block, .. } = &inner_body.statements[1].kind else {
        panic!("continue branch");
    };
    assert!(matches!(
        then_block.statements[0].kind,
        HirStatementKind::Continue { target } if target == *inner
    ));
    let HirStatementKind::If { then_block, .. } = &inner_body.statements[2].kind else {
        panic!("break branch");
    };
    assert!(matches!(
        then_block.statements[0].kind,
        HirStatementKind::Break { target } if target == *inner
    ));

    let execution = interpret(
        output
            .vir()
            .expect("accepted loop has VIR")
            .resolve()
            .expect("VIR resolves")
            .runtime(),
    )
    .expect("nested loops execute");
    assert_eq!(execution.values(), [VirRuntimeValue::U64(26)]);
}

#[test]
fn loop_surface_and_type_errors_fail_closed() {
    for (name, source, expected) in [
        (
            "break-outside.nera",
            "fn invalid() { break; return; }",
            FrontendStatus::Invalid,
        ),
        (
            "continue-outside.nera",
            "fn invalid() { continue; return; }",
            FrontendStatus::Invalid,
        ),
        (
            "non-bool.nera",
            "fn invalid() { while 1 { break; } return; }",
            FrontendStatus::Invalid,
        ),
        (
            "immutable.nera",
            "fn invalid() -> u64 { let value = 0; value = 1; return value; }",
            FrontendStatus::Invalid,
        ),
        (
            "explicit-invariant.nera",
            "fn deferred() { while true { invariant true; break; } return; }",
            FrontendStatus::Unsupported,
        ),
    ] {
        assert_eq!(lower(name, source).status(), expected, "{name}");
    }
}

#[test]
fn loop_resource_transitions_are_checked_at_break_and_back_edge() {
    let safe = accepted(
        "free-and-break.nera",
        "fn free_and_break() -> u64 {
             let memory = alloc<u64>(1);
             while true { free(memory); break; }
             return 1;
         }",
    );
    let verification = analyze_function_cfg(
        &safe
            .vir()
            .expect("accepted loop has VIR")
            .resolve()
            .expect("loop VIR resolves"),
        VirFunctionId::new(0),
    )
    .expect("break resource transition is analyzable");
    assert!(verification.all_obligations_proven());

    let mismatch = accepted(
        "loop-resource-mismatch.nera",
        include_str!("../spec/cases/control-flow/loop-resource-mismatch.nera"),
    );
    let program = mismatch.vir().expect("accepted loop has VIR");
    let verification = analyze_function_cfg(
        &program.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("resource mismatch reaches verifier");
    assert!(!verification.all_obligations_proven());
    assert_eq!(
        interpret(program.resolve().expect("VIR resolves").runtime())
            .expect("a consumed permission tombstone may cross an edge when it is not reused")
            .values(),
        [VirRuntimeValue::U64(2)]
    );
}
