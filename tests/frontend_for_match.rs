use nera::{
    FrontendStatus, HirForSource, HirPatternKind, HirStatementKind, SourceFile,
    VirExecutionErrorKind, VirFunctionId, VirInstruction, VirRuntimeValue, VirTerminator, analyze,
    analyze_function_cfg, interpret,
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

fn result(output: &nera::FrontendOutput) -> VirRuntimeValue {
    interpret(
        output
            .vir()
            .expect("accepted source has VIR")
            .resolve()
            .expect("VIR resolves")
            .runtime(),
    )
    .expect("program executes")
    .values()[0]
        .clone()
}

#[test]
fn half_open_for_reaches_hir_cfg_interpreter_and_verifier() {
    let source = include_str!("../spec/cases/control-flow/for-range.nera");
    let output = accepted("for-range.nera", source);
    let repeated = accepted("for-range.nera", source);
    assert_eq!(
        output.vir().expect("VIR").stable_dump(),
        repeated.vir().expect("repeated VIR").stable_dump()
    );

    let body = &output
        .hir()
        .expect("HIR")
        .entry_function()
        .body()
        .expect("body")
        .root;
    let HirStatementKind::For {
        pattern,
        source,
        body: loop_body,
        ..
    } = &body.statements[1].kind
    else {
        panic!("second statement is the for loop")
    };
    assert!(matches!(pattern.kind, HirPatternKind::Binding { .. }));
    assert_eq!(loop_body.locals.len(), 1, "loop binding owns its scope");
    assert!(matches!(
        source,
        HirForSource::IntegerRange {
            inclusive: false,
            ..
        }
    ));

    let function = &output.vir().expect("VIR").runtime().functions[0];
    let VirTerminator::Jump { target: header } = &function.blocks[0].terminator.terminator else {
        panic!("range predecessor jumps to a header")
    };
    assert!(matches!(
        function.blocks[header.block.get() as usize]
            .terminator
            .terminator,
        VirTerminator::Branch { .. }
    ));
    assert_eq!(result(&output), VirRuntimeValue::U64(14));
    let verification = analyze_function_cfg(
        &output.vir().expect("VIR").resolve().expect("VIR resolves"),
        VirFunctionId::new(0),
    )
    .expect("range loop reaches the verifier fixed point");
    assert!(verification.all_obligations_proven());
}

#[test]
fn for_bounds_execute_once_and_continue_uses_the_increment_latch() {
    let output = accepted(
        "for-order.nera",
        "fn main() -> u64 {
             let mut sum = 0;
             for item in begin()..finish() {
                 if item == 1 { continue; }
                 if item == 4 { break; }
                 sum = sum + item;
             }
             return sum;
         }
         fn begin() -> u64 { return 0; }
         fn finish() -> u64 { return 6; }",
    );
    let function = &output.vir().expect("VIR").runtime().functions[0];
    assert_eq!(
        function.blocks[0]
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction.instruction, VirInstruction::Call { .. }))
            .count(),
        2,
        "both bound calls are emitted once in the predecessor"
    );
    assert_eq!(
        function
            .blocks
            .iter()
            .skip(1)
            .flat_map(|block| &block.instructions)
            .filter(|instruction| matches!(instruction.instruction, VirInstruction::Call { .. }))
            .count(),
        0,
        "bound calls are not repeated by the header or latch"
    );
    assert_eq!(result(&output), VirRuntimeValue::U64(5));

    let zero = accepted(
        "empty-range.nera",
        "fn main() -> u64 { let mut value = 7; for item in 5..2 { value = value + item; } return value; }",
    );
    assert_eq!(result(&zero), VirRuntimeValue::U64(7));
}

#[test]
fn match_preserves_arm_order_single_evaluation_and_guard_order() {
    let output = accepted(
        "match-once.nera",
        "fn main() -> u64 {
             let memory = alloc<u64>(1);
             *memory = 2;
             match *memory {
                 2 if choose(false) => { free(memory); return 10; },
                 2 => { free(memory); return 20; },
                 _ => { free(memory); return 30; },
             }
         }
         fn choose(value: bool) -> bool { return value; }",
    );
    let function = &output.vir().expect("VIR").runtime().functions[0];
    assert_eq!(
        function
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter(|instruction| matches!(instruction.instruction, VirInstruction::Load { .. }))
            .count(),
        1,
        "the match value is materialized once"
    );
    assert_eq!(result(&output), VirRuntimeValue::U64(20));

    let skipped = accepted(
        "skipped-guard.nera",
        "fn main() -> u64 {
             let memory = alloc<u64>(1);
             *memory = 9;
             free(memory);
             match 0 {
                 1 if *memory == 9 => { return 1; },
                 _ => { return 2; },
             }
         }",
    );
    assert_eq!(
        result(&skipped),
        VirRuntimeValue::U64(2),
        "a nonmatching arm must not evaluate its guard"
    );
}

#[test]
fn bool_match_can_be_exhaustive_without_a_wildcard_or_fake_join() {
    let output = accepted(
        "bool-match.nera",
        "fn main() -> u64 {
             match false {
                 true => { return 1; },
                 false => { return 2; },
             }
         }",
    );
    let function = &output.vir().expect("VIR").runtime().functions[0];
    assert_eq!(result(&output), VirRuntimeValue::U64(2));
    assert!(
        function
            .blocks
            .iter()
            .all(|block| match &block.terminator.terminator {
                VirTerminator::Jump { target } => matches!(
                    function.blocks[target.block.get() as usize]
                        .terminator
                        .terminator,
                    VirTerminator::Return { .. }
                ),
                _ => true,
            }),
        "all-return match only jumps from selection to returning arms"
    );
}

#[test]
fn for_and_match_surface_boundaries_fail_closed() {
    for (name, source, expected) in [
        (
            "inclusive.nera",
            "fn main() { for item in 0..=2 { } return; }",
            FrontendStatus::Unsupported,
        ),
        (
            "iterator.nera",
            "fn main() { let value = 2; for item in value { } return; }",
            FrontendStatus::Unsupported,
        ),
        (
            "destructure.nera",
            "fn main() { for (left, right) in 0..2 { } return; }",
            FrontendStatus::Unsupported,
        ),
        (
            "bad-bound.nera",
            "fn main() { for item in false..true { } return; }",
            FrontendStatus::Invalid,
        ),
        (
            "non-exhaustive.nera",
            "fn main() -> u64 { match 1 { 1 => { return 1; }, } }",
            FrontendStatus::Invalid,
        ),
        (
            "after-wildcard.nera",
            "fn main() -> u64 { match 1 { _ => { return 1; }, 1 => { return 2; }, } }",
            FrontendStatus::Invalid,
        ),
        (
            "wrong-pattern.nera",
            "fn main() -> u64 { match true { 1 => { return 1; }, _ => { return 2; }, } }",
            FrontendStatus::Invalid,
        ),
        (
            "binding-pattern.nera",
            "fn main() -> u64 { match 1 { value => { return 1; }, } }",
            FrontendStatus::Unsupported,
        ),
    ] {
        assert_eq!(lower(name, source).status(), expected, "{name}");
    }
}

#[test]
fn resource_state_is_checked_on_for_back_edges_and_match_arms() {
    let safe = accepted(
        "for-free-break.nera",
        "fn main() -> u64 { let memory = alloc<u64>(1); for item in 0..2 { free(memory); break; } return 1; }",
    );
    let analysis = analyze_function_cfg(
        &safe.vir().expect("VIR").resolve().expect("VIR resolves"),
        VirFunctionId::new(0),
    )
    .expect("safe break is analyzable");
    assert!(analysis.all_obligations_proven());

    let mismatch = accepted(
        "for-free-continue.nera",
        "fn main() -> u64 { let memory = alloc<u64>(1); for item in 0..2 { free(memory); continue; } return 1; }",
    );
    let analysis = analyze_function_cfg(
        &mismatch
            .vir()
            .expect("VIR")
            .resolve()
            .expect("VIR resolves"),
        VirFunctionId::new(0),
    )
    .expect("resource mismatch reaches analysis");
    assert!(!analysis.all_obligations_proven());
    assert_eq!(
        analysis,
        analyze_function_cfg(
            &mismatch
                .vir()
                .expect("VIR")
                .resolve()
                .expect("VIR resolves"),
            VirFunctionId::new(0),
        )
        .expect("resource mismatch analysis repeats"),
        "control-flow obligation order and result are deterministic"
    );
    let error = interpret(
        mismatch
            .vir()
            .expect("VIR")
            .resolve()
            .expect("resolves")
            .runtime(),
    )
    .expect_err("the second iteration cannot reuse a consumed permission");
    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::UseAfterFree { .. }
            | VirExecutionErrorKind::PermissionAlreadyConsumed { .. }
            | VirExecutionErrorKind::DoubleFree { .. }
    ));

    let matched = accepted(
        "match-resource.nera",
        "fn main() -> u64 { let memory = alloc<u64>(1); match true { true => { free(memory); return 1; }, false => { free(memory); return 0; }, } }",
    );
    let analysis = analyze_function_cfg(
        &matched.vir().expect("VIR").resolve().expect("VIR resolves"),
        VirFunctionId::new(0),
    )
    .expect("resource arms are analyzable");
    assert!(analysis.all_obligations_proven());
}
