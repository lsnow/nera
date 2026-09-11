use nera::{
    FrontendStatus, PathFact, SourceFile, VirExecutionErrorKind, VirFunctionId, VirInstruction,
    VirIntegerPredicate, VirRuntimeValue, VirTerminator, analyze, analyze_function_cfg, interpret,
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
fn structured_source_reaches_interpreter_and_verifier_through_one_cfg() {
    let source = include_str!("../spec/cases/control-flow/structured.nera");
    let output = accepted("structured.nera", source);
    let program = output.vir().expect("accepted source has VIR");
    let repeated = accepted("structured.nera", source);
    assert_eq!(
        program.stable_dump(),
        repeated
            .vir()
            .expect("repeated source has VIR")
            .stable_dump(),
        "structured CFG construction must be deterministic"
    );
    let function = &program.runtime().functions[0];
    assert!(function.blocks.len() > 3);
    assert!(
        function
            .blocks
            .iter()
            .any(|block| matches!(block.terminator.terminator, VirTerminator::Branch { .. }))
    );
    assert!(function.blocks.iter().any(|block| {
        block
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.instruction, VirInstruction::Compare { .. }))
    }));

    let resolved = program.resolve().expect("structured VIR resolves");
    let execution = interpret(resolved.runtime()).expect("structured program executes safely");
    assert_eq!(execution.values(), [VirRuntimeValue::U64(42)]);

    let verification = analyze_function_cfg(
        &program.resolve().expect("analysis input resolves"),
        VirFunctionId::new(0),
    )
    .expect("structured CFG reaches resource analysis");
    assert!(verification.all_obligations_proven());
}

#[test]
fn branch_edges_retain_boolean_and_comparison_path_facts() {
    let output = accepted(
        "branch-facts.nera",
        "fn branch_facts() -> u64 {
             let memory = alloc<u64>(1);
             *memory = 5;
             let selector = *memory;
             if selector < 10 {
                 free(memory);
                 return 1;
             } else {
                 free(memory);
                 return 0;
             }
         }",
    );
    let program = output.vir().expect("accepted source has VIR");
    let function = &program.runtime().functions[0];
    let entry = &function.blocks[0];
    let VirTerminator::Branch {
        condition,
        then_target,
        else_target,
    } = &entry.terminator.terminator
    else {
        panic!("entry must branch");
    };
    let (predicate, left, right) = entry
        .instructions
        .iter()
        .rev()
        .find_map(|instruction| match instruction.instruction {
            VirInstruction::Compare {
                result,
                predicate,
                left,
                right,
            } if result.id == *condition => Some((predicate, left, right)),
            _ => None,
        })
        .expect("branch condition is a direct comparison");
    assert_eq!(predicate, VirIntegerPredicate::LessThan);

    let analysis = analyze_function_cfg(
        &program.resolve().expect("analysis input resolves"),
        function.id,
    )
    .expect("CFG analysis succeeds");
    for (expected, target) in [(true, then_target), (false, else_target)] {
        let destination = function
            .blocks
            .iter()
            .find(|block| block.id == target.block)
            .expect("branch target exists");
        let renames = target
            .arguments
            .iter()
            .copied()
            .zip(destination.parameters.iter().map(|parameter| parameter.id))
            .collect::<Vec<_>>();
        let renamed = |source| {
            renames
                .iter()
                .find_map(|(from, to)| (*from == source).then_some(*to))
                .expect("comparison fact value is transported")
        };
        let condition = renamed(*condition);
        let comparison = PathFact::comparison(predicate, renamed(left), renamed(right));
        let path = analysis
            .block(target.block)
            .expect("target is analyzed")
            .entry_state()
            .path_condition();
        assert!(path.implies(PathFact::boolean(condition, expected)));
        assert!(path.implies(if expected {
            comparison
        } else {
            comparison.negated()
        }));
    }
}

#[test]
fn both_arms_can_return_without_creating_a_fake_join() {
    let output = accepted(
        "both-return.nera",
        "fn both_return() -> u64 {
             if false {
                 return 1;
             } else {
                 return 2;
             }
         }",
    );
    let program = output.vir().expect("accepted source has VIR");
    assert_eq!(program.runtime().functions[0].blocks.len(), 3);
    let execution =
        interpret(program.resolve().expect("VIR resolves").runtime()).expect("VIR executes");
    assert_eq!(execution.values(), [VirRuntimeValue::U64(2)]);
}

#[test]
fn lexical_block_names_do_not_escape_and_shadowing_restores_the_outer_binding() {
    let shadowed = accepted(
        "shadowed.nera",
        "fn shadowed() -> u64 {
             let value = 1;
             {}
             {
                 let value = 2;
             }
             return value;
         }",
    );
    let execution = interpret(
        shadowed
            .vir()
            .expect("accepted")
            .resolve()
            .expect("resolves")
            .runtime(),
    )
    .expect("executes");
    assert_eq!(execution.values(), [VirRuntimeValue::U64(1)]);

    let escaped = lower(
        "escaped.nera",
        "fn escaped() -> u64 {
             { let hidden = 1; }
             return hidden;
         }",
    );
    assert_eq!(escaped.status(), FrontendStatus::Invalid);
    assert!(escaped.hir().is_none());
}

#[test]
fn conditions_are_typed_and_short_circuit_operators_remain_gated() {
    let non_boolean = lower(
        "non-boolean.nera",
        "fn non_boolean() -> u64 {
             if 1 { return 1; } else { return 0; }
         }",
    );
    assert_eq!(non_boolean.status(), FrontendStatus::Invalid);

    let short_circuit = lower(
        "short-circuit.nera",
        "fn short_circuit() -> u64 {
             if true && false { return 1; } else { return 0; }
         }",
    );
    assert_eq!(short_circuit.status(), FrontendStatus::Unsupported);

    let chained = lower(
        "chained.nera",
        "fn chained() -> u64 {
             if 1 < 2 < 3 { return 1; } else { return 0; }
         }",
    );
    assert_eq!(chained.status(), FrontendStatus::Invalid);

    let unreachable = lower(
        "unreachable.nera",
        "fn unreachable() -> u64 {
             return 1;
             return 2;
         }",
    );
    assert_eq!(unreachable.status(), FrontendStatus::Invalid);

    let deep = format!(
        "fn deep() {{ {} return; {} }}",
        "{".repeat(300),
        "}".repeat(300)
    );
    assert_eq!(
        lower("deep.nera", &deep).status(),
        FrontendStatus::Unsupported
    );
}

#[test]
fn every_surface_integer_comparison_maps_to_the_exact_vir_predicate() {
    for suffix in ["", "usize"] {
        for (operator, expected) in [
            ("==", VirIntegerPredicate::Equal),
            ("!=", VirIntegerPredicate::NotEqual),
            ("<", VirIntegerPredicate::LessThan),
            ("<=", VirIntegerPredicate::LessOrEqual),
            (">", VirIntegerPredicate::GreaterThan),
            (">=", VirIntegerPredicate::GreaterOrEqual),
        ] {
            let source = format!(
                "fn comparison() -> u64 {{ if 1{suffix} {operator} 2{suffix} {{ return 1; }} else {{ return 0; }} }}"
            );
            let output = accepted(operator, &source);
            let predicate = output.vir().expect("accepted").runtime().functions[0]
                .blocks
                .iter()
                .flat_map(|block| &block.instructions)
                .find_map(|instruction| match instruction.instruction {
                    VirInstruction::Compare { predicate, .. } => Some(predicate),
                    _ => None,
                })
                .expect("comparison reaches VIR");
            assert_eq!(predicate, expected, "{suffix} {operator}");
        }
    }

    assert_eq!(
        lower(
            "mixed-integer-comparison.nera",
            "fn comparison() -> u64 { if 1usize < 2 { return 1; } else { return 0; } }",
        )
        .status(),
        FrontendStatus::Invalid
    );
}

#[test]
fn condition_fault_is_evaluated_once_and_resource_mismatch_is_refuted() {
    let fault = accepted(
        "condition-fault.nera",
        include_str!("../spec/cases/control-flow/condition-fault.nera"),
    );
    let program = fault.vir().expect("accepted source has VIR");
    let loads = program.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter(|instruction| matches!(instruction.instruction, VirInstruction::Load { .. }))
        .count();
    assert_eq!(loads, 1);
    let error = interpret(program.resolve().expect("faulting VIR resolves").runtime())
        .expect_err("condition load must fault");
    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::UninitializedRead { .. }
    ));

    let consistent = accepted(
        "resource-consistent.nera",
        "fn resource_consistent() -> u64 {
             let memory = alloc<u64>(1);
             if true { free(memory); } else { free(memory); }
             return 1;
         }",
    );
    let verification = analyze_function_cfg(
        &consistent
            .vir()
            .expect("accepted source has VIR")
            .resolve()
            .expect("VIR resolves"),
        VirFunctionId::new(0),
    )
    .expect("consistent resource transition is analyzable");
    assert!(
        verification.all_obligations_proven(),
        "consistent resource obligations: {:#?}",
        verification.obligations()
    );

    let mismatch = accepted(
        "resource-mismatch.nera",
        include_str!("../spec/cases/control-flow/resource-mismatch.nera"),
    );
    let verification = analyze_function_cfg(
        &mismatch
            .vir()
            .expect("accepted source has VIR")
            .resolve()
            .expect("VIR resolves"),
        VirFunctionId::new(0),
    )
    .expect("resource mismatch is analyzable");
    assert!(!verification.all_obligations_proven());
    assert!(
        verification
            .obligations()
            .iter()
            .any(|record| !record.obligation().is_proven())
    );
}
