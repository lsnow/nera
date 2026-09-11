use nera::{
    CfgAnalysisConfig, FrontendIssueKind, FrontendStatus, HirContractId, HirExpressionKind,
    HirFunction, HirFunctionId, HirProgram, HirProgramTables, HirProgramValidationError,
    HirStatementKind, SourceFile, VirContractId, VirExecutionErrorKind, VirFunctionId,
    VirInstruction, VirRuntimeValue, analyze, interpret, verify_program,
};

fn accepted(name: &str, source: &[u8]) -> nera::FrontendOutput {
    let output = analyze(&SourceFile::new(name, source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{name}: {:?}",
        output.issues()
    );
    output
}

fn rebuild_hir(
    hir: &HirProgram,
    functions: Vec<HirFunction>,
) -> Result<HirProgram, HirProgramValidationError> {
    HirProgram::from_tables(HirProgramTables {
        data_layout: hir.data_layout(),
        entry_module: hir.entry_module_id(),
        entry_function: hir.entry_function_id(),
        modules: hir.modules().to_vec(),
        types: hir.types().to_vec(),
        type_capabilities: hir.type_capability_table().to_vec(),
        layouts: hir.layouts().to_vec(),
        fields: hir.fields().to_vec(),
        variants: hir.variants().to_vec(),
        generic_parameters: hir.generic_parameters().to_vec(),
        regions: hir.regions().to_vec(),
        region_constraints: hir.region_constraints().to_vec(),
        functions,
        contracts: hir.contracts().to_vec(),
        predicates: hir.predicates().to_vec(),
        specs: hir.specs().clone(),
    })
}

#[test]
fn direct_call_is_typed_once_and_lowered_for_every_function() {
    let output = accepted(
        "direct-call.nera",
        include_bytes!("../spec/cases/control-flow/direct-call.nera"),
    );
    let hir = output.hir().expect("accepted source has HIR");
    assert_eq!(
        hir.functions()
            .iter()
            .map(|function| (function.id, function.name.as_str()))
            .collect::<Vec<_>>(),
        vec![
            (HirFunctionId::new(0), "main"),
            (HirFunctionId::new(1), "add"),
            (HirFunctionId::new(2), "unused")
        ]
    );
    let HirStatementKind::Return { value: Some(value) } = &hir
        .entry_function()
        .body()
        .expect("main body")
        .root
        .statements[0]
        .kind
    else {
        panic!("main returns the call result")
    };
    let HirExpressionKind::Call(call) = &value.kind else {
        panic!("return expression is a typed direct call")
    };
    assert_eq!(call.callee, HirFunctionId::new(1));
    assert_eq!(call.contract.get(), 1);
    assert_eq!(call.arguments.len(), 2);
    assert_eq!(call.instantiated_signature, hir.functions()[1].signature);

    let vir = output.vir().expect("accepted source has VIR");
    assert_eq!(vir.runtime().functions.len(), 3);
    let call = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match &instruction.instruction {
            VirInstruction::Call {
                target, arguments, ..
            } => Some((target, arguments)),
            _ => None,
        })
        .expect("main contains a VIR call");
    assert_eq!(call.0.symbol, "add");
    assert_eq!(call.0.contract, VirContractId::new(1));
    assert_eq!(call.0.signature, vir.runtime().functions[1].signature);
    assert_eq!(call.1.len(), 2);

    let execution =
        interpret(vir.resolve().expect("direct calls resolve").runtime()).expect("execution");
    assert_eq!(execution.values(), &[VirRuntimeValue::U64(42)]);
    let verification = verify_program(
        &vir.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("closed scalar call contracts verify");
    assert!(verification.is_memory_checked_core0());
    assert_eq!(verification.functions().len(), 3);
}

#[test]
fn boolean_parameters_and_results_cross_direct_calls() {
    let output = accepted(
        "bool-call.nera",
        b"fn main() -> u64 {\n\
            if invert(false) { return 1; } else { return 0; }\n\
        }\n\
        fn invert(value: bool) -> bool {\n\
            if value { return false; }\n\
            return true;\n\
        }",
    );
    let vir = output.vir().expect("boolean call has VIR");
    assert_eq!(vir.runtime().functions[1].signature.parameters.len(), 1);
    assert_eq!(vir.runtime().functions[1].signature.results.len(), 1);
    let execution =
        interpret(vir.resolve().expect("boolean call resolves").runtime()).expect("execution");
    assert_eq!(execution.values(), &[VirRuntimeValue::U64(1)]);
    assert!(
        verify_program(
            &vir.resolve().expect("verification input resolves"),
            CfgAnalysisConfig::default()
        )
        .expect("boolean call verifies")
        .is_memory_checked_core0()
    );
}

#[test]
fn forward_mutual_recursion_uses_ids_without_topological_lowering() {
    let output = accepted(
        "recursive-call.nera",
        include_bytes!("../spec/cases/control-flow/recursive-call.nera"),
    );
    let vir = output.vir().expect("accepted source has VIR");
    assert_eq!(vir.runtime().functions.len(), 3);
    vir.resolve().expect("mutually recursive calls resolve");

    let execution =
        interpret(vir.resolve().expect("resolved recursion").runtime()).expect("terminates");
    assert_eq!(execution.values(), &[VirRuntimeValue::U64(6)]);
    let verification = verify_program(
        &vir.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("recursive summaries form a closed contract set");
    assert!(verification.is_memory_checked_core0());
    assert_eq!(verification.functions().len(), 3);
}

#[test]
fn own_pointer_and_permission_cross_the_same_call_boundary() {
    let output = accepted(
        "owned-call.nera",
        include_bytes!("../spec/cases/control-flow/owned-call.nera"),
    );
    let vir = output.vir().expect("accepted source has VIR");
    let identity = &vir.runtime().functions[1];
    assert_eq!(identity.signature.parameters.len(), 2);
    assert_eq!(identity.signature.results.len(), 2);

    let execution =
        interpret(vir.resolve().expect("resource call resolves").runtime()).expect("execution");
    assert_eq!(execution.values(), &[VirRuntimeValue::U64(42)]);

    let verification = verify_program(
        &vir.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("typed resource call verifies modularly");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
}

#[test]
fn recursive_own_call_uses_the_same_resource_summary_at_every_depth() {
    let output = accepted(
        "recursive-owned-call.nera",
        include_bytes!("../spec/cases/control-flow/recursive-owned-call.nera"),
    );
    let vir = output.vir().expect("accepted source has VIR");
    let recursive = &vir.runtime().functions[1];
    assert_eq!(recursive.signature.parameters.len(), 3);
    assert_eq!(recursive.signature.results.len(), 2);

    let contract = vir
        .as_unit()
        .specs
        .contract(recursive.contract)
        .expect("recursive function has one inferred contract");
    assert_eq!(
        contract.resources.len(),
        2,
        "requires consumes the input resource and ensures publishes a fresh result resource"
    );

    let resolved = vir.resolve().expect("recursive ownership calls resolve");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("recursive ownership is checked modularly");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("recursive ownership call executes")
            .values(),
        &[VirRuntimeValue::U64(42)]
    );
}

#[test]
fn call_arguments_are_emitted_once_in_source_order() {
    let source = b"fn main() -> u64 {\n\
        let first = alloc<u64>(1);\n\
        let second = alloc<u64>(1);\n\
        *first = 1;\n\
        *second = 2;\n\
        free(first);\n\
        free(second);\n\
        return choose(*first, *second);\n\
    }\n\
    fn choose(left: u64, right: u64) -> u64 { return left; }";
    let output = accepted("argument-order.nera", source);
    let vir = output.vir().expect("accepted source has VIR");
    let instructions = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect::<Vec<_>>();
    let loads = instructions
        .iter()
        .enumerate()
        .filter(|(_, instruction)| matches!(instruction.instruction, VirInstruction::Load { .. }))
        .collect::<Vec<_>>();
    let call_position = instructions
        .iter()
        .position(|instruction| matches!(instruction.instruction, VirInstruction::Call { .. }))
        .expect("call instruction");
    assert_eq!(loads.len(), 2);
    assert!(loads[0].1.source_span.start() < loads[1].1.source_span.start());
    assert!(loads[1].0 < call_position);

    let first_argument_start = std::str::from_utf8(source)
        .expect("ASCII fixture")
        .find("*first, *second")
        .expect("first argument");
    let error =
        interpret(vir.resolve().expect("call resolves").runtime()).expect_err("first load is UAF");
    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::UseAfterFree { .. }
    ));
    assert_eq!(error.source_span().start(), first_argument_start);
}

#[test]
fn invalid_static_calls_and_indirect_syntax_fail_closed() {
    for source in [
        "fn main() -> u64 { return missing(); }",
        "fn main() -> u64 { return one(); } fn one(value: u64) -> u64 { return value; }",
        "fn main() -> u64 { return one(true); } fn one(value: u64) -> u64 { return value; }",
        "fn main() { return; } fn main() { return; }",
    ] {
        let source_file = SourceFile::from_text("invalid-call.nera", source);
        let output = analyze(&source_file);
        assert_eq!(output.status(), FrontendStatus::Invalid, "{source}");
        assert_eq!(output.issues()[0].kind(), FrontendIssueKind::Elaboration);
        assert!(output.hir().is_none());
        assert!(output.vir().is_none());
    }

    let indirect_source = SourceFile::from_text(
        "indirect-call.nera",
        "fn main() -> u64 { return (one)(1); } fn one(value: u64) -> u64 { return value; }",
    );
    let indirect = analyze(&indirect_source);
    assert_eq!(indirect.status(), FrontendStatus::Unsupported);
    assert!(indirect.vir().is_none());
}

#[test]
fn inconsistent_hir_call_metadata_is_rejected_before_lowering() {
    let output = accepted(
        "direct-call.nera",
        include_bytes!("../spec/cases/control-flow/direct-call.nera"),
    );
    let hir = output.hir().expect("HIR");
    let mut functions = hir.functions().to_vec();
    {
        let HirStatementKind::Return { value: Some(value) } = &mut functions[0]
            .body
            .as_mut()
            .expect("main body")
            .root
            .statements[0]
            .kind
        else {
            panic!("main return")
        };
        let HirExpressionKind::Call(call) = &mut value.kind else {
            panic!("main call")
        };
        call.callee = HirFunctionId::new(99);
    }
    assert!(rebuild_hir(hir, functions.clone()).is_err());

    {
        let HirStatementKind::Return { value: Some(value) } = &mut functions[0]
            .body
            .as_mut()
            .expect("main body")
            .root
            .statements[0]
            .kind
        else {
            panic!("main return")
        };
        let HirExpressionKind::Call(call) = &mut value.kind else {
            panic!("main call")
        };
        call.callee = HirFunctionId::new(1);
        call.contract = HirContractId::new(0);
    }
    assert!(rebuild_hir(hir, functions).is_err());
}

#[test]
fn entry_signature_is_only_an_execution_wrapper_constraint() {
    let output = accepted(
        "parameterized-entry.nera",
        b"fn main(value: u64) -> u64 { return value; }",
    );
    let vir = output
        .vir()
        .expect("parameterized entry still lowers and validates");
    assert_eq!(vir.runtime().functions[0].id, VirFunctionId::new(0));
    let error = interpret(
        vir.resolve()
            .expect("internal signature is resolvable")
            .runtime(),
    )
    .expect_err("source execution cannot synthesize entry arguments");
    assert_eq!(
        error.kind(),
        &VirExecutionErrorKind::EntryPointParametersUnsupported { count: 1 }
    );
}

#[test]
fn nonterminating_recursion_hits_the_interpreter_depth_limit() {
    let output = accepted(
        "recursive-depth.nera",
        b"fn main() { recurse(); return; } fn recurse() { recurse(); return; }",
    );
    let vir = output.vir().expect("recursive source has VIR");
    let error = interpret(vir.resolve().expect("recursive target resolves").runtime())
        .expect_err("unbounded recursion is an execution resource fault");
    assert_eq!(error.kind(), &VirExecutionErrorKind::CallDepthExceeded);

    let verification = verify_program(
        &vir.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("recursive verification uses the registered contract, not execution");
    assert!(verification.is_memory_checked_core0());
}
