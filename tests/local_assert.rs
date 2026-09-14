use nera::*;
#[path = "support/local_assert.rs"]
mod fixture;

fn unit(source: &str) -> ValidatedVirUnit {
    let output = analyze(&SourceFile::from_text("local-assert.nera", source));
    assert!(output.vir().is_some(), "{:?}", output.issues());
    output.vir().unwrap().clone()
}

fn proofs(source: &str) -> Vec<(ObligationStatus, Option<SpecFailure>)> {
    let unit = unit(source);
    let report = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert!(unit.as_unit().specs.trust_entries().is_empty());
    report
        .functions()
        .values()
        .flat_map(|f| f.proofs().iter().map(|p| (p.status(), p.failure())))
        .collect()
}

#[test]
fn source_assertions_are_erased_and_do_not_change_memory_or_native_codegen() {
    let annotated = unit(fixture::SOURCE);
    let erased = unit(&fixture::erased());
    let resolved = annotated.resolve().unwrap();
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    assert_eq!(report.functions()[&VirFunctionId::new(0)].proofs().len(), 4);
    assert_eq!(
        annotated.runtime().stable_dump(),
        erased.runtime().stable_dump()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(2)]
    );
    assert_eq!(
        backend::X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(resolved.runtime())
            .unwrap(),
        backend::X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(erased.resolve().unwrap().runtime())
            .unwrap()
    );
}

#[test]
fn assignment_and_shadowing_are_snapshotted_at_each_statement() {
    use ObligationStatus::{Proven as P, Refuted as R};
    let source = "fn main()->u64 { let mut x=1; assert x==1; x=2; assert x==1; { let x=3; assert x==3; } assert x==2; return x; }";
    assert_eq!(
        proofs(source).iter().map(|p| p.0).collect::<Vec<_>>(),
        [P, R, P, P]
    );
}

#[test]
fn memory_observations_see_initialization_and_free_at_the_actual_point() {
    use ObligationStatus::{Proven as P, Refuted as R};
    let source = "fn main()->u64 { let p=alloc<u64>(1); assert alive(p.region); assert initialized(p); *p=7; assert initialized(p); free(p); assert alive(p.region); return 0; }";
    let proofs = proofs(source);
    assert_eq!(proofs.iter().map(|p| p.0).collect::<Vec<_>>(), [P, R, P, R]);
    assert_eq!(proofs[1].1, Some(SpecFailure::ResourceConflict));
    assert_eq!(proofs[3].1, Some(SpecFailure::ResourceConflict));
}

#[test]
fn initialized_element_ranges_use_checked_layout_scaling_and_real_state() {
    let source = "fn main()->u64 { let p=alloc<u64>(2); *p=7; assert initialized(p,0..1); assert initialized(p,0..2); assert initialized(p,2..3); assert initialized(p,1..0); assert initialized(p,0..18446744073709551615); free(p); return 0; }";
    assert_eq!(
        proofs(source).iter().map(|p| p.0).collect::<Vec<_>>(),
        [
            ObligationStatus::Proven,
            ObligationStatus::Refuted,
            ObligationStatus::Refuted,
            ObligationStatus::Refuted,
            ObligationStatus::Unknown
        ]
    );
}

#[test]
fn branches_and_early_returns_do_not_relocate_or_assume_assertions() {
    let source = "fn main()->u64 { return inspect(3); } fn inspect(x:u64)->u64 { if x<8 { assert x<8; return x; } assert x>=8; return x; }";
    assert!(proofs(source).iter().all(|p| p.0.is_proven()));
    let unknown = proofs(
        "fn main()->u64 { return f(3); } fn f(x:u64)->u64 { assert x<8; assert x<8; return x; }",
    );
    assert_eq!(unknown.len(), 2);
    assert!(unknown.iter().all(|p| *p
        == (
            ObligationStatus::Unknown,
            Some(SpecFailure::InsufficientFacts)
        )));
}

#[test]
fn logical_precedence_checked_arithmetic_and_short_circuit_are_not_runtime_operations() {
    let source = "fn main()->u64 { assert (1+2*3==7)==true && !(4-1==2); assert true || 0-1==0; assert 18446744073709551615+1==0; return 7; }";
    assert_eq!(
        proofs(source).iter().map(|p| p.0).collect::<Vec<_>>(),
        [
            ObligationStatus::Proven,
            ObligationStatus::Proven,
            ObligationStatus::Unknown
        ]
    );
    assert!(
        proofs("fn main()->u64 { let i=3usize; assert i+1<5; return 0; }")[0]
            .0
            .is_proven()
    );
}

#[test]
fn unsupported_or_effectful_assertions_never_silently_disappear() {
    for assertion in [
        "assert call();",
        "assert *p==1;",
        "assert alloc<u64>(1)==p;",
        "assert &x==&x;",
        "assert exists x in 0..8: x==1;",
        "proof { assert true; }",
        "assert x*x==1;",
        "assert old(x)==1;",
        "assert x/2==1;",
    ] {
        let source = format!(
            "fn main()->u64 {{ let x=1; let p=alloc<u64>(1); {assertion} free(p); return x; }} fn call()->bool {{ return true; }}"
        );
        let output = analyze(&SourceFile::from_text("gated.nera", source));
        assert!(output.vir().is_none(), "{assertion}");
        assert!(!output.issues().is_empty(), "{assertion}");
    }
    for source in [
        "fn main(){ assert missing==0; }",
        "fn main(){ assert 1; }",
        "fn main(){ assert true==1; }",
        "fn main(){ assert later==0; let later=0; }",
        "fn main(){ {let x=1;} assert x==1; }",
    ] {
        assert!(
            analyze(&SourceFile::from_text("invalid.nera", source))
                .vir()
                .is_none(),
            "{source}"
        );
    }
}

#[test]
fn source_spans_and_loan_end_planning_preserve_the_local_anchor() {
    let source =
        "fn main()->u64 { let mut x=7; let q=&x; let y=*q; assert alive(q.region); return y; }";
    let unit = unit(source);
    let report = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    let proof = &report.functions()[&VirFunctionId::new(0)].proofs()[0];
    assert!(proof.status().is_proven(), "{:?}", report.diagnostics());
    assert_eq!(
        &source[proof.source_span().start() as usize..proof.source_span().end() as usize],
        "assert alive(q.region);"
    );
    let VirSpecLocation::Runtime(VirLocation::Instruction { ordinal, .. }) = proof.location()
    else {
        panic!("expected instruction boundary");
    };
    assert!(
        unit.as_unit().runtime.functions[0].blocks[0].instructions[..=ordinal as usize]
            .iter()
            .any(|i| matches!(i.instruction, VirInstruction::LoanEnd { .. }))
    );
}

#[test]
fn final_guarded_cases_are_checked_independently() {
    let source = "fn main()->u64 { return f(true); } fn f(flag:bool)->u64 { let p=alloc<u64>(1); let mut x=1; if flag { free(p); x=2; } assert x==1 || x==2; if flag {} else { free(p); } return x; }";
    let unit = unit(source);
    let report = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    let function = &report.functions()[&VirFunctionId::new(1)];
    let proof = &function.proofs()[0];
    assert!(proof.status().is_proven(), "{:?}", report.diagnostics());
    let VirSpecLocation::Runtime(location) = proof.location() else {
        panic!();
    };
    let block = function.cfg().block(location.block().unwrap()).unwrap();
    let state = match location {
        VirLocation::BlockEntry { .. } => block.entry_conditional_state(),
        VirLocation::Instruction { ordinal, .. } => {
            &block.instruction_conditional_states()[ordinal as usize]
        }
        _ => panic!("wrong boundary"),
    };
    assert!(
        state.cases().len() >= 2,
        "fixture must exercise distinct final resource cases"
    );
}

#[test]
fn loop_local_assertions_and_parser_budgets_are_bounded() {
    let source =
        "fn main()->u64 { let mut i=0; while i<3 { assert i<3; i=i+1; } assert i>=3; return i; }";
    assert!(proofs(source).iter().all(|p| p.0.is_proven()));
    let source = format!("fn main() {{ assert {}true; }}", "!".repeat(130));
    std::thread::Builder::new()
        .name("logical-prefix-budget".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(move || {
            let output = analyze(&SourceFile::from_text("bounded.nera", source));
            assert_eq!(output.status(), FrontendStatus::Unsupported);
            assert!(output.vir().is_none());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn const_instances_have_separate_proves_and_resource_builtins_cannot_be_shadowed() {
    let source = "fn main()->u64 { return f<1>(7)+f<2>(0); } fn f<const N:usize>(x:u64)->u64 { assert N>0; return x; }";
    let result = proofs(source);
    assert_eq!(result.len(), 2);
    assert!(result.iter().all(|p| p.0.is_proven()));
    let source = "fn main()->u64 { let p=alloc<u64>(1); *p=7; assert initialized(p); free(p); return 0; } fn initialized()->bool { return true; }";
    let output = analyze(&SourceFile::from_text("shadow.nera", source));
    assert_eq!(output.status(), FrontendStatus::Unsupported);
    assert!(output.vir().is_none());
}
