use nera::*;

fn unit(source: &str) -> ValidatedVirUnit {
    let output = analyze(&SourceFile::from_text("runtime-assert.nera", source));
    assert!(output.vir().is_some(), "{:?}", output.issues());
    output.vir().unwrap().clone()
}

#[test]
fn false_assert_executes_with_its_source_span_and_does_not_become_a_spec_proof() {
    let source = "fn main()->u64 { assert false; return 7; }";
    let unit = unit(source);
    assert!(unit.as_unit().specs.proves().is_empty());
    let resolved = unit.resolve().unwrap();
    let error = interpret(resolved.runtime()).unwrap_err();
    assert_eq!(error.kind(), &VirExecutionErrorKind::CheckFailed);
    let span = error.source_span();
    assert_eq!(
        &source[span.start() as usize..span.end() as usize],
        "assert false;"
    );
    // Runtime checks retain the existing verifier obligation for successful execution.
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(report.functions().values().all(|f| f.proofs().is_empty()));
}

#[test]
fn assertions_read_current_storage_and_evaluate_calls_once() {
    let source = "fn main()->u64 { let mut x=0; assert bump(&mut x); assert x==1; let q=&x; assert *q==1; x=2; assert x==2; return x; } fn bump(x:&mut u64)->bool { *x=*x+1; return true; }";
    let unit = unit(source);
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(2)]
    );
}

#[test]
fn assertions_run_at_each_loop_iteration_and_after_branches() {
    for flag in ["true", "false"] {
        let source = format!(
            "fn main()->u64 {{ return f({flag}); }} fn f(flag:bool)->u64 {{ let mut x=0; if flag {{ x=2; }} else {{ x=3; }} assert x>=2; while x<5 {{ assert x<5; x=x+1; }} assert x==5; return x; }}"
        );
        let unit = unit(&source);
        assert_eq!(
            interpret(unit.resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(5)]
        );
    }
    let unit = unit("fn main()->u64 { let mut x=0; while x<3 { assert x<2; x=x+1; } return x; }");
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap_err()
            .kind(),
        &VirExecutionErrorKind::CheckFailed
    );
}

#[test]
fn runtime_assertions_are_instantiated() {
    let unit = unit(
        "fn main()->u64 { assert f<2>(2usize); return 7; } fn f<const N:usize>(x:usize)->bool { assert x==N; return true; }",
    );
    assert!(unit.as_unit().specs.proves().is_empty());
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(7)]
    );
}

#[test]
fn assertion_operands_are_type_checked_and_memory_reads_are_verified() {
    for source in [
        "fn main(){ assert 1; }",
        "fn main(){ assert missing; }",
        "fn main(){ assert alive(p.region); }",
    ] {
        assert!(
            analyze(&SourceFile::from_text("invalid.nera", source))
                .vir()
                .is_none(),
            "{source}"
        );
    }
    let unit = unit("fn main()->u64 { let p=alloc<u64>(1); assert *p==0; free(p); return 0; }");
    let report = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(interpret(unit.resolve().unwrap().runtime()).is_err());
}

#[test]
fn no_source_static_proof_entrypoint_is_exposed() {
    for source in [
        "fn main(){ prove true; }",
        "fn main(){ proof { assert true; } }",
        "fn main(){ let p=alloc<u64>(1); assert alive(p.region); free(p); }",
        "fn main(){ let p=alloc<u64>(1); assert initialized(p); free(p); }",
    ] {
        assert!(
            analyze(&SourceFile::from_text("static-entry.nera", source))
                .vir()
                .is_none(),
            "{source}"
        );
    }
    // The retired replacement spelling is not a reserved keyword.
    let unit = unit("fn main()->u64 { let prove=7; assert prove==7; return prove; }");
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(7)]
    );
}
