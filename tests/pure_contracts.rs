use nera::{ProgramVerification, SourceFile, analyze, verify_program};

fn verify(source: &str) -> ProgramVerification {
    let output = analyze(&SourceFile::from_text("pure-contracts.nera", source));
    let unit = output
        .vir()
        .unwrap_or_else(|| panic!("{:?}", output.issues()));
    verify_program(&unit.resolve().unwrap(), Default::default()).unwrap()
}

#[test]
fn scalar_contract_chain() {
    let source = "fn main()->u64 { let y=successor(41); assert y == 42; return y; }
    fn successor(x:u64)->u64 requires x < 18446744073709551615; ensures result == old(x) + 1; { return x+1; }";
    let result = verify(source);
    assert!(
        result.is_memory_checked_core0(),
        "{:?}",
        result.diagnostics()
    );
}

#[test]
fn bad_call_and_bad_body_do_not_verify() {
    let source = "fn main()->u64 {return f(1);} fn f(x:u64)->u64 requires x == 1; ensures result == 1; {return x;}";
    assert!(verify(source).is_memory_checked_core0());
    assert!(!verify(&source.replace("f(1)", "f(2)")).is_memory_checked_core0());
    assert!(!verify(&source.replace("return x;", "return 2;")).is_memory_checked_core0());
}

#[test]
fn requires_at_actual_call_state_and_each_normal_return() {
    let source = "fn main()->u64 { return caller(1); }
        fn caller(x:u64)->u64 requires x <= 10; ensures result <= 10; { return f(x); }
        fn f(x:u64)->u64 requires x <= 10; ensures result <= 10; { if x == 0 { return 0; } return x; }";
    assert!(verify(source).is_memory_checked_core0());
    assert!(
        !verify(&source.replace(
            "requires x <= 10; ensures result <= 10; { return f",
            "ensures result <= 10; { return f"
        ))
        .is_memory_checked_core0()
    );
    assert!(!verify(&source.replace("return 0;", "return 11;")).is_memory_checked_core0());
    // Conditions on an unreachable return cannot establish a reachable result.
    let source = "fn main()->u64 {return f(1);} fn f(x:u64)->u64 requires x == 1; ensures result == 1; { if x == 0 {return 99;} return x;}";
    assert!(verify(source).is_memory_checked_core0());
}

#[test]
fn bool_usize_and_entry_snapshot_survive_local_updates() {
    let source = "fn main()->u64 { let y=f(41usize); assert y == 42usize; let b=g(true); assert b; return 42; }
        fn f(x:usize)->usize requires x <= 41usize; ensures result == old(x)+1usize; {let mut y=x; y=y+1usize; return y;}
        fn g(b:bool)->bool requires b; ensures result; {return b;}";
    let report = verify(source);
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
}

#[test]
fn unsupported_or_inconsistent_interfaces_never_become_checked() {
    for source in [
        "fn main()->u64 requires false; {return 0;}",
        "fn main(x:u64)->u64 requires x == 1; {return x;}",
        "fn main()->u64 {return f(1);} fn f(x:u64)->u64 requires x < 1; requires x > 2; {return x;}",
        "fn main()->u64 {return f(1);} fn f(x:u64)->u64 requires x == 1 || x == 2; {return x;}",
        "fn main()->u64 {return f(1);} fn f(x:u64)->u64 ensures result == old(x); {return f(x);}",
        "fn main()->u64 {return f(1);} fn f(x:u64)->u64 ensures result == 1; {return g(x);} fn g(x:u64)->u64 ensures result == 1; {return f(x);}",
    ] {
        let output = analyze(&SourceFile::from_text("gated-contract.nera", source));
        let unit = output
            .vir()
            .unwrap_or_else(|| panic!("{:?}", output.issues()));
        let result = verify_program(&unit.resolve().unwrap(), Default::default());
        assert!(
            !result.is_ok_and(|r| r.is_memory_checked_core0()),
            "{source}"
        );
    }
    assert!(
        verify("fn main()->u64 requires true; ensures result == 42; {return 42;}")
            .is_memory_checked_core0()
    );
}

#[test]
fn failed_prove_and_later_memory_error_block_summary_publication() {
    for body in [
        "assert false; return 1;",
        "assert true; let p=alloc<u64>(1); free(p); return *p;",
    ] {
        let source =
            format!("fn main()->u64 {{return f();}} fn f()->u64 ensures result == 1; {{{body}}}");
        let report = verify(&source);
        assert!(!report.is_memory_checked_core0());
        assert!(
            report
                .functions()
                .values()
                .all(|f| f.summary().state != nera::verifier::summary::SummaryState::Closed)
        );
    }
}

#[test]
fn contracts_do_not_change_runtime_instructions_or_insert_checks() {
    let source = "fn main()->u64 {return f(41);} fn f(x:u64)->u64 requires x <= 41; ensures result == old(x)+1; {return x+1;}";
    let erased = source.replace(
        "requires x <= 41; ensures result == old(x)+1;",
        &" ".repeat("requires x <= 41; ensures result == old(x)+1;".len()),
    );
    let a = analyze(&SourceFile::from_text("erasure.nera", source));
    let b = analyze(&SourceFile::from_text("erasure.nera", &erased));
    let unit = a.vir().unwrap();
    assert_eq!(
        unit.runtime().stable_dump(),
        b.vir().unwrap().runtime().stable_dump()
    );
    assert!(unit.as_unit().specs.trust_entries().is_empty());
    assert_eq!(
        nera::interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [nera::VirRuntimeValue::U64(42)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.resolve().unwrap().runtime())
        .unwrap();
}

#[test]
fn old_result_and_locals_cannot_escape_their_scope() {
    for clause in [
        "requires result == 1;",
        "requires old(x) == 1;",
        "ensures result == old(result);",
        "ensures result == old(old(x));",
        "ensures result == y;",
    ] {
        let source = format!(
            "fn main()->u64 {{return 0;}} fn f(x:u64)->u64 {clause} {{let y=x; return y;}}"
        );
        let output = analyze(&SourceFile::from_text("bad-contract.nera", &source));
        assert!(output.vir().is_none(), "{clause}");
    }
}

#[test]
fn no_normal_return_does_not_provide_a_scalar_result_proof() {
    let report = verify(
        "fn main()->u64 {return 0;} fn spin()->u64 ensures false; {while true {} return 0;}",
    );
    let spin = &report.functions()[&nera::VirFunctionId::new(1)];
    assert!(spin.cfg().returns().is_empty());
    assert!(spin.postconditions().is_empty());
}

#[test]
fn replacing_or_removing_a_callee_does_not_reuse_published_facts() {
    let good = "fn main()->u64 {let x=f(); assert x==1; return x;} fn f()->u64 ensures result==1; {return 1;}";
    assert!(verify(good).is_memory_checked_core0());
    assert!(!verify(&good.replace("{return 1;}", "{return 2;}")).is_memory_checked_core0());
    let output = analyze(&SourceFile::from_text(
        "missing.nera",
        good.split(" fn f").next().unwrap(),
    ));
    assert!(output.vir().is_none());
}
