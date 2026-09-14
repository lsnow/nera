use nera::verification::{TextReportMode, render_text, verify_source};
use nera::{
    BorrowAccess, BorrowGuardAtom, BorrowResultRelation, FrontendStatus, SourceFile,
    VirRuntimeValue, analyze, interpret,
};

fn analyze_checked(source: &str) -> nera::frontend::FrontendOutput {
    let file = SourceFile::from_text("conditional-borrow.nera", source);
    let output = analyze(&file);
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let report = verify_source(&file, Default::default());
    assert!(
        report.is_checked(),
        "{}",
        render_text(&report, TextReportMode::Explain)
    );
    output
}

#[test]
fn boolean_guard_infers_both_shared_sources() {
    let output = analyze_checked(
        "fn main()->u64{let a=40;let b=2;let r=choose(true,&a,&b);return *r;}
         fn choose(flag:bool,a:&u64,b:&u64)->&u64{if flag{return a;}else{return b;}}",
    );
    let signature = &output.hir().unwrap().functions()[1].signature;
    assert_eq!(signature.borrow_result, None);
    assert_eq!(signature.borrow_result_alternatives.len(), 2);
    assert!(
        signature
            .borrow_result_alternatives
            .iter()
            .any(|alternative| {
                alternative.guard
                    == [BorrowGuardAtom::Boolean {
                        parameter: 0,
                        expected: true,
                    }]
                    && alternative.relation == BorrowResultRelation::whole(1, BorrowAccess::Shared)
            })
    );
    assert!(
        signature
            .borrow_result_alternatives
            .iter()
            .any(|alternative| {
                alternative.guard
                    == [BorrowGuardAtom::Boolean {
                        parameter: 0,
                        expected: false,
                    }]
                    && alternative.relation == BorrowResultRelation::whole(2, BorrowAccess::Shared)
            })
    );
    let dump = output.vir().unwrap().stable_dump();
    assert!(dump.starts_with("vir-unit-v25\n"));
    assert!(dump.contains("borrow-result-alt0["));
    assert!(dump.contains("param0=true"));
    assert!(dump.contains("param0=false"));
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(40)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.runtime())
        .unwrap();
}

#[test]
fn boolean_guard_mutable_result_is_a_child_loan() {
    let output = analyze_checked(
        "fn main()->u64{let mut a=1;let mut b=2;let r=choose(true,&mut a,&mut b);*r=40;return a+b;}
         fn choose(flag:bool,a:&mut u64,b:&mut u64)->&mut u64{if flag{return a;}else{return b;}}",
    );
    let alternatives = &output.hir().unwrap().functions()[1]
        .signature
        .borrow_result_alternatives;
    assert_eq!(alternatives.len(), 2);
    assert!(
        alternatives
            .iter()
            .all(|alternative| alternative.relation.access == BorrowAccess::Mutable)
    );
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.runtime())
        .unwrap();
}

#[test]
fn unknown_guard_keeps_worlds_and_restores_only_the_unselected_mutable_source() {
    let source =
        "fn main()->u64{let mut a=1;let mut b=2;let x=use_choice(true,&mut a,&mut b);let mut c=3;let mut d=4;let y=use_choice(false,&mut c,&mut d);return x+y;}
         fn use_choice(flag:bool,a:&mut u64,b:&mut u64)->u64{let r=choose(flag,a,b);if flag{let x=*b;*r=40;return x;}else{let x=*a;*r=40;return x;}}
         fn choose(flag:bool,a:&mut u64,b:&mut u64)->&mut u64{if flag{return a;}else{return b;}}";
    let output = analyze_checked(source);
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(5)]
    );
}

#[test]
fn guard_reassignment_and_selected_mutable_access_fail_closed() {
    let reassigned = analyze(&SourceFile::from_text(
        "guard-reassigned.nera",
        "fn main()->u64{return 0;} fn choose(mut flag:bool,a:&u64,b:&u64)->&u64{flag=false;if flag{return a;}else{return b;}}",
    ));
    assert!(matches!(
        reassigned.status(),
        FrontendStatus::Invalid | FrontendStatus::Unsupported
    ));

    let selected = SourceFile::from_text(
        "selected-conflict.nera",
        "fn main()->u64{let mut a=1;let mut b=2;return bad(true,&mut a,&mut b);} fn bad(flag:bool,a:&mut u64,b:&mut u64)->u64{let r=choose(flag,a,b);if flag{let x=*a;*r=40;return x;}else{let x=*b;*r=40;return x;}} fn choose(flag:bool,a:&mut u64,b:&mut u64)->&mut u64{if flag{return a;}else{return b;}}",
    );
    let report = verify_source(&selected, Default::default());
    assert!(!report.is_checked());
}

#[test]
fn reverse_sources_and_same_allocation_shared_aliases_keep_token_identity() {
    let output = analyze_checked(
        "fn main()->u64{let value=21;let a=&value;let b=&value;let r=reverse(false,a,b);return *r;}
         fn reverse(flag:bool,a:&u64,b:&u64)->&u64{if flag{return b;}else{return a;}}",
    );
    let alternatives = &output.hir().unwrap().functions()[1]
        .signature
        .borrow_result_alternatives;
    assert!(alternatives.iter().any(|alternative| {
        alternative.guard
            == [BorrowGuardAtom::Boolean {
                parameter: 0,
                expected: false,
            }]
            && alternative.relation == BorrowResultRelation::whole(1, BorrowAccess::Shared)
    }));
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(21)]
    );
}

#[test]
fn same_allocation_mutable_candidates_and_alternative_budget_fail_closed() {
    let aliased = SourceFile::from_text(
        "mutable-alias.nera",
        "fn main()->u64{let mut value=1;let a=&mut value;let b=&mut value;let r=choose(true,a,b);return *r;}
         fn choose(flag:bool,a:&mut u64,b:&mut u64)->&mut u64{if flag{return a;}else{return b;}}",
    );
    assert!(!verify_source(&aliased, Default::default()).is_checked());

    let over_budget = analyze(&SourceFile::from_text(
        "conditional-budget.nera",
        "fn main()->u64{return 0;}
         fn choose(p:bool,q:bool,r:bool,a:&u64,b:&u64,c:&u64,d:&u64,e:&u64)->&u64{
           if p{if q{return a;}else{return b;}}
           else{if q{return c;}else{if r{return d;}else{return e;}}}
         }",
    ));
    assert_eq!(over_budget.status(), FrontendStatus::Unsupported);
}
