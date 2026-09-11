use nera::verification::{TextReportMode, render_text, verify_source};
use nera::{
    BorrowAccess, BorrowResultRelation, FrontendStatus, MAX_BORROW_SOURCE_SCC_FUNCTIONS,
    SourceFile, VirRuntimeValue, analyze, interpret,
};

fn checked(source: &str, expected: u64) -> nera::frontend::FrontendOutput {
    let file = SourceFile::from_text("borrow-source-scc.nera", source);
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
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(expected)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.runtime())
        .unwrap();
    output
}

#[test]
fn recursive_source_budget_fails_before_any_component_is_published() {
    let count = MAX_BORROW_SOURCE_SCC_FUNCTIONS + 1;
    let mut source = String::from("fn main()->u64{return 0;}");
    for index in 0..count {
        source.push_str(&format!(
            "fn f{index}(a:&u64)->&u64{{return f{}(a);}}",
            (index + 1) % count
        ));
    }
    let file = SourceFile::from_text("borrow-source-budget.nera", source);
    let first = analyze(&file);
    let second = analyze(&file);
    assert_eq!(first.status(), FrontendStatus::Unsupported);
    assert_eq!(first.status(), second.status());
    assert_eq!(
        format!("{:?}", first.issues()),
        format!("{:?}", second.issues())
    );
    assert!(first.issues().iter().any(|issue| {
        issue
            .diagnostic()
            .message()
            .contains("exceeds the function budget")
    }));
    assert!(first.hir().is_none() && first.vir().is_none());
}

fn relation(output: &nera::frontend::FrontendOutput, name: &str) -> BorrowResultRelation {
    output
        .hir()
        .unwrap()
        .functions()
        .iter()
        .find(|function| function.name == name)
        .unwrap()
        .signature
        .borrow_result
        .unwrap()
}

#[test]
fn self_and_mutual_recursion_close_from_real_base_returns() {
    let self_recursive = checked(
        "fn main()->u64{let a=42;let b=7;let r=pick(1,&a,&b);return *r;}
         fn pick(n:u64,a:&u64,b:&u64)->&u64{if n==0{return a;}return pick(0,a,b);}",
        42,
    );
    assert_eq!(
        relation(&self_recursive, "pick"),
        BorrowResultRelation::whole(1, BorrowAccess::Shared)
    );

    let mutual = checked(
        "fn main()->u64{let a=42;let b=7;let r=left(1,&a,&b);return *r;}
         fn left(n:u64,a:&u64,b:&u64)->&u64{if n==0{return a;}return right(0,a,b);}
         fn right(n:u64,a:&u64,b:&u64)->&u64{if n==0{return a;}return left(0,a,b);}",
        42,
    );
    for name in ["left", "right"] {
        assert_eq!(
            relation(&mutual, name),
            BorrowResultRelation::whole(1, BorrowAccess::Shared)
        );
    }
}

#[test]
fn loop_fixed_point_handles_early_exit_and_loop_carried_reborrow() {
    let output = checked(
        "fn main()->u64{let a=42;let b=7;let r=through(2,&a,&b);return *r;}
         fn through(n:u64,a:&u64,b:&u64)->&u64{
           let current=a;let mut i=0;
           while i<n{if i==1{return &*current;}i=i+1;if i==9{break;}continue;}
           return current;
         }",
        42,
    );
    assert_eq!(
        relation(&output, "through"),
        BorrowResultRelation::whole(1, BorrowAccess::Shared)
    );
}

#[test]
fn loop_source_switch_and_source_only_recursive_cycle_fail_closed_deterministically() {
    for (name, source, message) in [
        (
            "loop-switch",
            "fn main()->u64{return 0;} fn choose(flag:bool,a:&u64,b:&u64)->&u64{let mut current=a;while flag{current=b;break;}return current;}",
            "multiple path-dependent",
        ),
        (
            "source-cycle",
            "fn main()->u64{return 0;} fn left(a:&u64,b:&u64)->&u64{return right(a,b);} fn right(a:&u64,b:&u64)->&u64{return left(a,b);}",
            "non-returning borrow SCC",
        ),
        (
            "unsafe-branch",
            "fn main()->u64{return 0;} fn bad(flag:bool,a:&u64,b:&u64)->&u64{if flag{let p=alloc<u64>(1);free(p);return &*p;}return bad(true,a,b);}",
            "projection",
        ),
    ] {
        let file = SourceFile::from_text(name, source);
        let first = analyze(&file);
        let second = analyze(&file);
        assert!(
            matches!(
                first.status(),
                FrontendStatus::Invalid | FrontendStatus::Unsupported
            ),
            "{name}: {:?}",
            first.issues()
        );
        assert_eq!(first.status(), second.status());
        assert_eq!(
            format!("{:?}", first.issues()),
            format!("{:?}", second.issues())
        );
        assert!(
            first
                .issues()
                .iter()
                .any(|issue| issue.diagnostic().message().contains(message)),
            "{name}: {:?}",
            first.issues()
        );
        assert!(first.vir().is_none());
    }
}

#[test]
fn syntactically_non_returning_single_source_gets_only_a_vacuous_abi_shape() {
    let source = SourceFile::from_text(
        "no-normal-return.nera",
        "fn main()->u64{return 0;} fn spin(a:&u64)->&u64{return spin(a);}",
    );
    let output = analyze(&source);
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    assert_eq!(
        relation(&output, "spin"),
        BorrowResultRelation::whole(0, BorrowAccess::Shared)
    );
    let report = verify_source(&source, Default::default());
    assert!(
        report.is_checked(),
        "{}",
        render_text(&report, TextReportMode::Explain)
    );

    let unsafe_source = SourceFile::from_text(
        "no-return-uaf.nera",
        "fn main()->u64{return 0;} fn spin(a:&u64)->&u64{let p=alloc<u64>(1);free(p);let x=*p;return spin(a);}",
    );
    let unsafe_output = analyze(&unsafe_source);
    assert_eq!(
        unsafe_output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        unsafe_output.issues()
    );
    assert!(!verify_source(&unsafe_source, Default::default()).is_checked());

    let fallthrough = analyze(&SourceFile::from_text(
        "borrow-fallthrough.nera",
        "fn main()->u64{return 0;} fn missing(a:&u64)->&u64{}",
    ));
    assert_eq!(fallthrough.status(), FrontendStatus::Invalid);
    assert!(fallthrough.hir().is_none() && fallthrough.vir().is_none());
}
