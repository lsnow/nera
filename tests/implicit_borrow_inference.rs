use nera::session::CompilerSession;
use nera::source::{SourceDatabase, SourceInput};
use nera::verification::{TextReportMode, render_text, verify_source};
use nera::{
    BorrowAccess, BorrowResultRelation, FrontendStatus, SourceFile, VirRuntimeValue, analyze,
    interpret,
};

#[path = "support/cli_process.rs"]
mod cli_process;

fn checked(source: &str, value: u64) -> nera::frontend::FrontendOutput {
    let file = SourceFile::from_text("implicit-borrow.nera", source);
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
        [VirRuntimeValue::U64(value)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.runtime())
        .unwrap();
    output
}

#[test]
fn direct_and_local_forwarding_infer_one_shared_or_mutable_source() {
    let shared = checked(
        "fn main()->u64{let mut a=40;let mut b=1;let r=forward(&a,&b);b=2;return *r+b;}
         fn forward(a:&u64,b:&u64)->&u64{let selected=first(a,b);return selected;}
         fn first(a:&u64,b:&u64)->&u64{return a;}",
        42,
    );
    for name in ["forward", "first"] {
        let function = shared
            .hir()
            .unwrap()
            .functions()
            .iter()
            .find(|function| function.name == name)
            .unwrap();
        assert_eq!(
            function.signature.borrow_result,
            Some(BorrowResultRelation::whole(0, BorrowAccess::Shared))
        );
    }

    let second = checked(
        "fn main()->u64{let a=1;let b=42;let r=second(&a,&b);return *r;} fn second(a:&u64,b:&u64)->&u64{return b;}",
        42,
    );
    assert_eq!(
        second.hir().unwrap().functions()[1].signature.borrow_result,
        Some(BorrowResultRelation::whole(1, BorrowAccess::Shared))
    );
    checked(
        "fn main()->u64{let a=42;let b=7;let r=same(false,&a,&b);return *r;} fn same(flag:bool,a:&u64,b:&u64)->&u64{if flag{return a;}return a;}",
        42,
    );
    checked(
        "fn main()->u64{let a=42;let b=7;let p=alloc<u64>(1);*p=1;let r=consume(&a,&b,p);return *r;} fn consume(a:&u64,b:&u64,p:Own<u64>)->&u64{let observed=*b;free(p);return a;}",
        42,
    );
    checked(
        "fn main()->u64{let a=[40,2];let b=[7];let r=first_slice(&a[..],&b[..]);return r[0]+r[1];} fn first_slice(a:&[u64],b:&[u64])->&[u64]{return a;}",
        42,
    );
    checked(
        "fn main()->u64{let mut a=[1,2];let mut b=[7];let r=first_slice_mut(&mut a[..],&mut b[..]);r[0]=40;return a[0]+a[1];} fn first_slice_mut(a:&mut [u64],b:&mut [u64])->&mut [u64]{return a;}",
        42,
    );
    let mutable = checked(
        "fn main()->u64{let mut a=1;let mut b=1;let r=first_mut(&mut a,&mut b);*r=40;return a+b;}
         fn first_mut(a:&mut u64,b:&mut u64)->&mut u64{*b=2;return a;}",
        42,
    );
    let function = &mutable.hir().unwrap().functions()[1];
    assert_eq!(
        function.signature.borrow_result,
        Some(BorrowResultRelation::whole(0, BorrowAccess::Mutable))
    );
    let abi = &mutable.vir().unwrap().as_unit().runtime.abis.functions[1].signature;
    assert_eq!(abi.borrow_result_parameter(), Some(0));
    assert!(abi.parameters()[0].result_slots().is_empty());
    assert!(!abi.parameters()[1].result_slots().is_empty());
}

#[test]
fn forward_reference_parameter_and_generic_instance_close_nonrecursive_dependencies() {
    let output = checked(
        "fn main()->u64{let a=7;let b=42;let r=outer<u64>(&a,&b);return *r;}
         fn outer<T>(a:&T,b:&T)->&T{return inner<T>(b,a);}
         fn inner<T>(a:&T,b:&T)->&T{return a;}",
        42,
    );
    let inferred: Vec<_> = output
        .hir()
        .unwrap()
        .functions()
        .iter()
        .filter(|function| function.signature.borrow_result.is_some())
        .map(|function| {
            (
                function.name.as_str(),
                function.signature.borrow_result.unwrap(),
            )
        })
        .collect();
    assert_eq!(inferred.len(), 2);
    assert_eq!(
        inferred
            .iter()
            .find(|(name, _)| name.contains("outer"))
            .unwrap()
            .1
            .parameter,
        1
    );
    assert_eq!(
        inferred
            .iter()
            .find(|(name, _)| name.contains("inner"))
            .unwrap()
            .1
            .parameter,
        0
    );
}

#[test]
fn cross_module_wrapper_uses_caller_coordinates_and_runs_natively() {
    let app = "module app; use lib::first; pub fn main()->u64{let mut a=40;let mut b=1;let r=wrap(&a,&b);b=2;return *r+b;} fn wrap(a:&u64,b:&u64)->&u64{return first(a,b);}";
    let lib = "module lib; pub fn first(a:&u64,b:&u64)->&u64{return a;}";
    let session = CompilerSession::modules(
        SourceDatabase::new(vec![
            SourceInput::new("app", SourceFile::from_text("app.nera", app)),
            SourceInput::new("lib", SourceFile::from_text("lib.nera", lib)),
        ])
        .unwrap(),
        Default::default(),
        "app::main",
    )
    .unwrap();
    let analysis = session.analyze("app").unwrap();
    assert_eq!(
        analysis.frontend().status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        analysis.frontend().issues()
    );
    assert!(session.verify("app").unwrap().is_checked());
    assert_eq!(
        interpret(
            analysis
                .frontend()
                .vir()
                .unwrap()
                .resolve()
                .unwrap()
                .runtime()
        )
        .unwrap()
        .values(),
        [VirRuntimeValue::U64(42)]
    );

    let fixture = cli_process::Fixture::new();
    fixture.file("app.nera", app);
    fixture.file("lib.nera", lib);
    let args = [
        "--module",
        "app=app.nera",
        "--module",
        "lib=lib.nera",
        "--entry",
        "app::main",
    ];
    let build = cli_process::run(
        fixture
            .command()
            .arg("build")
            .args(args)
            .args(["--emit", "exe", "-o", "native"]),
    );
    assert!(build.status.success(), "{build:?}");
    assert_eq!(
        std::process::Command::new(fixture.0.join("native"))
            .status()
            .unwrap()
            .code(),
        Some(42)
    );
}

#[test]
fn local_escape_and_unrepresentable_conditional_sources_fail_closed() {
    for (name, source, status, message) in [
        (
            "local",
            "fn main()->u64{return 42;} fn bad(a:&u64,b:&u64)->&u64{let local=1;return &local;}",
            FrontendStatus::Invalid,
            "local storage",
        ),
        (
            "conditional",
            "fn main()->u64{return 42;} fn choose(flag:bool,a:&u64,b:&u64)->&u64{if flag{return a;}return b;}",
            FrontendStatus::Unsupported,
            "multiple path-dependent",
        ),
    ] {
        let output = analyze(&SourceFile::from_text(name, source));
        assert_eq!(output.status(), status, "{name}: {:?}", output.issues());
        assert!(
            output
                .issues()
                .iter()
                .any(|issue| issue.diagnostic().message().contains(message)),
            "{name}: {:?}",
            output.issues()
        );
        assert!(output.vir().is_none());
    }
}

#[test]
fn aliased_arguments_do_not_allow_the_returned_storage_to_be_freed() {
    let source = SourceFile::from_text(
        "aliased-inputs.nera",
        "fn main()->u64{let p=alloc<u64>(1);*p=42;let r=first(&*p,&*p);free(p);return *r;} fn first(a:&u64,b:&u64)->&u64{return a;}",
    );
    let output = analyze(&source);
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let report = verify_source(&source, Default::default());
    assert!(
        !report.is_checked(),
        "{}",
        render_text(&report, TextReportMode::Explain)
    );
    assert!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime()).is_err(),
        "the independent runtime loan shadow must also reject early free"
    );
}
