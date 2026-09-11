use nera::session::CompilerSession;
use nera::source::{SourceDatabase, SourceInput};
use nera::verification::{TextReportMode, render_text, verify_source};
use nera::{FrontendStatus, SourceFile, VirRuntimeValue, analyze, interpret};

#[path = "support/cli_process.rs"]
mod cli_process;

const APP: &str = include_str!("../spec/cases/modules/generic-app.nera");
const VALUES: &str = include_str!("../spec/cases/modules/generic-values.nera");
const BORROW: &str = include_str!("../spec/cases/modules/generic-borrow.nera");

fn session(files: &[(&str, &str)]) -> CompilerSession {
    CompilerSession::modules(
        SourceDatabase::new(
            files
                .iter()
                .map(|(name, text)| {
                    SourceInput::new(*name, SourceFile::from_text(format!("{name}.nera"), text))
                })
                .collect(),
        )
        .unwrap(),
        Default::default(),
        "app::main",
    )
    .unwrap()
}

fn checked(text: &str, value: u64) -> nera::frontend::FrontendOutput {
    let source = SourceFile::from_text("generic.nera", text);
    let output = analyze(&source);
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let preview = verify_source(&source, Default::default());
    assert!(
        preview.is_checked(),
        "{}",
        render_text(&preview, TextReportMode::Explain)
    );
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        &[VirRuntimeValue::U64(value)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.runtime())
        .unwrap();
    output
}

#[test]
fn concrete_identity_reuse_and_const_normalization() {
    let output = checked(
        "struct Bag<T, const N: usize> { values: [T; N], } fn main()->u64 { let a = Bag<u64, 1+1>{values:[21;2]}; let b:Bag<u64,2> = id<Bag<u64,2>>(a); return b.values[0] + b.values[1]; } fn id<T>(x:T)->T { return x; }",
        42,
    );
    assert_eq!(output.instantiations().templates.len(), 2);
    assert_eq!(output.instantiations().instances.len(), 2);
    let id = output
        .instantiations()
        .instances
        .iter()
        .find(|i| i.key.definition == "crate::id")
        .unwrap();
    assert!(
        matches!(&id.key.arguments[0], nera::frontend::AstGenericArgument::Type(nera::frontend::AstType::Applied {name,..}) if name == "@crate::Bag")
    );
}

#[test]
fn owning_and_borrow_instances_use_existing_resource_checks() {
    checked(
        "fn main()->u64 { let p=alloc<u64>(1); *p=42; let q=id<Own<u64>>(p); let r = id<&u64>(&*q); let x=*r; free(q); return id<u64>(x); } fn id<T>(x:T)->T { return x; }",
        42,
    );
}

#[test]
fn mutable_reference_instances_and_inferred_signature_do_not_clone_for_local_regions() {
    let output = checked(
        "fn main()->u64 { let mut x=1; let r=id<&mut u64>(&mut x); *r=20; let mut y=2; let s=id<&mut u64>(&mut y); *s=22; return x+y; } fn id<T>(x:T)->T{return x;}",
        42,
    );
    assert_eq!(output.instantiations().instances.len(), 1);
    checked(
        "fn main()->u64 { let x=42; let r=id<u64>(&x); return *r; } fn id<T>(x:&T)->&T{return x;}",
        42,
    );
}

#[test]
fn template_body_is_checked_per_capability_not_once_for_copy() {
    checked(
        "fn main()->u64 {return duplicate<u64>(42);} fn duplicate<T>(x:T)->T{let other=x;return x;}",
        42,
    );
    for ty in ["Own<u64>", "&mut u64"] {
        let arg = if ty.starts_with("Own") {
            "let p=alloc<u64>(1);*p=42;let q=duplicate<Own<u64>>(p);free(q);"
        } else {
            "let mut x=42;let r=duplicate<&mut u64>(&mut x);"
        };
        let source = SourceFile::from_text(
            "move.nera",
            format!("fn main(){{{arg}return;}} fn duplicate<T>(x:T)->T{{let other=x;return x;}}"),
        );
        let output = analyze(&source);
        assert!(
            output.issues().iter().all(|i| !matches!(
                i.kind(),
                nera::frontend::FrontendIssueKind::Syntax
                    | nera::frontend::FrontendIssueKind::Lexical
            )),
            "{:?}",
            output.issues()
        );
        assert!(
            !verify_source(&source, Default::default()).is_checked(),
            "{ty}"
        );
    }
}

#[test]
fn const_substitution_and_checked_lengths() {
    checked(
        "fn main()->u64 {let b=make<u64,1>(21);return b[0]+b[1];} fn make<T,const N:usize>(x:T)->[T;N+1]{return [x;N+1];}",
        42,
    );
    for (source, message) in [
        (
            "fn main(){take<u64>();return;} fn take<const N:usize>(){return;}",
            "kind",
        ),
        ("fn main(){take<1>();return;} fn take<T>(){return;}", "kind"),
        (
            "fn main(){take<u64,1>();return;} fn take<T>(){return;}",
            "count",
        ),
        (
            "fn main(){take<u64>();return;} fn take(){return;}",
            "not a template",
        ),
        (
            "fn main(){take<u64>();return;} fn take<T>(){let x:[u64;M]=[1;M];return;}",
            "unresolved const",
        ),
        (
            "fn main(){take<18446744073709551615>();return;} fn take<const N:usize>(){let x=[1;N+1];return;}",
            "overflow",
        ),
        (
            "fn main(){take<1>();return;} fn take<const N:usize>(){let N=2;let x=N;return;}",
            "shadow",
        ),
        (
            "fn main(){take<1>();return;} fn take<const N:usize>(){for N in 0usize..1usize {let x=N;}return;}",
            "shadow",
        ),
        (
            "fn main(){take<1>();return;} fn take<const N:usize>(){match 0 {N=>{let x=N;},}return;}",
            "shadow",
        ),
        (
            "fn main(){take();return;} fn take<T>(){return;}",
            "explicit",
        ),
    ] {
        let source = SourceFile::from_text("const-error.nera", source);
        let output = analyze(&source);
        assert_ne!(
            output.status(),
            FrontendStatus::AcceptedProposal,
            "{source:?}"
        );
        assert!(
            format!("{:?}", output.issues()).contains(message),
            "{source:?}: {:?}",
            output.issues()
        );
    }
    let source = SourceFile::from_text(
        "bounds.nera",
        "fn main()->u64 {let a=make<2>();return a[2];} fn make<const N:usize>()->[u64;N]{return [1;N];}",
    );
    assert!(!verify_source(&source, Default::default()).is_checked());
}

#[test]
fn recursive_identity_and_expansion_budgets_are_replayable() {
    let source = SourceFile::from_text(
        "rec.nera",
        "fn main()->u64{return rec<u64>(1);} fn rec<T>(x:T)->T{return rec<T>(x);}",
    );
    let output = analyze(&source);
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    assert_eq!(output.instantiations().instances.len(), 1);
    assert_eq!(output, analyze(&source));
    for (source, message) in [
        (
            "fn main(){grow<0>();return;} fn grow<const N:usize>(){grow<N+1>();return;}",
            "instance budget",
        ),
        (
            "struct Loop<T>{next:Loop<T>,} fn main(){let mut x:Loop<u64>;return;}",
            "layout",
        ),
    ] {
        let source = SourceFile::from_text("rec-error.nera", source);
        let output = analyze(&source);
        assert_ne!(output.status(), FrontendStatus::AcceptedProposal);
        assert!(
            format!("{:?}", output.issues()).contains(message),
            "{:?}",
            output.issues()
        );
        assert_eq!(output, analyze(&source));
    }
}

#[test]
fn unused_templates_have_no_universal_verification_claim() {
    let source = SourceFile::from_text(
        "unused.nera",
        "fn main()->u64{return 42;} fn unused<T>(x:T)->T{return missing;} ",
    );
    let preview = verify_source(&source, Default::default());
    assert!(preview.is_checked());
    let report = preview.instantiations().unwrap();
    assert!(report.instances.is_empty());
    assert_eq!(report.uninstantiated().count(), 1);
    let text = render_text(&preview, TextReportMode::Summary);
    assert!(text.contains("uninstantiated template (not verified): crate::unused"));
    assert!(text.contains("never all template substitutions"));
}

#[test]
fn generic_parser_limits_and_unsupported_forms_fail_closed() {
    let output = checked(
        "struct Wrap<T>{value:T,} fn main()->u64 {let x:Wrap<Wrap<u64>>=Wrap<Wrap<u64>>{value:Wrap<u64>{value:42}};return x.value.value;}",
        42,
    );
    assert_eq!(output.cst().unwrap().tokens(), output.lexed().tokens());
    for (text, message) in [
        (
            "fn main(){return;} fn f<T,T>(){return;}",
            "duplicate generic binder",
        ),
        ("fn main(){return;} fn f<u64>(){return;}", "builtin type"),
        ("fn main(){return;} enum E<T>{Empty,}", "generic enums"),
        (
            "fn main(){return;} struct S<'a>{x:&'a u64,}",
            "explicit lifetime binders were removed",
        ),
        (
            "fn main(){f<&'a u64>();return;} fn f<T>(){return;}",
            "explicit lifetime annotations were removed",
        ),
        (
            "fn main(){f<1+18446744073709551615>();return;} fn f<const N:usize>(){return;}",
            "overflow",
        ),
    ] {
        let source = SourceFile::from_text("generic-boundary.nera", text);
        let output = analyze(&source);
        assert_ne!(output.status(), FrontendStatus::AcceptedProposal);
        assert!(
            format!("{:?}", output.issues()).contains(message),
            "{:?}",
            output.issues()
        );
    }
    for depth in [49, 256, 20_000] {
        let source = SourceFile::from_text(
            "depth.nera",
            format!(
                "fn main(){{let mut x:{}u64{};return;}} struct S<T>{{value:T,}}",
                "S<".repeat(depth),
                ">".repeat(depth)
            ),
        );
        let output = analyze(&source);
        assert_ne!(output.status(), FrontendStatus::AcceptedProposal);
        assert_eq!(output, analyze(&source));
        assert!(output.issues().iter().all(|issue| {
            issue
                .diagnostic()
                .primary_span()
                .is_none_or(|span| span.end() <= source.len())
        }));
    }
}

#[test]
fn generic_type_budget_does_not_reduce_existing_block_depth() {
    for (expression, template) in [
        ("42", ""),
        ("42", "fn unused<T>(x:T)->T{return x;}"),
        ("id<u64>(42)", "fn id<T>(x:T)->T{return x;}"),
    ] {
        let source = format!(
            "fn main()->u64 {{{}return {expression};{}}} {template}",
            "{".repeat(60),
            "}".repeat(60)
        );
        checked(&source, 42);
    }
}

#[test]
fn module_instances_keep_canonical_identity_sources_and_config_binding() {
    let compiler = session(&[("app", APP), ("values", VALUES), ("borrow", BORROW)]);
    let analysis = compiler.analyze("app").unwrap();
    let output = analysis.frontend();
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    assert_eq!(output.instantiations().instances.len(), 3);
    let preview = compiler.verify("app").unwrap();
    assert!(
        preview.is_checked(),
        "{}",
        render_text(&preview, TextReportMode::Explain)
    );
    let reordered = session(&[("borrow", BORROW), ("values", VALUES), ("app", APP)]);
    assert_eq!(analysis, reordered.analyze("app").unwrap());
    assert_eq!(preview, reordered.verify("app").unwrap());
    assert!(preview.matches_session(&compiler, "app"));
    let changed = APP.replace("1 + 1", "3");
    assert!(!preview.matches_session(
        &session(&[("app", &changed), ("values", VALUES), ("borrow", BORROW)]),
        "app"
    ));
    for instance in &output.instantiations().instances {
        assert!(
            analysis
                .locate_file_span(instance.source, instance.definition_span)
                .is_some()
        );
        for usage in &instance.uses {
            assert!(
                analysis
                    .locate_file_span(usage.source, usage.span)
                    .is_some()
            );
        }
    }
    let app = "module app; use library::id; struct Local{x:u64,} fn main()->u64{let x=id<Local>(Local{x:42});return x.x;}";
    let lib = "module library; pub fn id<T>(x:T)->T{return x;}";
    assert!(
        session(&[("app", app), ("library", lib)])
            .verify("app")
            .unwrap()
            .is_checked()
    );
}

#[test]
fn real_cli_generic_modules_share_interpreter_and_native_semantics() {
    let fixture = cli_process::Fixture::new();
    fixture.file("app.nera", APP);
    fixture.file("values.nera", VALUES);
    fixture.file("borrow.nera", BORROW);
    let args = [
        "--module",
        "app=app.nera",
        "--module",
        "values=values.nera",
        "--module",
        "borrow=borrow.nera",
        "--entry",
        "app::main",
    ];
    for command in ["frontend", "verify", "run"] {
        let output = cli_process::run(fixture.command().arg(command).args(args));
        assert!(output.status.success(), "{command}: {output:?}");
        if command == "run" {
            assert!(String::from_utf8_lossy(&output.stdout).contains("42"));
        }
    }
    if cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        let output = cli_process::run(
            fixture
                .command()
                .arg("build")
                .args(args)
                .args(["--emit", "exe", "-o", "native"]),
        );
        assert!(output.status.success(), "{output:?}");
        assert_eq!(
            std::process::Command::new(fixture.0.join("native"))
                .output()
                .unwrap()
                .status
                .code(),
            Some(42)
        );
    }
    fixture.file(
        "borrow.nera",
        BORROW.replace("return value;", "let local=42; return &local;"),
    );
    let output = cli_process::run(fixture.command().arg("verify").args(args));
    assert!(!output.status.success());
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(text.contains("borrow.nera"), "{text}");
}
