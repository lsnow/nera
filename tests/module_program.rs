use nera::session::CompilerSession;
use nera::source::{SourceDatabase, SourceInput};
use nera::verification::{TextReportMode, render_text};
use nera::{FrontendStatus, SourceFile, VirRuntimeValue, analyze, interpret};

#[path = "support/cli_process.rs"]
mod cli_process;

const APP: &str = "module app; use lib::compute; fn helper()->u64 { return 2; } fn main()->u64 { return compute() + helper(); }";
const LIB: &str = "module lib; fn helper()->u64 { return 40; } pub fn compute()->u64 { let p = alloc<u64>(1); *p = helper(); let x = *p; free(p); return x; }";

fn session(files: &[(&str, &str)], entry: &str) -> CompilerSession {
    let inputs = files
        .iter()
        .map(|(name, text)| {
            SourceInput::new(*name, SourceFile::from_text(format!("{name}.nera"), text))
        })
        .collect();
    CompilerSession::modules(
        SourceDatabase::new(inputs).unwrap(),
        Default::default(),
        entry,
    )
    .unwrap()
}

#[test]
fn closed_module_program_retains_owners_and_uses_every_consumer() {
    let compiler = session(&[("app", APP), ("lib", LIB)], "app::main");
    let analysis = compiler.analyze("app").unwrap();
    let output = analysis.frontend();
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let hir = output.hir().unwrap();
    assert_eq!(hir.modules().len(), 2);
    assert_eq!(hir.functions().len(), 4);
    assert_ne!(hir.functions()[0].module, hir.functions()[2].module);
    assert_eq!(output.files().len(), 2);
    let unit = output.vir().unwrap();
    assert_eq!(unit.as_unit().source_map.sources().len(), 2);
    let resolved = unit.resolve().unwrap();
    let execution = interpret(resolved.runtime()).unwrap();
    assert_eq!(execution.values(), &[VirRuntimeValue::U64(42)]);
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .unwrap();
    let preview = compiler.verify("app").unwrap();
    assert!(
        preview.is_checked(),
        "{}",
        render_text(&preview, TextReportMode::Explain)
    );
    assert_eq!(preview.counts().unwrap().functions, 4);
    assert!(render_text(&preview, TextReportMode::Summary).contains("closed module program"));
    let reordered = session(&[("lib", LIB), ("app", APP)], "app::main");
    assert_eq!(analysis, reordered.analyze("app").unwrap());
    assert_eq!(preview, reordered.verify("app").unwrap());
    // The configured entry need not belong to source/module zero.
    let library_entry = session(&[("app", APP), ("lib", LIB)], "lib::compute");
    let selected = library_entry.analyze("lib").unwrap();
    assert_eq!(
        selected.frontend().hir().unwrap().entry_module_id().get(),
        1
    );
    assert!(library_entry.verify("lib").unwrap().is_checked());
    assert_eq!(
        interpret(
            selected
                .frontend()
                .vir()
                .unwrap()
                .resolve()
                .unwrap()
                .runtime()
        )
        .unwrap()
        .values(),
        &[VirRuntimeValue::U64(40)]
    );
}

#[test]
fn visibility_imports_and_graph_errors_fail_before_hir() {
    for (app, lib, message, status) in [
        (
            "module app; use lib::hidden; fn main(){ hidden(); return; }",
            "module lib; fn hidden(){ return; }",
            "private",
            FrontendStatus::Invalid,
        ),
        (
            "module app; use missing::f; fn main(){ return; }",
            LIB,
            "missing module",
            FrontendStatus::Invalid,
        ),
        (
            "module app; use lib::compute; use lib::compute; fn main(){ return; }",
            LIB,
            "duplicate import",
            FrontendStatus::Invalid,
        ),
        (
            "module app; use lib::compute; fn compute(){ return; } fn main(){ return; }",
            LIB,
            "conflicts",
            FrontendStatus::Invalid,
        ),
        (
            APP,
            "module lib; pub fn compute()->u64 {return 1;} pub fn compute()->u64{return 2;}",
            "duplicate",
            FrontendStatus::Invalid,
        ),
        (
            APP,
            "module wrong; pub fn compute()->u64 {return 1;}",
            "mapping",
            FrontendStatus::Invalid,
        ),
        (
            "module app; use lib::compute; pub fn main()->u64 {return compute();}",
            "module lib; use app::main; pub fn compute()->u64 {return main();}",
            "cycles",
            FrontendStatus::Unsupported,
        ),
        (
            "module app; fn main(){return;}",
            "module lib; struct Hidden { n: u64, } pub fn expose(x: Hidden){return;}",
            "private type escapes",
            FrontendStatus::Invalid,
        ),
        (
            "module app; fn main(){return;}",
            "module lib; struct Hidden { n: u64, } pub fn expose(x: Own<Hidden>){return;}",
            "private type escapes",
            FrontendStatus::Invalid,
        ),
        (
            "module app; fn main(){return;}",
            "module lib; struct Hidden { n: u64, } pub fn expose(x: ptr<Hidden>){return;}",
            "private type escapes",
            FrontendStatus::Invalid,
        ),
        (
            "module app; fn main(){return;}",
            "module lib; struct Hidden { n: u64, } pub struct Exposed { x: [Hidden; 1], }",
            "private type escapes",
            FrontendStatus::Invalid,
        ),
    ] {
        let compiler = session(&[("app", app), ("lib", lib)], "app::main");
        let result = compiler.analyze("app").unwrap();
        assert_eq!(
            result.frontend().status(),
            status,
            "{:?}",
            result.frontend().issues()
        );
        assert!(result.frontend().hir().is_none());
        assert!(result.frontend().vir().is_none());
        assert!(
            result.frontend().issues()[0]
                .diagnostic()
                .message()
                .contains(message),
            "{:?}",
            result.frontend().issues()
        );
        assert!(!compiler.verify("app").unwrap().is_checked());
    }
}

#[test]
fn module_nominal_identity_and_type_only_dependency_are_preserved() {
    let compiler = session(
        &[
            (
                "app",
                "module app; use types::Value; fn main()->u64 { let v = Value { n: 42 }; return v.n; }",
            ),
            ("types", "module types; pub struct Value { n: u64, }"),
            (
                "other",
                "module other; struct Value { n: u64, } fn keep()->u64 { let v = Value { n: 3 }; return v.n; }",
            ),
        ],
        "app::main",
    );
    let result = compiler.analyze("app").unwrap();
    assert_eq!(
        result.frontend().status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        result.frontend().issues()
    );
    let hir = result.frontend().hir().unwrap();
    assert_eq!(hir.modules().len(), 3);
    let named: Vec<_> = hir
        .types()
        .iter()
        .filter(|ty| ty.name.as_deref() == Some("Value"))
        .collect();
    assert_eq!(named.len(), 2);
    assert_ne!(named[0].id, named[1].id);
    assert!(compiler.verify("app").unwrap().is_checked());
}

#[test]
fn dependency_diagnostics_and_generated_origins_use_exact_snapshot_file() {
    let bad = "module lib; pub fn compute()->u64 { let p = alloc<u64>(1); free(p); return *p; }";
    let compiler = session(&[("app", APP), ("lib", bad)], "app::main");
    let preview = compiler.verify("app").unwrap();
    assert!(!preview.is_checked());
    let text = render_text(&preview, TextReportMode::Explain);
    assert!(text.contains("lib.nera"), "{text}");
    assert!(text.contains("return *p"), "{text}");
    let source = compiler.analyze("app").unwrap();
    let map = &source.frontend().vir().unwrap().as_unit().source_map;
    for origin in map.origins() {
        let span = map.source_span_for_origin(origin.id).unwrap();
        let located = source.locate_vir_span(span).unwrap();
        assert_eq!(
            map.source(span.source).unwrap().name,
            compiler
                .sources()
                .source(located.source)
                .unwrap()
                .path()
                .to_string_lossy()
        );
    }
    let invalid = session(
        &[
            ("app", APP),
            (
                "lib",
                "module lib; pub fn compute()->u64 { return missing; }",
            ),
        ],
        "app::main",
    );
    let analysis = invalid.analyze("app").unwrap();
    assert_eq!(
        analysis.issues().next().unwrap().location.unwrap().source,
        invalid.sources().id("lib").unwrap()
    );
    assert!(
        render_text(&invalid.verify("app").unwrap(), TextReportMode::Summary).contains("lib.nera")
    );
}

#[test]
fn explicit_entry_and_function_recursion_are_independent_of_module_dag() {
    let compiler = session(
        &[(
            "app",
            "module app; fn down(n:u64)->u64 { if n == 3 { return 42; } return down(n + 1); } fn main()->u64 { return down(0); }",
        )],
        "app::main",
    );
    let result = compiler.analyze("app").unwrap();
    assert_eq!(
        result.frontend().status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        result.frontend().issues()
    );
    assert!(compiler.verify("app").unwrap().is_checked());
    let missing = session(&[("app", APP), ("lib", LIB)], "app::missing");
    assert!(missing.analyze("app").unwrap().frontend().hir().is_none());
    assert!(!compiler.verify("app").unwrap().matches_session(
        &session(&[("app", "fn main()->u64{return 42;}")], "app::main"),
        "app"
    ));
    assert_eq!(
        analyze(&SourceFile::from_text(
            "single.nera",
            "fn main()->u64{return 42;}"
        ))
        .status(),
        FrontendStatus::AcceptedProposal
    );
}

#[test]
fn real_cli_module_inputs_verify_run_and_native_differential() {
    let fixture = cli_process::Fixture::new();
    fixture.file("app.nera", APP);
    fixture.file("lib.nera", LIB);
    let args = [
        "--module",
        "lib=lib.nera",
        "--module",
        "app=app.nera",
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
        let built = cli_process::run(
            fixture
                .command()
                .arg("build")
                .args(args)
                .args(["--emit", "exe", "-o", "native"]),
        );
        assert!(built.status.success(), "{built:?}");
        let execution = std::process::Command::new(fixture.0.join("native"))
            .output()
            .unwrap();
        assert_eq!(execution.status.code(), Some(42));
    }
    for extra in [
        vec!["--module", "app=app.nera"],
        vec!["--entry", "lib::compute"],
        vec!["extra.nera"],
        vec!["--unknown"],
    ] {
        let output = cli_process::run(fixture.command().arg("verify").args(args).args(extra));
        assert_eq!(output.status.code(), Some(2), "{output:?}");
    }
    let protected = cli_process::run(
        fixture
            .command()
            .arg("build")
            .args(args)
            .args(["--emit", "asm", "-o", "lib.nera"]),
    );
    assert_eq!(protected.status.code(), Some(2));
    assert_eq!(
        std::fs::read_to_string(fixture.0.join("lib.nera")).unwrap(),
        LIB
    );
    fixture.file(
        "lib.nera",
        "module lib; pub fn compute()->u64 {let p=alloc<u64>(1);free(p);return *p;}",
    );
    let fault = cli_process::run(fixture.command().arg("run").args(args));
    assert!(!fault.status.success());
    assert!(
        String::from_utf8_lossy(&fault.stderr).contains("execution fault (unverified) lib.nera:"),
        "{fault:?}"
    );
}

#[test]
fn cross_module_borrow_enum_and_nominal_mismatch_use_existing_type_rules() {
    let app = "module app; use lib::bump; use lib::read; use types::Choice; fn main()->u64 { let mut n: u64 = 41; bump(&mut n); let c = Choice::Some(read(&n)); match c { Choice::Some(x) => { return x; }, Choice::None => { return 0; }, } }";
    let library = "module lib; pub fn bump(p:&mut u64) { *p = *p + 1; return; } pub fn read(p:&u64)->u64 { return *p; }";
    let types = "module types; pub enum Choice { Some(u64), None, }";
    let compiler = session(
        &[("app", app), ("lib", library), ("types", types)],
        "app::main",
    );
    let analysis = compiler.analyze("app").unwrap();
    assert_eq!(
        analysis.frontend().status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        analysis.frontend().issues()
    );
    let preview = compiler.verify("app").unwrap();
    assert!(
        preview.is_checked(),
        "{}",
        render_text(&preview, TextReportMode::Explain)
    );
    let resolved = analysis.frontend().vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        &[VirRuntimeValue::U64(42)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .unwrap();
    for function in analysis.frontend().hir().unwrap().functions() {
        let location = analysis
            .locate_hir_span(function.module, function.span)
            .unwrap();
        assert!(
            compiler.sources().source(location.source).unwrap().bytes()
                [location.span.start()..location.span.end()]
                .starts_with(b"fn ")
        );
    }
    let mismatch = session(
        &[
            (
                "app",
                "module app; use lib::make; struct Value { n:u64, } fn main(){ let x: Value = make(); return; }",
            ),
            (
                "lib",
                "module lib; pub struct Value { n:u64, } pub fn make()->Value { return Value { n:42 }; }",
            ),
        ],
        "app::main",
    );
    assert_eq!(
        mismatch.analyze("app").unwrap().frontend().status(),
        FrontendStatus::Invalid
    );
}

#[test]
fn source_set_identity_snapshot_and_unreachable_errors_are_fail_closed() {
    let compiler = session(&[("app", APP), ("lib", LIB)], "app::main");
    let old = compiler.verify("app").unwrap();
    assert!(!old.matches_session(
        &session(
            &[("app", APP), ("lib", &LIB.replace("40", "39"))],
            "app::main"
        ),
        "app"
    ));
    assert!(!old.matches_session(
        &session(&[("app", APP), ("lib", LIB)], "app::helper"),
        "app"
    ));
    let invalid = session(
        &[
            ("app", "module app; fn main()->u64{return 42;}"),
            (
                "z",
                "module z; fn bad()->u64 {let p=alloc<u64>(1);free(p);return *p;}",
            ),
        ],
        "app::main",
    );
    let result = invalid.verify("app").unwrap();
    assert!(!result.is_checked());
    assert!(render_text(&result, TextReportMode::Explain).contains("z.nera"));
    let fixture = cli_process::Fixture::new();
    let path = fixture.file("lib.nera", LIB);
    let inputs = SourceDatabase::new(vec![
        SourceInput::new("app", SourceFile::from_text("app.nera", APP)),
        SourceInput::new("lib", SourceFile::load(&path).unwrap()),
    ])
    .unwrap();
    let snapshot = CompilerSession::modules(inputs, Default::default(), "app::main").unwrap();
    let report = snapshot.verify("app").unwrap();
    let before = render_text(&report, TextReportMode::Explain);
    std::fs::write(path, "disk changed after snapshot").unwrap();
    assert_eq!(before, render_text(&report, TextReportMode::Explain));
    assert!(snapshot.verify("app").unwrap().is_checked());
    let independent = CompilerSession::new(snapshot.sources().clone(), Default::default()).unwrap();
    let selected = independent.analyze("lib").unwrap();
    let file = &selected.frontend().files()[0];
    let located = selected
        .locate_file_span(file.source, file.ast.span())
        .unwrap();
    assert_eq!(located.source, independent.sources().id("lib").unwrap());
}

#[test]
fn nested_modules_layout_failures_and_restricted_import_forms_are_explicit() {
    let nested = session(
        &[
            (
                "app",
                "module app; use util::numbers::answer; fn main()->u64 {return answer();}",
            ),
            (
                "util/numbers",
                "module util::numbers; pub fn answer()->u64{return 42;}",
            ),
        ],
        "app::main",
    );
    assert!(nested.verify("app").unwrap().is_checked());
    let implicit = session(
        &[
            (
                "app",
                "use types::Value; fn main()->u64 {let v = Value {n:42}; return v.n;}",
            ),
            ("types", "pub struct Value {n:u64,}"),
            ("empty", ""),
        ],
        "app::main",
    );
    assert!(implicit.verify("app").unwrap().is_checked());
    for code in [
        "module types; pub struct Broken { x: [u64; 18446744073709551615], }",
        "module types; pub struct Broken { x: Broken, }",
    ] {
        let compiler = session(
            &[
                (
                    "app",
                    "module app; use types::Broken; struct Wrap { x: Broken, } fn main(){return;}",
                ),
                ("types", code),
            ],
            "app::main",
        );
        let result = compiler.analyze("app").unwrap();
        assert_eq!(result.frontend().status(), FrontendStatus::Invalid);
        let location = result.issues().next().unwrap().location.unwrap();
        assert_eq!(location.source, compiler.sources().id("types").unwrap());
        assert!(location.span.end() <= code.len());
    }
    for import in [
        "use lib::*;",
        "use lib::{compute};",
        "pub use lib::compute;",
    ] {
        let code = format!("module app; {import} fn main(){{return;}}");
        let compiler = session(&[("app", &code), ("lib", LIB)], "app::main");
        assert_eq!(
            compiler.analyze("app").unwrap().frontend().status(),
            FrontendStatus::Unsupported
        );
    }
    let bytes = SourceDatabase::new(vec![
        SourceInput::new("app", SourceFile::from_text("app.nera", APP)),
        SourceInput::new("lib", SourceFile::new("lib.nera", vec![0xff])),
    ])
    .unwrap();
    let compiler = CompilerSession::modules(bytes, Default::default(), "app::main").unwrap();
    let result = compiler.analyze("app").unwrap();
    assert_eq!(result.frontend().status(), FrontendStatus::Invalid);
    assert_eq!(
        result.issues().next().unwrap().location.unwrap().source,
        compiler.sources().id("lib").unwrap()
    );
}

#[test]
fn opaque_structs_hide_representation_but_preserve_owner_predicate_interfaces() {
    let lib = r#"module lib;
        pub opaque struct Storage { value: u64, }
        pub predicate Ready(p: ptr<Storage>) { owns(p); initialized(p, 0usize..1usize); }
        pub fn make() -> Own<Storage>
        ensures Ready(result);
        { let p = alloc<Storage>(1); p.value = 42; fold Ready(p); return p; }
        pub fn destroy(p: Own<Storage>) -> u64
        requires Ready(p);
        { unfold Ready(p); let value = p.value; free(p); finish Ready(p); return value; }
    "#;
    let app = r#"module app; use lib::Storage; use lib::Ready; use lib::make; use lib::destroy;
        fn forward(p: Own<Storage>) -> Own<Storage>
        requires Ready(p); ensures Ready(result); { return p; }
        fn main() -> u64 { let p = forward(make()); return destroy(p); }
    "#;
    let compiler = session(&[("app", app), ("lib", lib)], "app::main");
    let analysis = compiler.analyze("app").unwrap();
    let output = analysis.frontend();
    assert!(output.vir().is_some(), "{:?}", output.issues());
    assert!(compiler.verify("app").unwrap().is_checked());
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    for operation in [
        "let value = p.value;",
        "p.value = 9;",
        "let view = &p.value;",
        "let fake = Storage { value: 1, };",
    ] {
        let app = app.replace(
            "return destroy(p);",
            &format!("{operation} return destroy(p);"),
        );
        let compiler = session(&[("app", &app), ("lib", lib)], "app::main");
        let result = compiler.analyze("app").unwrap();
        assert!(result.frontend().vir().is_none(), "{operation}");
        assert!(format!("{:?}", result.frontend().issues()).contains("opaque representation"));
    }
    // Even direct HIR construction must pass the independent privacy check.
    let hir = output.hir().unwrap();
    let tables_of = |hir: &nera::HirProgram| nera::HirProgramTables {
        data_layout: hir.data_layout(),
        entry_module: hir.entry_module_id(),
        entry_function: hir.entry_function_id(),
        type_capabilities: hir.type_capability_table().to_vec(),
        modules: hir.modules().to_vec(),
        functions: hir.functions().to_vec(),
        types: hir.types().to_vec(),
        layouts: hir.layouts().to_vec(),
        fields: hir.fields().to_vec(),
        variants: hir.variants().to_vec(),
        generic_parameters: hir.generic_parameters().to_vec(),
        contracts: hir.contracts().to_vec(),
        predicates: hir.predicates().to_vec(),
        regions: hir.regions().to_vec(),
        region_constraints: hir.region_constraints().to_vec(),
        specs: hir.specs().clone(),
    };
    let mut tables = tables_of(hir);
    let client = tables
        .functions
        .iter()
        .find(|f| f.name == "main")
        .unwrap()
        .module;
    tables
        .types
        .iter_mut()
        .find(|t| t.opaque.is_some())
        .unwrap()
        .opaque = Some(client);
    assert!(nera::HirProgram::from_tables(tables).is_err());

    // Reclassify a valid public representation while retaining its real owner:
    // independent body validation must reject the now-private client access.
    let exposed_lib = lib.replace("opaque struct", "struct");
    let exposed_app = app.replace(
        "return destroy(p);",
        "let value = p.value; return destroy(p);",
    );
    let compiler = session(&[("app", &exposed_app), ("lib", &exposed_lib)], "app::main");
    let analysis = compiler.analyze("app").unwrap();
    let mut tables = tables_of(analysis.frontend().hir().unwrap());
    let owner = tables
        .functions
        .iter()
        .find(|f| f.name == "make")
        .unwrap()
        .module;
    tables
        .types
        .iter_mut()
        .find(|t| t.name.as_deref() == Some("Storage"))
        .unwrap()
        .opaque = Some(owner);
    let error = nera::HirProgram::from_tables(tables).unwrap_err();
    assert!(
        error.to_string().contains("opaque representation"),
        "{error}"
    );
}

#[test]
fn opaque_public_struct_can_hide_private_nested_types() {
    let lib = r#"module lib;
        struct Hidden { value: u64, }
        pub opaque struct Handle { inner: Hidden, }
        pub fn make() -> Handle { return Handle { inner: Hidden { value: 7, }, }; }
        pub fn read(h: Handle) -> u64 { return h.inner.value; }
    "#;
    let app = "module app; use lib::make; use lib::read; fn main() -> u64 { return read(make()); }";
    let compiler = session(&[("app", app), ("lib", lib)], "app::main");
    assert!(compiler.verify("app").unwrap().is_checked());
    let result = compiler.analyze("app").unwrap();
    assert_eq!(
        interpret(
            result
                .frontend()
                .vir()
                .unwrap()
                .resolve()
                .unwrap()
                .runtime()
        )
        .unwrap()
        .values(),
        [VirRuntimeValue::U64(7)]
    );
}

#[test]
fn opaque_arena_api_preserves_private_cursor_and_real_cleanup() {
    let source = include_str!("../spec/cases/verify/predicate-opaque-arena.nera");
    let main_start = source.find("fn main()").unwrap();
    let make_start = source.find("fn make()").unwrap();
    let library = format!(
        "module lib;\n{}{}",
        &source[..main_start],
        &source[make_start..]
    )
    .replace("opaque struct", "pub opaque struct")
    .replace("predicate Ready", "pub predicate Ready")
    .replace("fn ", "pub fn ");
    let app = "module app; use lib::Arena; use lib::Ready; use lib::make; use lib::fill; use lib::reset; use lib::destroy; fn main() -> u64 { return destroy(reset(fill(make()))); }";
    let compiler = session(&[("app", app), ("lib", &library)], "app::main");
    assert!(compiler.verify("app").unwrap().is_checked());
    let output = compiler.analyze("app").unwrap();
    assert_eq!(
        interpret(
            output
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
    for extra in [
        "fn peek(p: &Arena) -> usize requires p.cursor <= 8usize; { return 0usize; }",
        "predicate Spy(p: ptr<Arena>) { owns(p); p.cursor <= 8usize; }",
    ] {
        let client = format!("{app}\n{extra}");
        let compiler = session(&[("app", &client), ("lib", &library)], "app::main");
        let output = compiler.analyze("app").unwrap();
        assert!(output.frontend().vir().is_none());
        assert!(format!("{:?}", output.frontend().issues()).contains("opaque representation"));
    }
}

#[test]
fn opaque_arena_keeps_ownership_while_another_module_returns_its_view() {
    let source = include_str!("../spec/cases/verify/predicate-borrow-calls.nera");
    let main_start = source.find("fn main()").unwrap();
    let make_start = source.find("fn make()").unwrap();
    let view_start = source.find("fn prepare(").unwrap();
    let lib = format!(
        "module lib; use views::prepare;\n{}{}",
        &source[..main_start],
        &source[make_start..view_start]
    )
    .replace("opaque struct", "pub opaque struct")
    .replace("predicate Ready", "pub predicate Ready")
    .replace("fn ", "pub fn ");
    let views = format!("module views; pub {}", &source[view_start..]);
    let app = "module app; use lib::make; use lib::fill; use lib::reset; use lib::destroy; fn main() -> u64 { return destroy(reset(fill(make()))); }";
    let compiler = session(
        &[("app", app), ("lib", &lib), ("views", &views)],
        "app::main",
    );
    assert!(compiler.verify("app").unwrap().is_checked());
    let analysis = compiler.analyze("app").unwrap();
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
    for bad in [
        views.replace("view[0] = 12;", "view[2] = 12;"),
        views.replace("return view;", "return &mut view[1usize..];"),
    ] {
        let compiler = session(&[("app", app), ("lib", &lib), ("views", &bad)], "app::main");
        assert!(!compiler.verify("app").unwrap().is_checked());
    }
}

#[test]
fn reference_field_sources_survive_cross_module_stored_and_ssa_forwarding() {
    let types = "module types; pub struct Views { left:&mut u64, right:&mut u64, }";
    let storage = "module storage; use types::Views; pub fn keep(v:Views)->Views { return v; }";
    let library = "module library; use types::Views; use storage::keep;
        pub fn take(v:Views)->&mut u64 { let stored=keep(v); return stored.right; }";
    let app = "module app; use types::Views; use library::take;
        fn main()->u64 { let mut a=1; let mut b=42;
            let outcome=take(Views { left:&mut a, right:&mut b }); return *outcome; }";
    let compiler = session(
        &[
            ("app", app),
            ("library", library),
            ("storage", storage),
            ("types", types),
        ],
        "app::main",
    );
    let analysis = compiler.analyze("app").unwrap();
    let output = analysis.frontend();
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let report = compiler.verify("app").unwrap();
    assert!(
        report.is_checked(),
        "{}",
        render_text(&report, TextReportMode::Explain)
    );
    let program = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(program.runtime()).unwrap().values(),
        &[VirRuntimeValue::U64(42)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(program.runtime())
        .unwrap();
}
