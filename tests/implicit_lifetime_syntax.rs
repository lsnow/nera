use nera::verification::{TextReportMode, render_text, verify_source};
use nera::{FrontendStatus, SourceFile, VirRuntimeValue, analyze, interpret};

fn checked(text: &str) {
    assert!(
        !text.contains("'") && !text.contains("where"),
        "ordinary borrow source must not use explicit lifetime syntax"
    );
    let source = SourceFile::from_text("implicit-lifetime.nera", text);
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
        &[VirRuntimeValue::U64(42)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.runtime())
        .unwrap();
}

#[test]
fn ordinary_unique_conditional_projection_and_generic_sources_need_no_lifetime_syntax() {
    for program in [
        "fn main()->u64{let x=42;let r=first(&x,7);return *r;} fn first(x:&u64,y:u64)->&u64{return x;}",
        "fn main()->u64{let x=42;let y=7;let r=first(&x,&y);return *r;} fn first(x:&u64,y:&u64)->&u64{return x;}",
        "fn main()->u64{let x=42;let y=7;let r=choose(true,&x,&y);return *r;} fn choose(flag:bool,x:&u64,y:&u64)->&u64{if flag{return x;}else{return y;}}",
        "struct Pair{a:u64,b:u64,} fn main()->u64{let p=Pair{a:42,b:7};let r=field(&p);return *r;} fn field(p:&Pair)->&u64{return &p.a;}",
        "fn main()->u64{let x=42;let r=id<u64>(&x);return *r;} fn id<T>(x:&T)->&T{return x;}",
        "fn main()->u64{let mut x=1;let r=id(&mut x);*r=42;return x;} fn id(x:&mut u64)->&mut u64{return x;}",
    ] {
        checked(program);
    }
}

#[test]
fn removed_lifetime_spellings_have_specific_migration_diagnostics() {
    for (source, message) in [
        (
            "fn main(){return;} fn id<'a>(x:&u64)->&u64{return x;}",
            "explicit lifetime binders were removed",
        ),
        (
            "fn main(){return;} fn id(x:&'a u64)->&u64{return x;}",
            "explicit lifetime annotations were removed",
        ),
        (
            "fn main(){let x=42;let r=&'a x;return;}",
            "explicit lifetime annotations were removed",
        ),
        (
            "fn main(){return;} fn read(x:&u64,y:&u64) where 'a:'b; {return;}",
            "explicit lifetime where clauses were removed",
        ),
    ] {
        let source = SourceFile::from_text("legacy-lifetime.nera", source);
        let first = analyze(&source);
        let second = analyze(&source);
        assert_eq!(first, second);
        assert_eq!(first.status(), FrontendStatus::Unsupported);
        assert!(
            first.issues()[0].diagnostic().message().contains(message),
            "{:?}",
            first.issues()
        );
        assert!(first.hir().is_none());
        assert!(first.vir().is_none());
        assert!(!verify_source(&source, Default::default()).is_checked());
    }
}

#[test]
fn inferred_interfaces_keep_escape_and_permission_failures() {
    for source in [
        "fn main(){return;} fn escape(x:&u64)->&u64{let y=42;return &y;}",
        "fn main()->u64{let p=alloc<u64>(1);*p=42;let r=id(&*p);free(p);return *r;} fn id(x:&u64)->&u64{return x;}",
    ] {
        let source = SourceFile::from_text("unsafe-inferred-interface.nera", source);
        assert!(!verify_source(&source, Default::default()).is_checked());
    }
}

#[test]
fn apostrophe_tokens_remain_lossless_for_migration_diagnostics() {
    let source = SourceFile::from_text(
        "lossless-lifetime.nera",
        "fn main(){return;} fn id<'source>(x:&u64)->&u64{return x;}",
    );
    let output = analyze(&source);
    let token = output
        .lexed()
        .tokens()
        .iter()
        .find(|token| token.kind() == nera::TokenKind::Lifetime)
        .unwrap();
    assert_eq!(token.raw(&source), b"'source");
    assert_eq!(output.status(), FrontendStatus::Unsupported);
}
