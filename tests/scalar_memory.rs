use nera::*;

fn report(source: &str) -> ProgramVerification {
    let out = analyze(&SourceFile::from_text("scalar-memory.nera", source));
    let unit = out.vir().unwrap_or_else(|| panic!("{:?}", out.issues()));
    verify_program(&unit.resolve().unwrap(), Default::default()).unwrap()
}

#[test]
fn real_stores_and_alias_writes_determine_loaded_values() {
    let source = "fn main()->u64 {let p=alloc<u64>(1); *p=42; let first=*p; assert first==42;
        let q=&mut *p; *q=7; let second=*p; assert second==7; free(p); return second;}";
    let good = report(source);
    assert!(good.is_memory_checked_core0(), "{:?}", good.diagnostics());
    assert!(!report(&source.replace("second==7", "second==42")).is_memory_checked_core0());
    let source = "fn main()->u64 {let mut values=[1,2]; values[1]=42; let a=values[0]; let b=values[1]; assert a==1; assert b==42; return b;}";
    let good = report(source);
    assert!(good.is_memory_checked_core0(), "{:?}", good.diagnostics());
}

#[test]
fn aggregate_replacement_updates_contents_even_when_initialization_is_preserved() {
    let source = "fn main()->u64 {let mut values=[1,2]; values=[7,8]; let a=values[0]; let b=values[1]; assert a==7; assert b==8; return b;}";
    let good = report(source);
    assert!(good.is_memory_checked_core0(), "{:?}", good.diagnostics());
    assert!(!report(&source.replace("a==7", "a==1")).is_memory_checked_core0());
}

#[test]
fn branch_join_keeps_common_values_but_does_not_select_one_arm() {
    let source = "fn main()->u64 {return f(true);} fn f(b:bool)->u64 {let p=alloc<u64>(1); *p=0;
        if b {*p=42;} else {*p=42;} let result=*p; assert result==42; free(p); return result;}";
    // `result` is a Spec keyword, not a runtime binding name.
    let source = source.replace("result", "value");
    assert!(report(&source).is_memory_checked_core0());
    assert!(!report(&source.replace("else {*p=42;}", "else {*p=7;}")).is_memory_checked_core0());
}

#[test]
fn calls_and_invalid_reads_cannot_reuse_stale_scalar_contents() {
    let source = "fn main()->u64 {let mut value=42; update(&mut value); let got=value; assert got==42; return got;}
        fn update(p:&mut u64) {*p=7; return;}";
    assert!(!report(source).is_memory_checked_core0());
    for source in [
        "fn main()->u64 {let p=alloc<u64>(1); let x=*p; assert x==0; free(p); return x;}",
        "fn main()->u64 {let p=alloc<u64>(1); *p=42; free(p); let x=*p; assert x==42; return x;}",
    ] {
        assert!(!report(source).is_memory_checked_core0());
    }
}

#[test]
fn dynamic_write_invalidates_every_possible_cell_not_only_the_lower_bound() {
    let source = "fn main()->u64 {return f(0usize);} fn f(i:usize)->u64 requires i<=1usize; {
        let mut a=[1,2]; a[i]=7; let x=a[0]; assert x==1; return x;}";
    assert!(!report(source).is_memory_checked_core0());
    let source = source
        .replace("f(0usize)", "f(1usize)")
        .replace("i<=1usize", "i==1usize");
    let result = report(&source);
    assert!(
        result.is_memory_checked_core0(),
        "{:?}",
        result.diagnostics()
    );
}
