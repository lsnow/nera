use nera::*;

fn checked(source: &str) -> bool {
    let output = analyze(&SourceFile::from_text("frame.nera", source));
    let unit = output
        .vir()
        .unwrap_or_else(|| panic!("{:?}", output.issues()));
    let report = verify_program(&unit.resolve().unwrap(), Default::default());
    match report {
        Ok(report) => {
            if !report.is_memory_checked_core0() {
                eprintln!("{:?}", report.diagnostics());
            }
            report.is_memory_checked_core0()
        }
        Err(error) => {
            eprintln!("{error:?}");
            false
        }
    }
}

#[test]
fn reads_and_writes_are_independent_upper_bounds() {
    let source = "fn main()->u64 {let mut n=1; update(&mut n); return n;}
        fn update(p:&mut u64) reads (); writes p[0..1]; {*p=7; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("writes p[0..1]", "writes ()")));
    assert!(!checked(&source.replace("*p=7", "*p=*p+1")));
    assert!(checked(
        &source
            .replace("reads ()", "reads p[0..1]")
            .replace("*p=7", "*p=*p+1")
    ));
    assert!(checked(
        &source.replace("reads ();", "").replace("*p=7", "*p=*p+1")
    ));
    assert!(!checked(
        "fn main()->u64 {let n=1; return read(&n,&n);}
        fn read(p:&u64,q:&u64)->u64 reads p[0..1]; {return *q;}"
    ));
}

#[test]
fn ranges_are_unioned_and_bounds_checked_at_entry() {
    let source = "fn main()->u64 {let mut a=[1,2]; update(&mut a[0..2]); return a[1];}
        fn update(p:&mut [u64]) requires len(p)==2usize;
        writes p[0..1]; writes p[1..2]; reads ();
        {p[0]=7; p[1]=8; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("writes p[1..2];", "")));
    assert!(!checked(&source.replace("p[1..2];", "p[2..3];")));
    assert!(!checked(&source.replace("p[1..2];", "p[2..2];")));
    assert!(checked(
        &source.replace("writes p[1..2];", "writes p[0usize..len(p)];")
    ));
}

#[test]
fn hidden_call_effects_and_failed_callees_cannot_publish() {
    let source = "fn main()->u64 {let mut n=1; wrapper(&mut n); return n;}
        fn wrapper(p:&mut u64) writes p[0..1]; {leaf(p); return;}
        fn leaf(p:&mut u64) {*p=7; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("writes p[0..1]", "writes ()")));
    assert!(!checked(&source.replace(
        "fn leaf(p:&mut u64)",
        "fn leaf(p:&mut u64) writes ();"
    )));
}

#[test]
fn empty_frames_do_not_authorize_access_or_free() {
    assert!(checked(
        "fn main()->u64 reads (); writes (); {let mut n=1; n=2; return n;}"
    ));
    let source = "fn main()->u64 {let p=alloc<u64>(1); *p=1; consume(p); return 0;}
        fn consume(p:Own<u64>) reads (); writes (); {free(p); return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("free(p);", "*p=1; free(p);")));
    let source = "fn main()->u64 {let p=alloc<u64>(1); return read(p);}
        fn read(p:Own<u64>)->u64 reads p[0..1]; {let n=*p; free(p); return n;}";
    assert!(!checked(source));
}

#[test]
fn branches_and_frame_only_recursion_remain_checked() {
    let source = "fn main()->u64 {let mut a=[1,2]; update(&mut a[0..2],true); return a[1];}
        fn update(p:&mut [u64],b:bool) requires len(p)==2usize; writes p[0..1];
        {if b {p[0]=7;} else {p[1]=8;} return;}";
    assert!(!checked(source));
    assert!(checked(&source.replace("p[1]=8", "p[0]=8")));
    // Partial correctness, not a termination or native stack-space guarantee.
    assert!(checked(
        "fn main()->u64 {return rec();} fn rec()->u64 writes (); {return rec();}"
    ));
}

#[test]
fn frame_budget_and_schema_mutations_fail_closed() {
    let source = "fn main()->u64 {let mut n=1; update(&mut n); return n;}
        fn update(p:&mut u64) writes p[0..1]; {*p=7; return;}";
    let output = analyze(&SourceFile::from_text("budget.nera", source));
    let validated = output.vir().unwrap();
    let config = CfgAnalysisConfig {
        max_region_pairs_per_instruction: 0,
        ..Default::default()
    };
    assert!(
        !verify_program(&validated.resolve().unwrap(), config)
            .is_ok_and(|r| r.is_memory_checked_core0())
    );
    let mut unit = validated.as_unit().clone();
    let index = unit
        .specs
        .assertions()
        .iter()
        .position(|a| matches!(a.kind, SpecAssertionKind::Footprint { .. }))
        .unwrap();
    let clause = unit.specs.assertions()[index].clause;
    // A footprint is not an ensures guarantee or a local resource assertion.
    if let VirSpecClauseOwner::Contract { position, .. } =
        &mut unit.specs.clauses_mut()[clause.get() as usize].owner
    {
        *position = VirContractPosition::Ensures;
    }
    assert!(unit.into_validated().is_err());
    let mut unit = validated.as_unit().clone();
    let SpecAssertionKind::Footprint {
        range: Some(range), ..
    } = &mut unit.specs.assertions_mut()[index].kind
    else {
        unreachable!()
    };
    range.pointer = VirSpecSnapshot::Result {
        function: VirFunctionId::new(1),
        slot: 0,
    };
    assert!(unit.into_validated().is_err());
}

#[test]
fn untouched_tail_remains_usable_after_a_partial_write_call() {
    let source = "fn main()->u64 {let mut a=[1,2]; let p=&mut a[0..1]; let tail=&mut a[1..2];
        update(p); tail[0]=9; return tail[0];}
        fn update(p:&mut [u64]) requires len(p)==1usize; writes p[0..1]; reads (); {p[0]=7; return;}";
    assert!(checked(source));
}

#[test]
fn private_temporary_storage_is_not_a_public_write() {
    assert!(checked(
        "fn main()->u64 reads (); writes (); {let p=alloc<u64>(1); *p=7; let n=*p; free(p); return n;}"
    ));
    assert!(!checked(
        "fn main()->u64 {let p=make(); free(p); return 0;} fn make()->Own<u64> writes (); {let p=alloc<u64>(1); *p=7; return p;}"
    ));
}
