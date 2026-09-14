use nera::*;

fn checked(source: &str) -> bool {
    let out = analyze(&SourceFile::from_text("memory-contracts.nera", source));
    let unit = out.vir().unwrap_or_else(|| panic!("{:?}", out.issues()));
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
fn scalar_heap_old_and_current_are_distinct() {
    let source = "fn main()->u64 {let mut n=41; update(&mut n); return 0;}
        fn update(p:&mut u64) requires *p==41; ensures *p==old(*p)+1; {*p=42; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("n=41", "n=40")));
    assert!(!checked(&source.replace("*p=42", "*p=43")));
    assert!(!checked(&source.replace("old(*p)+1", "old(*p)")));
}

#[test]
fn fixed_fields_and_entry_bound_array_indices() {
    let source = "struct Pair {x:u64,y:u64,} fn main()->u64 {let mut p=Pair{x:41,y:7}; update(&mut p); return 0;}
        fn update(p:&mut Pair) requires p.x==41; ensures p.x==old(p.x)+1; {p.x=42; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("p.x=42", "p.y=42")));
    let source = "fn main()->u64 {let mut a=[41,7]; update(&mut a,0usize); return 0;}
        fn update(p:&mut [u64;2],i:usize) requires i==0usize; requires p[i]==41; ensures p[i]==old(p[i])+1; {p[i]=42; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("p[i]=42", "p[1]=42")));
}

#[test]
fn returned_owner_can_be_observed_before_authority_transfer() {
    let source = "fn main()->u64 {let p=make(); free(p); return 0;}
        fn make()->Own<u64> ensures *result==42; {let p=alloc<u64>(1); *p=42; return p;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("*p=42", "*p=41")));
}

#[test]
fn boolean_usize_and_returned_fixed_field_observations() {
    let source = "fn main()->u64 {let mut b=true; flip(&mut b); let mut n=41usize; update(&mut n); return 0;}
        fn flip(p:&mut bool) requires *p; ensures !*p; {*p=false; return;}
        fn update(p:&mut usize) requires *p==41usize; ensures *p==old(*p)+1usize; {*p=42usize; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("*p=false", "*p=true")));
    let source = "struct Pair {x:u64,y:u64,} fn main()->u64 {let p=Pair{x:41,y:7}; let q=identity(&p); return q.x;}
        fn identity(p:&Pair)->&Pair requires p.x==41; ensures result.x==41; {return p;}";
    assert!(checked(source));
}

#[test]
fn reborrow_and_unknown_call_effect_do_not_preserve_stale_values() {
    let source = "fn main()->u64 {let mut n=41; update(&mut n); return 0;}
        fn update(p:&mut u64) requires *p==41; ensures *p==old(*p)+1; {let q=&mut *p; *q=42; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("*q=42", "*q=7")));
    let source = "fn main()->u64 {let mut n=41; update(&mut n); return 0;}
        fn update(p:&mut u64) requires *p==41; ensures *p==41; {set(p); return;}
        fn set(p:&mut u64) {*p=7; return;}";
    assert!(!checked(source));
}

#[test]
fn old_is_history_not_current_authority_and_missing_contents_are_unknown() {
    let source = "fn main()->u64 {let p=alloc<u64>(1); *p=41; consume(p); return 0;}
        fn consume(p:Own<u64>) requires *p==41; ensures old(*p)==41; {free(p); return;}";
    assert!(checked(source));
    assert!(!checked(
        &source.replace("ensures old(*p)==41", "ensures *p==41")
    ));
    assert!(!checked(
        &source.replace("ensures old(*p)==41", "ensures *p==*p")
    ));
    assert!(!checked(
        &source.replace("ensures old(*p)==41", "ensures true || *p==41")
    ));
    assert!(!checked(&source.replace("*p=41; consume", "consume")));
    let source = "fn main()->u64 {let mut p=41; read(&p); return 0;}
        fn read(p:&u64) ensures *p==41; {return;}";
    assert!(!checked(source));
}

#[test]
fn schema_rejects_forged_memory_roots_indices_epochs_and_types() {
    let source = "fn main()->u64 {let mut n=41; update(&mut n); return 0;}
        fn update(p:&mut u64) requires *p==41; ensures *p==old(*p)+1; {*p=42; return;}";
    let out = analyze(&SourceFile::from_text("schema.nera", source));
    let raw = out.vir().unwrap().as_unit();
    let id = raw
        .specs
        .terms()
        .iter()
        .position(|t| {
            matches!(
                t.kind,
                VirSpecTermKind::Snapshot(VirSpecSnapshot::Memory { .. })
            )
        })
        .unwrap();
    for forged in [
        VirSpecSnapshot::Memory {
            function: VirFunctionId::new(0),
            parameter: Some(0),
            old: false,
            projection: SpecMemoryProjection::Cell,
        },
        VirSpecSnapshot::Memory {
            function: VirFunctionId::new(1),
            parameter: Some(99),
            old: false,
            projection: SpecMemoryProjection::Cell,
        },
        VirSpecSnapshot::Memory {
            function: VirFunctionId::new(1),
            parameter: Some(0),
            old: true,
            projection: SpecMemoryProjection::Cell,
        },
        VirSpecSnapshot::Memory {
            function: VirFunctionId::new(1),
            parameter: None,
            old: false,
            projection: SpecMemoryProjection::Cell,
        },
        VirSpecSnapshot::Memory {
            function: VirFunctionId::new(1),
            parameter: Some(0),
            old: false,
            projection: SpecMemoryProjection::Field(VirFieldId::new(99)),
        },
        VirSpecSnapshot::Memory {
            function: VirFunctionId::new(1),
            parameter: Some(0),
            old: false,
            projection: SpecMemoryProjection::Index(SpecMemoryIndex::Parameter(99)),
        },
    ] {
        let mut unit = raw.clone();
        unit.specs.terms_mut()[id].kind = VirSpecTermKind::Snapshot(forged);
        assert!(unit.into_validated().is_err(), "{forged:?}");
    }
    let mut unit = raw.clone();
    unit.specs.terms_mut()[id].ty = VirSpecType::Bool;
    assert!(unit.into_validated().is_err());
}

#[test]
fn uncertain_indices_slice_extents_and_branch_contents_remain_gated() {
    let source = "fn main()->u64 {let mut a=[41,7]; update(&mut a,0usize); return 0;}
        fn update(p:&mut [u64;2],i:usize) requires i<=1usize; requires p[i]==41; {*p=42; return;}";
    // The body uses a proper element write; only the entry index is uncertain.
    assert!(!checked(&source.replace("*p=42", "p[i]=42")));
    let source = "fn main()->u64 {let mut a=[41,7]; update(&mut a[0..2]); return 0;}
        fn update(p:&mut [u64]) requires p[0]==41; {p[0]=42; return;}";
    assert!(!checked(source));
    let source = "fn main()->u64 {let mut n=41; update(&mut n,true); return 0;}
        fn update(p:&mut u64,b:bool) requires *p==41; ensures *p==42; {if b {*p=42;} else {*p=7;} return;}";
    assert!(!checked(source));
    assert!(checked(&source.replace("else {*p=7;}", "else {*p=42;}")));
}
