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
fn boolean_return_snapshots_preserve_history_without_aliasing_current_cells() {
    let source = "struct Pair {first:bool,second:bool,}
        fn main()->u64 {let mut p=Pair{first:true,second:false}; let saved=save(&mut p); assert saved; return 42;}
        fn save(p:&mut Pair)->bool
        ensures result==old(p.first);
        ensures result!=p.first;
        {let saved=p.first; if saved {p.first=false;} else {p.first=true;} return saved;}";
    assert!(checked(source));
    assert!(checked(&source.replace(
        "ensures result==old(p.first);",
        "ensures (!(!result))==old(p.first);"
    )));
    for invalid in [
        source.replace("return saved;", "return p.first;"),
        source.replace("return saved;", "return p.second;"),
        source.replace("result==old(p.first)", "result==p.first"),
        source.replace("result==old(p.first)", "result==old(p.second)"),
    ] {
        assert!(!checked(&invalid), "{invalid}");
    }
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

#[test]
fn symbolic_heap_increments_require_no_wrap_and_preserve_cell_identity() {
    let source = "fn main()->u64 {let mut n=3; bump(&mut n); return 0;} fn bump(p:&mut u64) requires *p<18446744073709551615; ensures *p==old(*p)+1; {*p=*p+1; return;}";
    assert!(checked(source));
    assert!(!checked(
        &source.replace("requires *p<18446744073709551615;", "")
    ));
    assert!(!checked(&source.replace("*p=*p+1;", "*p=4;")));
    let fields = "struct Pair {x:u64,y:u64,} fn main()->u64 {let mut p=Pair{x:3,y:3}; bump(&mut p); return 0;} fn bump(p:&mut Pair) requires p.x<8; requires p.y<8; ensures p.x==old(p.y)+1; {p.x=p.y+1; return;}";
    assert!(checked(fields));
    assert!(!checked(&fields.replace("p.x=p.y+1;", "p.x=p.x+1;")));
}

#[test]
fn symbolic_heap_origins_check_every_branch_and_do_not_use_current_value_as_old() {
    let source = "fn main()->u64 {let mut n=3; bump(&mut n,true); return 0;} fn bump(p:&mut u64,flag:bool) requires *p<8; ensures *p==old(*p)+1; {if flag {*p=*p+1;} else {let n=*p; *p=n+1;} return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("*p=n+1;", "*p=n+2;")));
    assert!(!checked(&source.replace("*p=n+1;", "*p=4;")));
    assert!(!checked(&source.replace("old(*p)+1", "*p+1")));
}

#[test]
fn returned_scalar_preserves_entry_cell_history_across_calls() {
    let source = "fn main()->u64 {let mut n=3; return forward(&mut n);} fn take(p:&mut u64)->u64 requires *p<8; ensures *p==old(*p)+1; ensures result==old(*p); {let n=*p; *p=n+1; return n;} fn forward(p:&mut u64)->u64 requires *p<8; ensures *p==old(*p)+1; ensures result==old(*p); {return take(p);}";
    assert!(checked(source));
    let forwarded = source.replace("return take(p);", "let n=take(p); return identity(n);")
        + " fn identity(n:u64)->u64 {return n;}";
    assert!(checked(&forwarded));
    let advanced = source
        .replace("return take(p);", "let n=take(p); return next(n);")
        .replace(
            "ensures result==old(*p); {let n=take(p)",
            "ensures result==old(*p)+1; {let n=take(p)",
        )
        + " fn next(n:u64)->u64 requires n<8; {return n+1;}";
    assert!(checked(&advanced));
    assert!(!checked(&forwarded.replace("{return n;}", "{return 3;}")));
    assert!(!checked(&source.replace("return n;", "return n+1;")));
    assert!(!checked(&source.replace("return n;", "return 3;")));
    assert!(!checked(&source.replace("result==old(*p)", "result==*p")));
    let twice = source.replace("return take(p);", "let n=take(p); let m=take(p); return m;")
        .replace("fn forward(p:&mut u64)->u64 requires *p<8; ensures *p==old(*p)+1; ensures result==old(*p);", "fn forward(p:&mut u64)->u64 requires *p<7; ensures *p==old(*p)+2; ensures result==old(*p)+1;");
    assert!(checked(&twice));
    assert!(!checked(&twice.replace("return m;", "return n;")));
}

#[test]
fn returned_scalar_history_distinguishes_fields_branches_and_wrap() {
    let source = "struct Pair {x:u64,y:u64,} fn main()->u64 {let mut p=Pair{x:3,y:3}; return choose(&mut p,true);} fn choose(p:&mut Pair,b:bool)->u64 requires p.x<8; requires p.y<8; ensures result==old(p.y)+1; {if b {return p.y+1;} else {let n=p.y; return n+1;}}";
    assert!(checked(source));
    assert!(!checked(&source.replace("let n=p.y", "let n=p.x")));
    assert!(!checked(&source.replace("return n+1", "return n+2")));
    let wrap = "fn main()->u64 {let mut n=3; return read(&mut n);} fn read(p:&mut u64)->u64 requires *p<18446744073709551615; ensures result==old(*p)+1; {return *p+1;}";
    assert!(checked(wrap));
    assert!(!checked(
        &wrap.replace("requires *p<18446744073709551615;", "")
    ));
}

#[test]
fn nested_inline_fields_preserve_typed_history_and_distinct_offsets() {
    let source = "struct Inner {pad:bool,cursor:usize,} struct Outer {tag:u64,state:Inner,tail:usize,} fn main()->u64 {let mut p=Outer{tag:9,state:Inner{pad:true,cursor:3usize},tail:3usize}; let n=bump(&mut p); return 0;} fn bump(p:&mut Outer)->usize requires p.state.cursor<8usize; requires p.tail<8usize; ensures p.state.cursor==old(p.state.cursor)+1usize; ensures result==old(p.state.cursor); {let n=p.state.cursor; p.state.cursor=n+1usize; return n;}";
    assert!(checked(source));
    assert!(!checked(
        &source.replace("let n=p.state.cursor;", "let n=p.tail;")
    ));
    assert!(!checked(
        &source.replace("p.state.cursor=n+1usize;", "p.tail=n+1usize;")
    ));
    assert!(!checked(&source.replace(
        "old(p.state.cursor)+1usize",
        "old(p.state.cursor)+2usize"
    )));
    let boolean = "struct Inner {flag:bool,} struct Outer {state:Inner,} fn main()->u64 {let mut p=Outer{state:Inner{flag:true}}; clear(&mut p); return 0;} fn clear(p:&mut Outer) requires p.state.flag; ensures !p.state.flag; ensures old(p.state.flag); {p.state.flag=false; return;}";
    assert!(checked(boolean));
    assert!(!checked(&boolean.replace("p.state.flag=false;", "")));
}

#[test]
fn nested_memory_paths_are_bounded_and_independently_validated() {
    assert!(SpecMemoryFieldPath::<VirFieldId>::new(&[]).is_none());
    assert!(SpecMemoryFieldPath::new(&[VirFieldId::new(0)]).is_none());
    assert!(SpecMemoryFieldPath::new(&[VirFieldId::new(0); 17]).is_none());
    let source = "struct Inner {cursor:usize,} struct Outer {state:Inner,} fn main()->u64 {return 0;} fn bump(p:&mut Outer) requires p.state.cursor<8usize; ensures p.state.cursor==old(p.state.cursor)+1usize; {p.state.cursor=p.state.cursor+1usize; return;}";
    let output = analyze(&SourceFile::from_text("nested.nera", source));
    let raw = output.vir().unwrap().as_unit().clone();
    let (id, term) = raw
        .specs
        .terms()
        .iter()
        .enumerate()
        .find(|(_, t)| {
            matches!(
                t.kind,
                VirSpecTermKind::Snapshot(VirSpecSnapshot::Memory {
                    projection: SpecMemoryProjection::Fields(_),
                    ..
                })
            )
        })
        .unwrap();
    let VirSpecTermKind::Snapshot(VirSpecSnapshot::Memory {
        function,
        parameter,
        old,
        projection: SpecMemoryProjection::Fields(path),
    }) = term.kind
    else {
        unreachable!()
    };
    let fields = path.fields();
    for forged in [
        vec![fields[1], fields[0]],
        vec![fields[0], VirFieldId::new(999)],
        vec![fields[0], fields[0]],
        vec![fields[0], fields[1], fields[1]],
    ] {
        let mut unit = raw.clone();
        unit.specs.terms_mut()[id].kind = VirSpecTermKind::Snapshot(VirSpecSnapshot::Memory {
            function,
            parameter,
            old,
            projection: SpecMemoryProjection::Fields(SpecMemoryFieldPath::new(&forged).unwrap()),
        });
        assert!(unit.into_validated().is_err(), "{forged:?}");
    }
    for depth in [16, 17] {
        let mut source = String::from("fn main()->u64 {return 0;} struct T0 {v:usize,}");
        for n in 1..depth {
            source.push_str(&format!("struct T{n} {{f:T{},}}", n - 1));
        }
        let path = format!("p.{}v", "f.".repeat(depth - 1));
        source.push_str(&format!("fn bump(p:&mut T{}) requires {path}<8usize; ensures {path}==old({path})+1usize; {{{path}={path}+1usize; return;}}",depth-1));
        if depth == 16 {
            assert!(checked(&source));
        } else {
            assert!(
                analyze(&SourceFile::from_text("deep.nera", source))
                    .vir()
                    .is_none()
            );
        }
    }
}

#[test]
fn nested_contract_observations_respect_inner_opacity_and_do_not_chase_owners() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let library = "module lib; pub struct Inner {cursor:usize,} pub struct Outer {state:Inner,}";
    let app = "module app; use lib::Outer; fn main()->u64 {return 0;} fn inspect(p:&Outer) requires p.state.cursor<8usize; {return;}";
    for visible in [true, false] {
        let library = if visible {
            library.to_owned()
        } else {
            library.replace("pub struct Inner", "pub opaque struct Inner")
        };
        let inputs = [("app", app), ("lib", library.as_str())]
            .into_iter()
            .map(|(name, text)| {
                SourceInput::new(name, SourceFile::from_text(format!("{name}.nera"), text))
            })
            .collect();
        let compiler = CompilerSession::modules(
            SourceDatabase::new(inputs).unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap();
        assert_eq!(compiler.verify("app").unwrap().is_checked(), visible);
    }
    for pointer in ["Own<Inner>", "ptr<Inner>"] {
        let source = format!(
            "struct Inner {{cursor:usize,}} struct Outer {{state:{pointer},}} fn main()->u64 {{return 0;}} fn inspect(p:&Outer) requires p.state.cursor<8usize; {{return;}}"
        );
        assert!(
            analyze(&SourceFile::from_text("chase.nera", source))
                .vir()
                .is_none()
        );
    }
}

#[test]
fn two_entry_cell_sums_survive_memory_and_scalar_return_calls() {
    let source = "struct State {cursor:u64,step:u64,} fn main()->u64 {let mut p=State{cursor:3,step:2}; return forward(&mut p);} fn advance(p:&mut State)->u64 requires p.cursor<8; requires p.step<8; ensures p.cursor==old(p.cursor)+old(p.step); ensures result==old(p.cursor)+old(p.step); {let n=p.cursor+p.step; p.cursor=n; return n;} fn forward(p:&mut State)->u64 requires p.cursor<8; requires p.step<8; ensures p.cursor==old(p.cursor)+old(p.step); ensures result==old(p.cursor)+old(p.step); {return advance(p);}";
    assert!(checked(source));
    let exact = source.replace(
        "return forward(&mut p);",
        "let n=forward(&mut p); expect_five(n); return n;",
    ) + " fn expect_five(n:u64) requires n==5; {return;}";
    assert!(checked(&exact));
    assert!(!checked(&exact.replace("requires n==5", "requires n==6")));
    assert!(!checked(&source.replace(
        "{return advance(p);}",
        "{p.step=2; return advance(p);}"
    )));

    assert!(!checked(
        &source.replace("let n=p.cursor+p.step", "let n=p.cursor+p.cursor")
    ));
    assert!(!checked(
        &source.replace("let n=p.cursor+p.step", "let n=5")
    ));
    assert!(!checked(&source.replace("requires p.cursor<8;", "")));
    let extra = source
        .replace("let n=p.cursor+p.step", "let n=p.cursor+p.step+1")
        .replace("old(p.cursor)+old(p.step);", "old(p.cursor)+old(p.step)+1;");
    assert!(checked(&extra));
    let repeated = source
        .replace("p.cursor+p.step", "p.cursor+p.cursor")
        .replace("old(p.cursor)+old(p.step)", "old(p.cursor)+old(p.cursor)");
    assert!(checked(&repeated));
}

#[test]
fn historical_sums_keep_distinct_inputs_and_commutative_branch_joins() {
    let source = "fn main()->u64 {let mut a=3; let mut b=2; return forward(&mut a,&mut b,true);} fn sum(a:&mut u64,b:&mut u64,flag:bool)->u64 requires *a<8; requires *b<8; ensures *a==old(*a)+old(*b); ensures result==old(*a)+old(*b); {let mut n=0; if flag {n=*a+*b;} else {n=*b+*a;} *a=n; *b=0; return n;} fn forward(a:&mut u64,b:&mut u64,flag:bool)->u64 requires *a<8; requires *b<8; ensures *a==old(*a)+old(*b); ensures result==old(*a)+old(*b); {return sum(a,b,flag);}";
    assert!(checked(source));
    assert!(!checked(&source.replace("n=*b+*a", "n=*b+*b")));
    assert!(!checked(&source.replace("old(*a)+old(*b)", "old(*a)+*b")));
    assert!(!checked(&source.replace("*a=n;", "*a=5;")));
}

#[test]
fn repeated_heap_steps_compose_across_calls_without_duplicating_sources() {
    let source = "struct State {cursor:u64,step:u64,} fn main()->u64 {let mut p=State{cursor:1,step:2}; let n=twice(&mut p); exact(n); return n;} fn advance(p:&mut State)->u64 requires p.cursor<8; requires p.step<8; ensures p.cursor==old(p.cursor)+old(p.step); ensures result==old(p.cursor)+old(p.step); {p.cursor=p.cursor+p.step; return p.cursor;} fn twice(p:&mut State)->u64 requires p.cursor<4; requires p.step<4; ensures p.cursor==old(p.cursor)+old(p.step)+old(p.step); ensures result==old(p.cursor)+old(p.step)+old(p.step); {let n=advance(&mut *p); return advance(p);} fn exact(n:u64) requires n==5; {return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("requires n==5", "requires n==4")));
    assert!(!checked(&source.replace(
        "old(p.cursor)+old(p.step)+old(p.step)",
        "old(p.cursor)+old(p.step)"
    )));
    assert!(!checked(&source.replace(
        "let n=advance(&mut *p);",
        "let n=advance(&mut *p); p.step=2;"
    )));
}

#[test]
fn weighted_histories_merge_equivalent_branches_and_reject_a_third_source() {
    let source = "struct State {x:u64,y:u64,z:u64,} fn main()->u64 {let mut p=State{x:1,y:2,z:2}; return sum(&mut p,true);} fn sum(p:&mut State,b:bool)->u64 requires p.x<8; requires p.y<8; requires p.z<8; ensures p.x==old(p.x)+old(p.y)+old(p.x); ensures result==old(p.x)+old(p.y)+old(p.x); {let mut n=0; if b {n=(p.x+p.y)+p.x;} else {n=p.x+(p.y+p.x);} p.x=n; return n;}";
    assert!(checked(source));
    assert!(!checked(
        &source.replace("n=p.x+(p.y+p.x)", "n=p.y+(p.y+p.x)")
    ));
    assert!(!checked(&source.replace("requires p.x<8;", "")));
    let third = source
        .replace("(p.x+p.y)+p.x", "(p.x+p.y)+p.z")
        .replace("p.x+(p.y+p.x)", "p.x+(p.y+p.z)")
        .replace("old(p.x)+old(p.y)+old(p.x)", "old(p.x)+old(p.y)+old(p.z)");
    assert!(!checked(&third));
}

#[test]
fn call_substitution_scales_both_history_terms_and_the_constant() {
    let source = "struct State {x:u64,y:u64,} fn main()->u64 {let mut p=State{x:1,y:2}; let n=compose(&mut p); exact(n); return n;} fn double(p:&mut State)->u64 requires p.x<16; ensures p.x==old(p.x)+old(p.x); ensures result==old(p.x)+old(p.x); {p.x=p.x+p.x; return p.x;} fn compose(p:&mut State)->u64 requires p.x<4; requires p.y<4; ensures result==old(p.x)+old(p.y)+old(p.x)+old(p.y)+2; {p.x=p.x+p.y+1; return double(p);} fn exact(n:u64) requires n==8; {return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace(
        "old(p.x)+old(p.y)+old(p.x)+old(p.y)+2",
        "old(p.x)+old(p.y)+old(p.x)+old(p.y)+1"
    )));
    assert!(!checked(&source.replace("requires n==8", "requires n==7")));
}

#[test]
fn parameter_steps_compose_with_memory_histories_across_calls() {
    let source = "struct State {cursor:u64,} fn main()->u64 {let mut p=State{cursor:1}; let n=twice(&mut p,2); exact(n); return n;} fn advance(p:&mut State,n:u64)->u64 requires p.cursor<16; requires n<4; ensures p.cursor==old(p.cursor)+n; ensures result==old(p.cursor)+n; {p.cursor=p.cursor+n; return p.cursor;} fn twice(p:&mut State,n:u64)->u64 requires p.cursor<4; requires n<4; ensures p.cursor==old(p.cursor)+n+n; ensures result==old(p.cursor)+n+n; {let first=advance(&mut *p,n); return advance(p,n);} fn exact(n:u64) requires n==5; {return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("requires n==5", "requires n==6")));
    assert!(!checked(
        &source.replace("p.cursor=p.cursor+n", "p.cursor=p.cursor+1")
    ));
    assert!(!checked(
        &source.replace("old(p.cursor)+n+n", "old(p.cursor)+n")
    ));
    assert!(!checked(&source.replace("requires n<4;", "")));
    let constant = source
        .replace("return advance(p,n)", "return advance(p,1)")
        .replace("old(p.cursor)+n+n", "old(p.cursor)+n+1")
        .replace("requires n==5", "requires n==4");
    assert!(checked(&constant));
}

#[test]
fn parameter_history_tracks_identity_not_equal_intervals() {
    let source = "fn main()->u64 {let mut p=1; return add(&mut p,2,3,true);} fn add(p:&mut u64,n:u64,m:u64,flag:bool)->u64 requires *p<8; requires n<4; requires m<4; ensures *p==old(*p)+n; ensures result==old(*p)+n; {let mut end=0; if flag {end=*p+n;} else {end=n+*p;} *p=end; return end;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("end=n+*p", "end=m+*p")));
    assert!(!checked(&source.replace("old(*p)+n", "old(*p)+m")));
}

#[test]
fn nonzero_slice_starts_cancel_only_matching_historical_sources() {
    let source = include_str!("../spec/cases/verify/contract-borrowed-cursor.nera");
    assert!(checked(source));
    assert!(!checked(&source.replace(
        "ensures len(result)==count",
        "ensures len(result)==count+1usize"
    )));
    assert!(!checked(
        &source.replace("let end=start+count;", "let end=start+1usize;")
    ));
    assert!(!checked(
        &source.replace("p.slots[start..end]", "p.slots[0usize..end]")
    ));
    assert!(!checked(&source.replace("requires count<=4usize;", "")));
}

#[test]
fn returned_child_allows_only_disjoint_contract_observations() {
    let source = "struct Pair {first:u64, second:u64,}
        fn main()->u64 {let mut p=Pair{first:1,second:42}; let q=take(&mut p); return *q;}
        fn take(p:&mut Pair)->&mut u64
        ensures p.first==7;
        {p.first=7; return &mut p.second;}";
    assert!(checked(source));
    // The current observation is read after the returned mutable child was
    // created. Owning that child's parent is not authority to read its bytes.
    assert!(!checked(&source.replace("&mut p.second", "&mut p.first")));
    assert!(!checked(&source.replace("p.first=7", "p.first=8")));
    assert!(!checked(&source.replace(
        "return &mut p.second;",
        "let q=&mut p.second; let n=p.first; return q;"
    )));
}
