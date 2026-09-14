use nera::*;

fn checked(source: &str) -> bool {
    let out = analyze(&SourceFile::from_text("resource-contracts.nera", source));
    let unit = out.vir().unwrap_or_else(|| panic!("{:?}", out.issues()));
    match verify_program(&unit.resolve().unwrap(), Default::default()) {
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
fn distinct_symbolic_borrow_inputs_do_not_prove_physical_disjointness() {
    let source = "fn main()->u64 {let n=1; inspect(&n,&n); return n;}
        fn inspect(p:&u64,q:&u64) ensures disjoint(p[0..1],q[0..1]); {return;}";
    assert!(!checked(source));
    // A wrapper must not discharge another callee's precondition merely from
    // its own independently named entry views either.
    let source = "fn main()->u64 {let n=1; wrapper(&n,&n); return n;}
        fn wrapper(p:&u64,q:&u64) {inspect(p,q); return;}
        fn inspect(p:&u64,q:&u64) requires disjoint(p[0..1],q[0..1]); {return;}";
    assert!(!checked(source));
}

#[test]
fn scalar_resource_contract_refines_existing_borrow_authority() {
    let source = "fn main()->u64 {let mut n=41; update(&mut n); return n;}
        fn update(p:&mut u64) requires writable(p,0..1); requires initialized(p); requires *p==41;
        ensures readable(p,0..1); ensures *p==old(*p)+1; {*p=42; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("n=41", "n=7")));
    assert!(!checked(&source.replace("*p=42", "*p=43")));
}

#[test]
fn repeated_exclusive_occurrences_are_not_pure_idempotent_facts() {
    let source = "fn main()->u64 {let mut n=41; update(&mut n); return n;}
        fn update(p:&mut u64) requires writable(p,0..1); {*p=42; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace(
        "requires writable(p,0..1);",
        "requires writable(p,0..1); requires writable(p,0..1);"
    )));
    let source = "fn main()->u64 {let n=41; return read(&n);}
        fn read(p:&u64)->u64 requires readable(p,0..1); requires readable(p,0..1); {return *p;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("readable", "writable")));
}

#[test]
fn slice_length_and_memory_contents_bind_the_same_entry() {
    let source = "fn main()->u64 {let mut a=[41,7]; update(&mut a[0..2],0usize); return a[0];}
        fn update(p:&mut [u64],i:usize) requires len(p)==2usize; requires i==0usize;
        requires writable(p,0usize..len(p)); requires p[i]==41;
        ensures readable(p,0usize..len(p)); ensures p[i]==old(p[i])+1;
        {p[i]=42; return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("a[0..2]", "a[0..1]")));
    assert!(!checked(
        &source.replace("0usize..len(p)", "0usize..3usize")
    ));
}

#[test]
fn owner_return_and_consumption_are_real_body_effects() {
    let source = "fn main()->u64 {let p=make(); consume(p); return 0;}
        fn make()->Own<u64> ensures readable(result,0..1); {let p=alloc<u64>(1); *p=42; return p;}
        fn consume(p:Own<u64>) requires writable(p,0..1); {free(p); return;}";
    assert!(checked(source));
    assert!(!checked(&source.replace("*p=42;", "")));
    assert!(!checked(&source.replace(
        "{free(p); return;}",
        "ensures readable(p,0..1); {free(p); return;}"
    )));
}

#[test]
fn adjacent_ranges_share_one_allocation_without_duplicating_authority() {
    let source = "fn main()->u64 {let mut a=[1,2]; write(&mut a[0..2]); return 0;}
        fn write(p:&mut [u64]) requires len(p)==2usize;
        requires writable(p,0..1); requires writable(p,1..2);
        requires disjoint(p[0..1],p[1..2]); {p[0]=7; p[1]=8; return;}";
    assert!(checked(source));
    assert!(!checked(
        &source.replace("writable(p,1..2)", "writable(p,0..2)")
    ));
    assert!(!checked(&source.replace(
        "disjoint(p[0..1],p[1..2])",
        "disjoint(p[0..2],p[1..2])"
    )));
    // Empty ranges carry no access but must still have in-bounds endpoints.
    assert!(checked(
        &source.replace("writable(p,1..2)", "writable(p,2..2)")
    ));
    assert!(!checked(
        &source.replace("writable(p,1..2)", "writable(p,3..3)")
    ));
}

#[test]
fn forged_call_aliases_cannot_satisfy_two_exclusive_roots() {
    let source = "fn main()->u64 {let mut x=1; let mut y=2; write(&mut x,&mut y); return 0;}
        fn write(p:&mut u64,q:&mut u64) requires writable(p,0..1); requires writable(q,0..1); {*p=7; *q=8; return;}";
    assert!(checked(source));
    let out = analyze(&SourceFile::from_text("alias.nera", source));
    let mut raw = out.vir().unwrap().as_unit().clone();
    let main = &mut raw.runtime.functions[0];
    for block in &mut main.blocks {
        for instruction in &mut block.instructions {
            if let VirInstruction::Call { arguments, .. } = &mut instruction.instruction {
                arguments[2] = arguments[0];
                arguments[3] = arguments[1];
            }
        }
    }
    let raw = raw
        .into_validated()
        .expect("mutation keeps the physical signature");
    assert!(
        !verify_program(&raw.resolve().unwrap(), Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn returned_slice_and_cfg_resource_export_use_actual_authority() {
    let source = "fn main()->u64 {let mut a=[1,2]; let q=view(&mut a[0..2],true); return q[0];}
        fn view(p:&mut [u64],b:bool)->&mut [u64] requires len(p)==2usize; requires writable(p,0..2);
        ensures len(p)==old(len(p)); ensures len(result)==1usize;
        ensures writable(result,0..1); {if b {return &mut p[0..1];} else {return &mut p[0..1];}}";
    assert!(checked(source));
    assert!(!checked(
        &source.replace("writable(result,0..1)", "writable(result,0..2)")
    ));
}

#[test]
fn raw_existential_witness_selects_existing_bytes_and_cannot_create_resources() {
    let source = "fn main()->u64 {let n=41; return read(&n);} fn read(p:&u64)->u64 requires readable(p,0..1); {return *p;}";
    let out = analyze(&SourceFile::from_text("witness.nera", source));
    for (witness, expected) in [(Some(8), true), (Some(16), false), (None, false)] {
        let mut raw = out.vir().unwrap().as_unit().clone();
        let leaf = raw.specs.assertions()[0].clone();
        let binder = VirSpecBinderId::new(raw.specs.binders().len() as u32);
        raw.specs.binders_mut().push(VirSpecBinder {
            id: binder,
            owner: VirSpecBinderOwner::Clause(leaf.clause),
            name: "bytes".into(),
            ty: VirSpecType::U64,
            origin: leaf.origin,
        });
        let bound = VirSpecTermId::new(raw.specs.terms().len() as u32);
        raw.specs.terms_mut().push(VirSpecTerm {
            id: bound,
            clause: leaf.clause,
            ty: VirSpecType::U64,
            kind: VirSpecTermKind::Binder(binder),
            origin: leaf.origin,
        });
        let witness = witness.map(|n| {
            let id = VirSpecTermId::new(raw.specs.terms().len() as u32);
            raw.specs.terms_mut().push(VirSpecTerm {
                id,
                clause: leaf.clause,
                ty: VirSpecType::U64,
                kind: VirSpecTermKind::U64(n),
                origin: leaf.origin,
            });
            id
        });
        if let SpecAssertionKind::PointsTo { memory, .. } = &mut raw.specs.assertions_mut()[0].kind
        {
            memory.end_bytes = bound;
        } else {
            panic!("readable leaf");
        }
        let root = VirSpecAssertionId::new(raw.specs.assertions().len() as u32);
        raw.specs.assertions_mut().push(VirSpecAssertion {
            id: root,
            clause: leaf.clause,
            kind: SpecAssertionKind::Exists {
                binder,
                body: leaf.id,
                witness,
            },
            origin: leaf.origin,
        });
        raw.specs.clauses_mut()[leaf.clause.get() as usize].kind =
            VirSpecClauseKind::Assertion { root };
        let raw = raw.into_validated().unwrap();
        let actual = verify_program(&raw.resolve().unwrap(), Default::default())
            .is_ok_and(|r| r.is_memory_checked_core0());
        assert_eq!(actual, expected);
    }
}

#[test]
fn resource_schema_scope_and_type_cannot_be_forged() {
    let source = "fn main()->u64 {let n=41; return read(&n);} fn read(p:&u64)->u64 requires readable(p,0..1); {return *p;}";
    let out = analyze(&SourceFile::from_text("resource-schema.nera", source));
    let raw = out.vir().unwrap().as_unit();
    for mutation in 0..3 {
        let mut raw = raw.clone();
        let SpecAssertionKind::PointsTo { memory, .. } = &mut raw.specs.assertions_mut()[0].kind
        else {
            unreachable!()
        };
        match mutation {
            0 => {
                memory.pointer = VirSpecSnapshot::Result {
                    function: VirFunctionId::new(1),
                    slot: 0,
                }
            }
            1 => memory.authority = memory.pointer,
            _ => {
                memory.pointer = VirSpecSnapshot::Parameter {
                    function: VirFunctionId::new(0),
                    slot: 0,
                }
            }
        }
        assert!(raw.into_validated().is_err());
    }
    for source in [
        "fn main()->u64 requires readable(result,0..1); {return 0;}",
        "fn main()->u64 {return 0;} fn f(p:&u64) requires readable(p,0..1) || true; {return;}",
        "fn main()->u64 {return 0;} fn f(p:&u64) requires readable(p,0..1); {return;} fn readable()->bool {return true;}",
    ] {
        assert!(
            analyze(&SourceFile::from_text("gated.nera", source))
                .vir()
                .is_none()
        );
    }
}

#[test]
fn fresh_result_identity_must_come_from_actual_allocation() {
    let source = "fn main()->u64 {let x=1; let p=make(&x); free(p); return 0;}
        fn make(p:&u64)->Own<u64> requires readable(p,0..1); ensures readable(result,0..1);
        ensures disjoint(result[0..1],p[0..1]); {let q=alloc<u64>(1); *q=42; return q;}";
    assert!(checked(source));
    assert!(!checked(&source.replace(
        "disjoint(result[0..1],p[0..1])",
        "disjoint(result[0..1],result[0..1])"
    )));
    let source = "fn main()->u64 {let p=alloc<u64>(1); *p=42; let q=identity(p); free(q); return 0;}
        fn identity(p:Own<u64>)->Own<u64> requires readable(p,0..1); ensures disjoint(result[0..1],p[0..1]); {return p;}";
    assert!(!checked(source));
}

#[test]
fn joint_ledger_respects_query_budget_and_recursive_calls_recheck_resources() {
    let source = include_str!("../spec/cases/verify/contract-resources.nera");
    let out = analyze(&SourceFile::from_text("budget.nera", source));
    let unit = out.vir().unwrap();
    let config = CfgAnalysisConfig {
        max_region_pairs_per_instruction: 0,
        ..Default::default()
    };
    assert!(
        !verify_program(&unit.resolve().unwrap(), config)
            .is_ok_and(|r| r.is_memory_checked_core0())
    );
    let source = "fn main()->u64 {let n=1; return read(&n);} fn read(p:&u64)->u64 requires readable(p,0..1); {return read(p);}";
    assert!(checked(source)); // partial correctness only; do not execute divergence
    assert!(!checked(
        &source.replace("readable(p,0..1)", "readable(p,0..2)")
    ));
}
