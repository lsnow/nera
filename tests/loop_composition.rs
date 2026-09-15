use nera::*;
#[path = "support/loop_composition.rs"]
mod fixture;
#[path = "support/runtime_origins.rs"]
mod runtime_origins;
use runtime_origins::runtime_with_resolved_origins;

fn checked(source: &str) {
    let out = analyze(&SourceFile::from_text("loop-composition.nera", source));
    assert_eq!(
        out.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        out.issues()
    );
    let report =
        verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
}

#[test]
fn scalar_calls_use_real_requires_and_ensures_on_each_iteration() {
    checked("fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=next(i);} assert i==3; return i;}
        fn next(i:u64)->u64 requires i<3; ensures result==i+1; {return i+1;}");
}

#[test]
fn false_condition_call_keeps_its_actual_memory_effect() {
    let source = "fn main()->u64 {let mut x=0; let mut i=0;
        while stop(&mut x) {invariant i<=3; i=i+1;}
        let value=x; return value;}
        fn stop(p:&mut u64)->bool reads (); writes p[0..1]; {*p=42; return false;}";
    checked(source);
    let out = analyze(&SourceFile::from_text("condition-effect.nera", source));
    assert_eq!(
        interpret(out.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    // The summary need not export the exact written value, but it must not
    // preserve the caller's stale pre-call value on the false-condition exit.
    let bad = source.replace("return value;", "assert value==0; return value;");
    let out = analyze(&SourceFile::from_text("stale-condition-effect.nera", &bad));
    assert!(
        !verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn module_generic_conditional_borrow_and_slice_effects_compose_with_loop() {
    let session = fixture::session(fixture::APP, fixture::OPS);
    let analysis = session.analyze("app").unwrap();
    assert!(
        analysis.frontend().vir().is_some(),
        "{:?}",
        analysis.frontend().issues()
    );
    let unit = analysis.frontend().vir().unwrap();
    let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let plain = fixture::session(&fixture::erase_invariants(fixture::APP), fixture::OPS);
    assert!(plain.verify("app").unwrap().is_checked());
    let plain_analysis = plain.analyze("app").unwrap();
    assert_eq!(
        runtime_with_resolved_origins(unit),
        runtime_with_resolved_origins(plain_analysis.frontend().vir().unwrap())
    );
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn fixed_borrow_parameter_can_cross_an_inductive_loop() {
    checked("fn main()->u64 {let mut a=[0,0]; fill(&mut a,2usize); return a[1];}
        fn fill(p:&mut [u64;2],n:usize) requires n<=2usize; {let mut i=0usize; while i<n {invariant i<=n; p[i]=42; i=i+1usize;} return;}");
}

#[test]
fn calls_havoc_written_content_but_preserve_unrelated_allocation() {
    let source = "fn main()->u64 {let p=alloc<u64>(1); *p=0; let q=alloc<u64>(1); *q=7;
        let mut i=0; while i<3 {invariant i<=3; let value=*q; assert value==7;
        let r=view(&mut *p); write(r); i=i+1;}
        free(p); free(q); return 42;}
        fn view(p:&mut u64)->&mut u64 {return p;}
        fn write(p:&mut u64) reads (); writes p[0..1]; {*p=42; return;}";
    checked(source);
    for bad in [
        source.replace(
            "let value=*q; assert value==7",
            "let value=*p; assert value==0",
        ),
        source.replace("writes p[0..1]", "writes ()"),
    ] {
        let out = analyze(&SourceFile::from_text("bad-call-frame.nera", &bad));
        assert!(out.vir().is_some(), "{:?}", out.issues());
        assert!(
            !verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default())
                .unwrap()
                .is_memory_checked_core0()
        );
    }
}

#[test]
fn bad_callee_pre_post_and_loop_contracts_block_publication() {
    for (app, ops) in [
        (
            fixture::APP.replace("set<u64,2>", "set<u64,1>"),
            fixture::OPS.to_owned(),
        ),
        (
            fixture::APP.replace(",i,42", ",2usize,42"),
            fixture::OPS.to_owned(),
        ),
        (
            fixture::APP.to_owned(),
            fixture::OPS.replace("readable(result,0..1)", "readable(result,0..2)"),
        ),
        (
            fixture::APP.replace("invariant i<=2usize", "invariant i==0usize"),
            fixture::OPS.to_owned(),
        ),
        (
            fixture::APP.to_owned(),
            fixture::OPS.replace("{p[i]=value;", "writes (); {p[i]=value;"),
        ),
    ] {
        let compiler = fixture::session(&app, &ops);
        let preview = compiler.verify("app").unwrap();
        assert!(!preview.is_checked());
        assert!(
            compiler.analyze("app").unwrap().frontend().vir().is_some(),
            "{:?}",
            preview.outcome()
        );
    }
}

#[test]
fn callee_nonmonotone_effect_and_foreign_loop_origins_fail_validation() {
    let compiler = fixture::session(fixture::APP, fixture::OPS);
    let analysis = compiler.analyze("app").unwrap();
    let original = analysis.frontend().vir().unwrap().as_unit();
    let mut deinit = original.clone();
    let instruction = deinit
        .runtime
        .functions
        .iter_mut()
        .flat_map(|f| &mut f.blocks)
        .flat_map(|b| &mut b.instructions)
        .find(|i| matches!(i.instruction, VirInstruction::Write { .. }))
        .unwrap();
    let VirInstruction::Write {
        pointer,
        permission,
        access,
        ..
    } = instruction.instruction
    else {
        unreachable!()
    };
    instruction.instruction = VirInstruction::ObjectDeinitialize {
        pointer,
        permission,
        access,
    };
    assert!(matches!(
        deinit.validate().unwrap_err().kind(),
        VirValidationErrorKind::LoopInvariantFeatureGated(_)
    ));
    let mut foreign = original.clone();
    let origin = foreign
        .specs
        .clauses()
        .iter()
        .find(|c| c.location.function() != VirFunctionId::new(0))
        .unwrap()
        .origin
        .origin();
    let clause = foreign.specs.loop_invariants()[0].clause;
    foreign.specs.loop_invariants_mut()[0].origin = origin;
    foreign.specs.clauses_mut()[clause.get() as usize].origin =
        VirSpecClauseOrigin::Explicit { origin };
    assert!(foreign.validate().is_err());
    let mut boundary = original.clone();
    boundary.specs.loop_invariants_mut()[0]
        .boundary
        .as_mut()
        .unwrap()
        .back_edges
        .clear();
    assert!(boundary.validate().is_err());
}

#[test]
fn loop_call_audit_binds_callee_body_instance_and_each_loop_check() {
    use nera::verifier::{relation::audit::RelationReplayCache, summary::audit::SummaryAudit};
    let compiler = fixture::session(fixture::APP, fixture::OPS);
    let analysis = compiler.analyze("app").unwrap();
    let unit = analysis.frontend().vir().unwrap();
    let resolved = unit.resolve().unwrap();
    let report = verify_program(&resolved, Default::default()).unwrap();
    let audit = SummaryAudit::from_report(&report);
    let cache = RelationReplayCache::new(&resolved, Default::default()).unwrap();
    assert!(cache.accepts_summary_audit(&audit));
    let mut missing = audit.clone();
    let main = missing
        .functions
        .iter_mut()
        .find(|f| f.function == VirFunctionId::new(0))
        .unwrap();
    let index = main
        .requirements
        .iter()
        .position(|(_, f)| {
            matches!(
                f.site(),
                VerifierFindingSite::Spec {
                    entity: VerifierSpecEntity::Clause(_),
                    ..
                }
            )
        })
        .unwrap();
    main.requirements.remove(index);
    assert!(!cache.accepts_summary_audit(&missing));
    let changed = fixture::session(&fixture::APP.replace(",i,42", ",i,43"), fixture::OPS)
        .analyze("app")
        .unwrap();
    let changed_unit = changed.frontend().vir().unwrap().resolve().unwrap();
    assert!(
        !RelationReplayCache::new(&changed_unit, Default::default())
            .unwrap()
            .accepts_summary_audit(&audit)
    );
    let mut mismatch = unit.as_unit().clone();
    let calls: Vec<_> = mismatch.runtime.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter_map(|i| {
            if let VirInstruction::Call { target, .. } = &i.instruction {
                Some(target.clone())
            } else {
                None
            }
        })
        .collect();
    let a = calls.iter().find(|c| c.symbol.contains("set")).unwrap();
    let b = calls
        .iter()
        .find(|c| c.symbol.contains("set") && c.contract != a.contract)
        .unwrap();
    for block in &mut mismatch.runtime.functions[0].blocks {
        for i in &mut block.instructions {
            if let VirInstruction::Call { target, .. } = &mut i.instruction
                && target.contract == a.contract
            {
                target.contract = b.contract;
            }
        }
    }
    assert!(mismatch.validate().is_err());
}

#[test]
fn condition_calls_and_recursive_contract_closure_are_not_assumed() {
    checked("fn main()->u64 {let mut i=0; while more(i) {invariant i<=3; i=i+1;} assert i==3; return i;}
        fn more(i:u64)->bool ensures result==(i<3); {return i<3;}");
    checked("fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=finish(i);} assert i==3; return i;}
        fn finish(n:u64)->u64 requires n<=2; ensures result==3; {if n==2 {return 3;} return finish(n+1);}");
    let source = "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=bad(i);} return i;}
        fn bad(i:u64)->u64 requires i<3; ensures result==i+1; {if i==0 {return 7;} return bad(0);}";
    let out = analyze(&SourceFile::from_text("recursive-loop.nera", source));
    assert!(out.vir().is_some(), "{:?}", out.issues());
    assert!(
        !verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn identical_module_spans_do_not_share_loop_origins_or_callee_proofs() {
    use nera::session::CompilerSession;
    use nera::source::{SourceDatabase, SourceInput};
    let app =
        "module app; use left::count; use more::other; fn main()->u64 {return count(2)+other(3);}";
    let left = "module left; pub fn count(n:u64)->u64 requires n<=3; ensures result==3; {
        let mut i=0; while i<3 {invariant i<=3; i=step(i);} return i;}
        fn step(i:u64)->u64 requires i<3; ensures result==i+1; {return i+1;}";
    let more = left.replace("left", "more").replace("count", "other");
    let make = |more: &str| {
        CompilerSession::modules(
            SourceDatabase::new(vec![
                SourceInput::new("app", SourceFile::from_text("app.nera", app)),
                SourceInput::new("left", SourceFile::from_text("left.nera", left)),
                SourceInput::new("more", SourceFile::from_text("more.nera", more)),
            ])
            .unwrap(),
            Default::default(),
            "app::main",
        )
        .unwrap()
    };
    let compiler = make(&more);
    let preview = compiler.verify("app").unwrap();
    assert!(
        preview.is_checked(),
        "{}",
        nera::verification::render_text(&preview, nera::verification::TextReportMode::Summary)
    );
    let analysis = compiler.analyze("app").unwrap();
    let unit = analysis.frontend().vir().unwrap().as_unit();
    let invariants = unit.specs.loop_invariants();
    assert_eq!(invariants.len(), 2);
    let a = unit
        .source_map
        .source_span_for_origin(invariants[0].origin)
        .unwrap();
    let b = unit
        .source_map
        .source_span_for_origin(invariants[1].origin)
        .unwrap();
    assert_eq!(a.span, b.span);
    assert_ne!(a.source, b.source);
    let mut raw = unit.clone();
    raw.specs.loop_invariants_mut()[0].origin = invariants[1].origin;
    raw.specs.clauses_mut()[invariants[0].clause.get() as usize].origin =
        VirSpecClauseOrigin::Explicit {
            origin: invariants[1].origin,
        };
    assert!(raw.validate().is_err());
    let bad = make(&more.replace("return i+1", "return i+2"));
    let preview = bad.verify("app").unwrap();
    assert!(!preview.is_checked());
    let text =
        nera::verification::render_text(&preview, nera::verification::TextReportMode::Explain);
    assert!(text.contains("more.nera"));
}
