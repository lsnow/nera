use nera::*;
#[path = "support/contract_composition.rs"]
mod fixture;
use fixture::*;

#[test]
fn modules_const_instances_and_conditional_borrows_share_one_verified_unit() {
    let compiler = session(&[("app", APP), ("left", LEFT), ("right", RIGHT)]);
    let report = compiler.verify("app").unwrap();
    assert!(
        report.is_checked(),
        "{}",
        nera::verification::render_text(&report, nera::verification::TextReportMode::Explain)
    );
    let analysis = compiler.analyze("app").unwrap();
    let unit = analysis.frontend().vir().unwrap();
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
    let reordered = session(&[("right", RIGHT), ("left", LEFT), ("app", APP)]);
    assert_eq!(analysis, reordered.analyze("app").unwrap());
}

#[test]
fn wrong_const_resource_bound_and_one_module_postcondition_do_not_leak_proofs() {
    for (left, right) in [
        (LEFT.replace("view<u64,2>", "view<u64,1>"), RIGHT.to_owned()),
        (
            LEFT.to_owned(),
            RIGHT.replace("len(result)==N", "len(result)==2usize"),
        ),
        (
            LEFT.replace("readable(result,0..1)", "readable(result,0..3)"),
            RIGHT.to_owned(),
        ),
    ] {
        let compiler = session(&[("app", APP), ("left", &left), ("right", &right)]);
        let analysis = compiler.analyze("app").unwrap();
        assert!(
            analysis.frontend().vir().is_some(),
            "{:?}",
            analysis.frontend().issues()
        );
        assert!(!compiler.verify("app").unwrap().is_checked());
    }
}

#[test]
fn repeated_generic_recursive_instances_keep_independent_contracts() {
    let source = "fn main()->u64 {let a=step<u64>(0,41); let b=step<bool>(0,true); return a+b;}
        fn step<T>(n:u64,x:T)->u64 requires n<=2; ensures result==21; reads (); writes ();
        {if n==2 {return 21;} return step<T>(n+1,x);}";
    let output = analyze(&SourceFile::from_text("generic-recursion.nera", source));
    let unit = output
        .vir()
        .unwrap_or_else(|| panic!("{:?}", output.issues()));
    let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn contracts_do_not_override_type_or_return_borrow_sources() {
    let wrong_type = RIGHT.replace("view<bool,1>", "view<u64,1>");
    assert!(
        session(&[("app", APP), ("left", LEFT), ("right", &wrong_type)])
            .analyze("app")
            .unwrap()
            .frontend()
            .vir()
            .is_none()
    );
    for source in [
        "fn main()->u64 {return 0;} fn bad()->&u64 ensures readable(result,0..1); {let x=1; return &x;}",
        "fn main()->u64 {return 0;} fn bad(p:&u64)->&mut u64 ensures writable(result,0..1); {return p;}",
    ] {
        assert!(
            analyze(&SourceFile::from_text("bad-source.nera", source))
                .vir()
                .is_none()
        );
    }
}

#[test]
fn module_contract_and_transitive_body_changes_invalidate_existing_audit() {
    use nera::verifier::relation::audit::RelationReplayCache;
    use nera::verifier::summary::audit::SummaryAudit;
    let compiler = session(&[("app", APP), ("left", LEFT), ("right", RIGHT)]);
    let analysis = compiler.analyze("app").unwrap();
    let unit = analysis.frontend().vir().unwrap().resolve().unwrap();
    let audit = SummaryAudit::from_report(&verify_program(&unit, Default::default()).unwrap());
    assert!(
        RelationReplayCache::new(&unit, Default::default())
            .unwrap()
            .accepts_summary_audit(&audit)
    );
    for right in [
        RIGHT.replace("return 1", "return 2"),
        RIGHT.replace("len(result)==N", "len(result)==2usize"),
        RIGHT.replace("{return p;}", "{let q=p; return q;}"),
    ] {
        let compiler = session(&[("app", APP), ("left", LEFT), ("right", &right)]);
        let analysis = compiler.analyze("app").unwrap();
        let unit = analysis.frontend().vir().unwrap().resolve().unwrap();
        assert!(
            !RelationReplayCache::new(&unit, Default::default())
                .unwrap()
                .accepts_summary_audit(&audit)
        );
    }
}

#[test]
fn resource_snapshot_cannot_be_captured_from_another_generic_instance() {
    let compiler = session(&[("app", APP), ("left", LEFT), ("right", RIGHT)]);
    let analysis = compiler.analyze("app").unwrap();
    let original = analysis.frontend().vir().unwrap();
    let mut raw = original.as_unit().clone();
    let mut roots = raw.specs.assertions().iter().filter_map(|a| {
        let SpecAssertionKind::Permission(memory) = &a.kind else {
            return None;
        };
        let VirSpecSnapshot::Parameter { function, slot } = memory.pointer else {
            return None;
        };
        Some((a.id, function, slot))
    });
    let (id, first, _) = roots.next().unwrap();
    let (_, other, slot) = roots.find(|(_, function, _)| *function != first).unwrap();
    let SpecAssertionKind::Permission(memory) =
        &mut raw.specs.assertions_mut()[id.get() as usize].kind
    else {
        unreachable!()
    };
    memory.pointer = VirSpecSnapshot::Parameter {
        function: other,
        slot,
    };
    assert!(raw.into_validated().is_err());
}
