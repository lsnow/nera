use nera::*;

#[path = "support/opaque_arena.rs"]
mod fixture;

fn report(output: &FrontendOutput) -> ProgramVerification {
    assert!(output.vir().is_some(), "{:?}", output.issues());
    verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .expect("semantic analysis must finish")
}

fn checked(output: &FrontendOutput, expected: u64) {
    let report = report(output);
    let failed: Vec<_> = report
        .functions()
        .iter()
        .flat_map(|(id, f)| {
            f.cfg()
                .obligations()
                .iter()
                .filter(|c| !c.obligation().is_proven())
                .map(move |c| (*id, c.obligation().kind()))
        })
        .collect();
    assert!(report.is_memory_checked_core0(), "{failed:?}");
    let resolved = output.vir().unwrap().resolve().unwrap();
    let replay =
        nera::verifier::relation::audit::RelationReplayCache::new(&resolved, Default::default())
            .unwrap();
    for (&id, f) in report.functions() {
        assert_eq!(
            f.summary().state,
            nera::verifier::summary::SummaryState::Closed
        );
        assert!(replay.accepts_memory_trace(
            id,
            f.cfg().provenance_evidence(),
            f.cfg().relation_queries(),
            f.cfg().relation_evidence()
        ));
    }
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(expected)]
    );
}

#[test]
fn opaque_arena_modules_cover_both_capacities_and_lifecycle() {
    for capacity in [6, 8] {
        let (library, forward, app) = fixture::instance(capacity);
        for entry in fixture::ENTRIES {
            let analysis = fixture::session_entry(&library, &forward, &app, entry)
                .analyze("app")
                .unwrap();
            checked(analysis.frontend(), 49);
        }
    }
}

#[test]
fn opaque_arena_rejects_semantic_misuse_after_vir_admission() {
    use ResourceObligationKind as K;
    for (name, library, forward, app, expected) in [
        (
            "capacity",
            fixture::LIBRARY.to_owned(),
            fixture::FORWARD.to_owned(),
            fixture::APP.replace(
                "allocate(&mut *arena,6usize)",
                "allocate(&mut *arena,7usize)",
            ),
            "precondition",
        ),
        (
            "invariant",
            fixture::LIBRARY.replace("p.cursor=end;", "p.cursor=7usize;"),
            fixture::FORWARD.to_owned(),
            fixture::APP.to_owned(),
            "predicate",
        ),
        (
            "uninitialized",
            fixture::LIBRARY.replace("backing[i]=0;", ""),
            fixture::FORWARD.to_owned(),
            fixture::APP.to_owned(),
            "initialization",
        ),
        (
            "live reset",
            fixture::LIBRARY.to_owned(),
            fixture::FORWARD.to_owned(),
            fixture::APP.replace("remaining[0]=7;", "clear(&mut *arena); remaining[0]=7;"),
            "authority",
        ),
        (
            "live free",
            fixture::LIBRARY.to_owned(),
            fixture::FORWARD.to_owned(),
            fixture::APP.replace(
                "let total=client(&mut *arena,1usize,3usize);",
                "let view=allocate(&mut *arena,6usize); release(arena); let total=view[0];",
            ),
            "authority",
        ),
        (
            "open return",
            fixture::LIBRARY.replace(
                "    p.cursor=0usize;\n    fold Ready(p);\n    return;",
                "    p.cursor=0usize;\n    return;",
            ),
            fixture::FORWARD.to_owned(),
            fixture::APP.to_owned(),
            "boundary",
        ),
        (
            "forward contract",
            fixture::LIBRARY.to_owned(),
            fixture::FORWARD.replace("requires count<=6usize;", ""),
            fixture::APP.to_owned(),
            "precondition",
        ),
    ] {
        let analysis = fixture::session(&library, &forward, &app)
            .analyze("app")
            .unwrap();
        let report = report(analysis.frontend());
        assert!(!report.is_memory_checked_core0(), "{name}");
        let failed: Vec<_> = report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .filter(|c| !c.obligation().is_proven())
            .map(|c| c.obligation().kind())
            .collect();
        assert!(
            failed.iter().any(|k| match expected {
                "precondition" => matches!(k, K::CallContractPrecondition { .. }),
                "predicate" => matches!(k, K::PredicateActionValid { .. }),
                "initialization" => matches!(
                    k,
                    K::LoopInvariantEstablished { .. }
                        | K::MemoryInitialized { .. }
                        | K::ObjectValueBytesInitialized { .. }
                ),
                "authority" => matches!(
                    k,
                    K::PermissionAvailable { .. }
                        | K::PredicateCarrierMovable { .. }
                        | K::PredicateInterfaceValid { .. }
                ),
                "boundary" => matches!(
                    k,
                    K::PredicateBoundaryRestored { .. } | K::PredicateInterfaceValid { .. }
                ),
                _ => false,
            }),
            "{name}: wrong failure layer: {failed:?}"
        );
    }
}

#[test]
fn opaque_arena_clients_cannot_observe_or_open_private_representation() {
    for (name, forward, app) in [
        (
            "runtime cursor",
            fixture::FORWARD.to_owned(),
            fixture::APP.replace(
                "let parent=allocate",
                "let hidden=arena.cursor; let parent=allocate",
            ),
        ),
        (
            "contract cursor",
            fixture::FORWARD.to_owned(),
            fixture::APP.replace(
                "requires Ready(arena);",
                "requires Ready(arena); requires arena.cursor==0usize;",
            ),
        ),
        (
            "private slots",
            fixture::FORWARD.to_owned(),
            fixture::APP.replace(
                "let parent=allocate",
                "let hidden=arena.slots[0]; let parent=allocate",
            ),
        ),
        (
            "unfold",
            fixture::FORWARD.to_owned(),
            fixture::APP.replace(
                "let parent=allocate",
                "unfold Ready(arena); let parent=allocate",
            ),
        ),
        (
            "forward cursor",
            fixture::FORWARD.replace(
                "{ return reserve(p,count); }",
                "{ let hidden=p.cursor; return reserve(p,count); }",
            ),
            fixture::APP.to_owned(),
        ),
    ] {
        let analysis = fixture::session(fixture::LIBRARY, &forward, &app)
            .analyze("app")
            .unwrap();
        assert!(analysis.frontend().vir().is_none(), "{name}");
        assert!(
            analysis
                .frontend()
                .issues()
                .iter()
                .any(|i| i.kind() == FrontendIssueKind::Elaboration
                    && (i.diagnostic().message().contains("opaque")
                        || i.diagnostic().message().contains("private"))),
            "{name}: {:?}",
            analysis.frontend().issues()
        );
    }
}

#[test]
fn canonical_loan_ids_follow_final_cfg_order_after_nested_loops() {
    let source = "fn main()->u64 { return choose(true)+choose(false); }
        fn choose(flag:bool)->u64 {
            let p=alloc<u64>(1); *p=21;
            if flag {
                let mut i=0usize;
                while i<2usize { invariant i<=2usize; i=i+1usize; }
                let view=&*p; return *view;
            } else { let view=&*p; return *view; }
        }";
    checked(
        &analyze(&SourceFile::from_text("loan-order.nera", source)),
        42,
    );
    let reborrow = source.replace(
        "let view=&*p;",
        "let parent=&mut *p; let view=&mut *parent;",
    );
    checked(
        &analyze(&SourceFile::from_text("reborrow-order.nera", reborrow)),
        42,
    );
    let alias = source.replace("return *view;", "let copy=view; return *copy;");
    checked(
        &analyze(&SourceFile::from_text("alias-order.nera", alias)),
        42,
    );
}
