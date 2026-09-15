use crate::*;

fn raw(source: &str) -> VirUnit {
    let (file, hir) = typed(source);
    super::super::lower_raw_sources(&hir, &[&file], false).unwrap()
}

fn typed(source: &str) -> (SourceFile, HirProgram) {
    let file = SourceFile::from_text("loop-schema.nera", source);
    let lexed = lex(&file);
    let parsed = crate::frontend::parser::parse(&file, lexed.tokens(), false).unwrap();
    let graph = crate::frontend::modules::ModuleGraph::single(&parsed.ast).unwrap();
    let (concrete, _) = crate::frontend::instantiate::run(&[&parsed.ast], &graph).unwrap();
    let refs: Vec<_> = concrete.iter().collect();
    let hir = crate::frontend::hir::elaborate_modules(&refs, graph).unwrap();
    (file, hir)
}

#[test]
fn typed_loop_snapshots_reject_foreign_owner_scope_type_and_orphans() {
    let (_, hir) = typed(
        "fn main()->u64 {let mut i=0; while i<3 {invariant old(i)<=i; let hidden=1; i=i+hidden;} return i;}",
    );
    super::hir_from_tables(super::program_tables(&hir)).unwrap();
    for mutation in 0..7 {
        let mut tables = super::program_tables(&hir);
        let term = tables
            .specs
            .terms
            .iter_mut()
            .find(|t| {
                matches!(
                    t.kind,
                    HirSpecTermKind::Snapshot(HirSpecSnapshot::LoopEntry { .. })
                )
            })
            .unwrap();
        let HirSpecTermKind::Snapshot(HirSpecSnapshot::LoopEntry {
            function,
            loop_id,
            local,
        }) = &mut term.kind
        else {
            unreachable!()
        };
        match mutation {
            0 => *function = HirFunctionId::new(99),
            1 => *loop_id = HirLoopId::new(99),
            2 => *local = HirLocalId::new(1), // body-only `hidden`
            3 => {
                term.ty = tables
                    .types
                    .iter()
                    .find(|t| t.kind == HirTypeKind::Bool)
                    .unwrap()
                    .id
            }
            4 => tables.specs.loop_invariants[0].loop_id = HirLoopId::new(99),
            5 => tables.specs.loop_invariants[0].clause = HirSpecClauseId::new(99),
            _ => tables.specs.loop_invariants[0].span = tables.functions[0].span,
        }
        assert!(
            super::hir_from_tables(tables).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn typed_boundaries_preserve_erasure_and_scalar_profile_gates() {
    for source in [
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=i+1;} return i;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant old(i)<=i; invariant i<=3; i=i+1;} return i;}",
        "fn main()->u64 {let mut sum=0; for i in 0..3 {invariant i<=3; sum=sum+i;} return sum;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; for j in 0..2 {invariant j<=2; if j==1 {continue;}} i=i+1;} return i;}",
        "fn main()->u64 {let mut i=0; while false {invariant i<=3; i=i+1;} return i;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; if i==1 {break;} i=i+1;} return i;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; if i==1 {return i;} i=i+1; continue;} return i;}",
        "fn main()->u64 {for i in 0..3 {invariant i<=3; if i==1 {return i;} continue;} return 3;}",
        "fn main()->u64 {while true {invariant true; return 1;} return 0;}",
        "fn main()->u64 {for i in 0..3 {invariant i<=3; break;} return 0;}",
    ] {
        let unit = raw(source);
        assert!(!unit.specs.loop_invariants().is_empty());
        let gated = source.contains("old(");
        if gated {
            assert!(matches!(
                unit.validate().unwrap_err().kind(),
                VirValidationErrorKind::LoopInvariantFeatureGated(_)
            ));
        } else {
            unit.validate().unwrap();
        }
        let output = analyze(&SourceFile::from_text("loop-schema.nera", source));
        assert_eq!(
            output.status(),
            if gated {
                FrontendStatus::Unsupported
            } else {
                FrontendStatus::AcceptedProposal
            }
        );
        assert_eq!(output.vir().is_none(), gated);
        let mut plain = source.to_owned();
        while let Some(start) = plain.find("invariant ") {
            let end = start + plain[start..].find(';').unwrap() + 1;
            plain.replace_range(start..end, &" ".repeat(end - start));
        }
        let unannotated = analyze(&SourceFile::from_text("loop-schema.nera", plain));
        assert_eq!(&unit.runtime, &unannotated.vir().unwrap().as_unit().runtime);
        // Runtime projection is executable only after explicitly erasing all
        // Spec declarations in this test, not through a production bypass.
        let mut erased = unit;
        erased.specs = VirSpecEnvironment::implicit(&erased.runtime);
        erased.rebuild_source_map_from_runtime("erased-loop.vir", source.len());
        let erased = erased.into_validated().unwrap();
        let resolved = erased.resolve().unwrap();
        let plain_resolved = unannotated.vir().unwrap().resolve().unwrap();
        assert_eq!(
            interpret(resolved.runtime()).unwrap().values(),
            interpret(plain_resolved.runtime()).unwrap().values()
        );
        let assembly = crate::backend::X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(resolved.runtime())
            .unwrap();
        assert_eq!(
            assembly,
            crate::backend::X86_64_UNKNOWN_LINUX_GNU
                .codegen_program(plain_resolved.runtime())
                .unwrap()
        );
    }
}

#[test]
fn independent_boundary_validation_rejects_mutated_edges_and_bindings() {
    let unit =
        raw("fn main()->u64 {let mut i=0; while i<3 {invariant old(i)<=i; i=i+1;} return i;}");
    for mutation in 0..10 {
        let mut bad = unit.clone();
        let b = bad.specs.loop_invariants_mut()[0]
            .boundary
            .as_mut()
            .unwrap();
        match mutation {
            0 => b.entries.clear(),
            1 => b.back_edges.clear(),
            2 => b.exits.clear(),
            3 => b.preheader = b.header,
            4 => b.bindings[0].entry = b.bindings[0].head,
            5 => b.bindings[0].ty = VirType::Bool,
            6 => b.blocks.push(b.header),
            7 => b.condition = b.preheader,
            8 => b.latch = Some(b.header),
            _ => b.bindings.clear(),
        }
        let error = bad.into_validated().unwrap_err();
        assert!(
            !matches!(
                error.kind(),
                VirValidationErrorKind::LoopInvariantFeatureGated(_)
            ),
            "mutation {mutation}: {error:?}"
        );
    }
}

#[test]
fn generic_module_loops_keep_separate_owners_and_origins() {
    let sources = [
        ("absent", "module absent; struct Unused { value:u64, }"),
        (
            "app",
            "module app; use left::count; use more::other; fn main()->u64 {return count<2>()+count<3>()+other<4>();}",
        ),
        (
            "left",
            "module left; pub fn count<const N:usize>()->u64 {let mut i=0usize; while i<N {invariant i<=N; i=i+1usize;} return 1;}",
        ),
        (
            "more",
            "module more; pub fn other<const N:usize>()->u64 {let mut i=0usize; while i<N {invariant i<=N; i=i+1usize;} return 1;}",
        ),
    ];
    let files: Vec<_> = sources
        .iter()
        .map(|(name, source)| SourceFile::from_text(format!("{name}.nera"), *source))
        .collect();
    let parsed: Vec<_> = files
        .iter()
        .map(|f| crate::frontend::parser::parse(f, lex(f).tokens(), true).unwrap())
        .collect();
    let mapped: Vec<_> = sources
        .iter()
        .zip(&parsed)
        .map(|((name, _), p)| (name.to_string(), &p.ast))
        .collect();
    let graph = crate::frontend::modules::ModuleGraph::build(&mapped, "app::main").unwrap();
    let asts: Vec<_> = parsed.iter().map(|p| &p.ast).collect();
    let (concrete, _) = crate::frontend::instantiate::run(&asts, &graph).unwrap();
    let hir = crate::frontend::hir::elaborate_modules(&concrete.iter().collect::<Vec<_>>(), graph)
        .unwrap();
    let unit =
        super::super::lower_raw_sources(&hir, &files.iter().collect::<Vec<_>>(), true).unwrap();
    assert_eq!(unit.specs.loop_invariants().len(), 3);
    unit.validate().unwrap();
    let owners: std::collections::BTreeSet<_> = unit
        .specs
        .loop_invariants()
        .iter()
        .map(|i| i.function)
        .collect();
    assert_eq!(owners.len(), 3);
    let source_ids: std::collections::BTreeSet<_> = unit
        .specs
        .loop_invariants()
        .iter()
        .map(|i| match unit.source_map.origin(i.origin).unwrap().kind {
            VirOriginKind::User { source, .. } => source,
            _ => panic!("explicit invariant must retain its user source"),
        })
        .collect();
    assert_eq!(source_ids.len(), 2);
    let spans: Vec<_> = unit
        .specs
        .loop_invariants()
        .iter()
        .map(|i| {
            unit.source_map
                .source_span_for_origin(i.origin)
                .unwrap()
                .span
        })
        .collect();
    assert!(spans.iter().all(|span| *span == spans[0]));
    let mut tables = super::program_tables(&hir);
    let gated = tables.specs.loop_invariants.last().unwrap().clone();
    let term = tables
        .specs
        .terms
        .iter_mut()
        .find(|t| {
            t.clause == gated.clause
                && matches!(
                    t.kind,
                    HirSpecTermKind::Snapshot(HirSpecSnapshot::Local { .. })
                )
        })
        .unwrap();
    let HirSpecTermKind::Snapshot(HirSpecSnapshot::Local { function, local }) = term.kind else {
        unreachable!()
    };
    term.kind = HirSpecTermKind::Snapshot(HirSpecSnapshot::LoopEntry {
        function,
        loop_id: gated.loop_id,
        local,
    });
    let gated_hir = super::hir_from_tables(tables).unwrap();
    let error =
        super::super::lower_modules(&gated_hir, &files.iter().collect::<Vec<_>>()).unwrap_err();
    let source = unit
        .source_map
        .source_span_for_origin(unit.specs.loop_invariants().last().unwrap().origin)
        .unwrap();
    let module = hir.function_by_id(gated.function).unwrap().module;
    assert_eq!(error.source, Some(VirSourceId::new(module.get())));
    assert_ne!(error.source, Some(source.source)); // compact VIR table omits `absent`
    assert_eq!(error.span, source.span);
    let mut bad = unit.clone();
    bad.specs.loop_invariants_mut()[0].function = unit.specs.loop_invariants()[1].function;
    assert!(!matches!(
        bad.validate().unwrap_err().kind(),
        VirValidationErrorKind::LoopInvariantFeatureGated(_)
    ));
}

#[test]
fn wrong_loop_scope_and_body_only_old_values_are_not_snapshots() {
    for source in [
        "fn main(){invariant true; return;}",
        "fn main(){while true {let x=0; invariant x==0; break;} return;}",
        "fn main(){while true {invariant x==0; let x=0; break;} return;}",
        "fn main(){for i in 0..2 {invariant old(i)<=i;} return;}",
        "fn main(){let p=alloc<u64>(1); while true {invariant old(p)==p; break;} free(p); return;}",
    ] {
        let out = analyze(&SourceFile::from_text("bad-loop.nera", source));
        assert!(out.vir().is_none());
        assert!(!out.issues().is_empty());
        assert!(!out.issues().iter().any(|i| i.diagnostic().message()
            == "loop invariant is outside the structured stable-resource induction profile"));
    }
}
