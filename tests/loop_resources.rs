use nera::*;

fn inspect(source: &str) -> (FrontendOutput, ProgramVerification) {
    let output = analyze(&SourceFile::from_text("loop-resources.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{source}: {:?}",
        output.issues()
    );
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .unwrap();
    (output, report)
}

const INITIALIZE: &str = include_str!("../spec/cases/verify/loop-initialize-target.nera");
const UPDATE: &str = include_str!("../spec/cases/verify/loop-update-target.nera");

#[test]
fn dynamic_initialization_and_update_close_without_unrolling_or_trust() {
    for source in [INITIALIZE, UPDATE] {
        for n in [0, 1, 6, 8] {
            let source = source.replacen("6usize", &format!("{n}usize"), 1);
            let (output, report) = inspect(&source);
            assert!(
                report.is_memory_checked_core0(),
                "{source}: {:?}",
                report.diagnostics()
            );
            assert!(
                output
                    .vir()
                    .unwrap()
                    .as_unit()
                    .specs
                    .trust_entries()
                    .is_empty()
            );
            assert_eq!(
                interpret(output.vir().unwrap().resolve().unwrap().runtime())
                    .unwrap()
                    .values(),
                [VirRuntimeValue::U64(if n == 0 { 0 } else { 42 })]
            );
            assert!(
                report.functions()[&VirFunctionId::new(1)]
                    .cfg()
                    .obligations()
                    .iter()
                    .any(|o| matches!(
                        o.obligation().kind(),
                        ResourceObligationKind::LoopResourcesPreserved { .. }
                    ) && o.obligation().is_proven())
            );
        }
    }
}

#[test]
fn nonzero_prefix_and_boolean_elements_are_typed_induction_facts() {
    for (element, value) in [("u64", "42"), ("bool", "true")] {
        let source = format!(
            "fn main(){{fill(6usize); return;}}
            fn fill(end:usize) requires end<=8usize; {{
                if end<2usize {{return;}}
                let p=alloc<[{element};8]>(1); let mut i=2usize;
                while i<end {{invariant 2usize<=i; invariant i<=end;
                    invariant initialized(p,2usize..i); invariant writable(p,i..end);
                    p[i]={value}; i=i+1usize;
                }} free(p); return;
            }}"
        );
        let (_, report) = inspect(&source);
        assert!(
            report.is_memory_checked_core0(),
            "{source}: {:?}",
            report.diagnostics()
        );
    }
}

#[test]
fn complex_dynamic_origin_loses_precision_without_relaxing_the_budget() {
    let (_, report) = inspect(
        "fn main(){fill(2usize,6usize); return;}
        fn fill(begin:usize,end:usize) {
            if begin>end {return;} if end>8usize {return;}
            let p=alloc<[u64;8]>(1); let mut i=begin;
            while i<end {invariant begin<=i; invariant i<=end;
                invariant initialized(p,begin..i); invariant writable(p,i..end);
                if i<begin {break;} p[i]=42; i=i+1usize;
            } free(p); return;
        }",
    );
    assert!(!report.is_memory_checked_core0());
}

#[test]
fn writable_remaining_range_and_readable_prefix_share_one_interface() {
    let source = INITIALIZE.replace("invariant initialized(p, 0usize..i);",
        "invariant initialized(p, 0usize..i);\n        invariant readable(p, 0usize..i);\n        invariant writable(p, i..n);");
    let (_, report) = inspect(&source);
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    for extra in [
        "invariant writable(p, 0usize..n);",
        "invariant writable(p, i..n);",
    ] {
        let (_, report) = inspect(&source.replace("p[i] = 42;", &format!("{extra}\n p[i] = 42;")));
        assert!(
            !report.is_memory_checked_core0(),
            "duplicate exclusive use: {extra}"
        );
        assert!(
            report.functions()[&VirFunctionId::new(1)]
                .cfg()
                .obligations()
                .iter()
                .any(|o| matches!(
                    o.obligation().kind(),
                    ResourceObligationKind::LoopInvariantEstablished { .. }
                ) && !o.obligation().is_proven())
        );
    }
}

#[test]
fn missing_writes_wrong_entry_and_each_backedge_block_publication() {
    for source in [
        INITIALIZE.replace("p[i] = 42;", ""),
        INITIALIZE.replace("let mut i = 0usize;", "let mut i = 1usize;"),
        INITIALIZE.replace("i = i + 1usize;", "i = i + 2usize;"),
        INITIALIZE.replace(
            "p[i] = 42;",
            "if i == 0usize { i = i + 1usize; continue; } p[i] = 42;",
        ),
        INITIALIZE.replace("p[i] = 42;", "let before = p[i]; p[i] = 42;"),
        INITIALIZE.replace("invariant initialized(p, 0usize..i);", ""),
    ] {
        let (_, report) = inspect(&source);
        assert!(!report.is_memory_checked_core0(), "{source}");
        assert!(
            report.functions()[&VirFunctionId::new(0)]
                .cfg()
                .obligations()
                .iter()
                .any(|o| matches!(
                    o.obligation().kind(),
                    ResourceObligationKind::CallContractAvailable { .. }
                ) && !o.obligation().is_proven())
        );
    }
}

#[test]
fn frame_keeps_untouched_allocations_but_forgets_modified_contents() {
    let source = "fn main()->u64 {
        let p=alloc<u64>(1); *p=0;
        let q=alloc<u64>(1); *q=7;
        let mut i=0;
        while i<3 { invariant i<=3; assert *q==7; *p=i; i=i+1; }
        free(p); free(q); return 0;
    }";
    // Heap reads are runtime observations; bind them before a logical assert.
    let source = source.replace("assert *q==7;", "let value=*q; assert value==7;");
    let (_, report) = inspect(&source);
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let bad = source.replace(
        "let value=*q; assert value==7;",
        "let value=*p; assert value==0;",
    );
    let (_, report) = inspect(&bad);
    assert!(
        !report.is_memory_checked_core0(),
        "first-iteration scalar contents leaked into induction"
    );
}

#[test]
fn fresh_allocation_direct_or_through_calls_remains_explicitly_gated() {
    for source in [
        "fn main(){let p=alloc<u64>(1); let mut i=0; while i<3 {invariant i<=3; let q=alloc<u64>(1); free(q); i=i+1;} free(p); return;}",
        "fn main(){let mut i=0; while i<3 {invariant i<=3; call(); i=i+1;} return;} fn call(){let p=alloc<u64>(1); free(p); return;}",
    ] {
        let output = analyze(&SourceFile::from_text("gated-loop.nera", source));
        assert_eq!(
            output.status(),
            FrontendStatus::Unsupported,
            "{source}: {:?}",
            output.issues()
        );
        assert!(output.vir().is_none());
    }
}

#[test]
fn stable_borrow_is_carried_without_resetting_loan_authority() {
    let source = "fn main()->u64 {let mut x=7; let r=&x; let mut i=0; while i<3 {
        invariant i<=3; invariant readable(r, 0usize..1usize);
        let value=*r; assert value==7; i=i+1;
    } return *r;}";
    let (_, report) = inspect(source);
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let bad = source.replace(
        "invariant readable(r, 0usize..1usize);",
        "invariant writable(r, 0usize..1usize);",
    );
    let (_, report) = inspect(&bad);
    assert!(!report.is_memory_checked_core0());
}

#[test]
fn raw_backedge_cannot_swap_owner_permissions_or_forge_resource_snapshots() {
    let source = "fn main(){let p=alloc<u64>(1); let q=alloc<u64>(1); *p=0; *q=7;
        let mut i=0; while i<3 {invariant i<=3; invariant alive(p.region); *p=i; i=i+1;}
        free(p); free(q); return;}";
    let (output, report) = inspect(source);
    assert!(report.is_memory_checked_core0());
    let mut unit = output.vir().unwrap().as_unit().clone();
    let boundary = unit.specs.loop_invariants()[0].boundary.clone().unwrap();
    let f = &mut unit.runtime.functions[0];
    let header = f.blocks.iter().find(|b| b.id == boundary.header).unwrap();
    let slots: Vec<_> = header
        .parameters
        .iter()
        .enumerate()
        .filter(|(_, p)| p.ty == VirType::Permission)
        .map(|(i, _)| i)
        .collect();
    assert_eq!(slots.len(), 2);
    for b in &mut f.blocks {
        if boundary.blocks.contains(&b.id)
            && let VirTerminator::Jump { target } = &mut b.terminator.terminator
            && target.block == boundary.header
        {
            target.arguments.swap(slots[0], slots[1]);
        }
    }
    let unit = unit.into_validated().unwrap();
    let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report.functions()[&VirFunctionId::new(0)]
            .cfg()
            .obligations()
            .iter()
            .any(|o| matches!(
                o.obligation().kind(),
                ResourceObligationKind::LoopResourcesPreserved { .. }
            ) && !o.obligation().is_proven())
    );
    let mut unit = output.vir().unwrap().as_unit().clone();
    let assertion = unit
        .specs
        .assertions_mut()
        .iter_mut()
        .find(|a| matches!(a.kind, SpecAssertionKind::Alive(_)))
        .unwrap();
    assertion.kind = SpecAssertionKind::Alive(VirSpecSnapshot::Value {
        function: VirFunctionId::new(99),
        value: VirValueId::new(0),
    });
    assert!(unit.validate().is_err());
}

#[test]
fn resource_obligations_are_replayed_and_cannot_be_omitted_from_summary_audit() {
    use nera::verifier::{relation::audit::RelationReplayCache, summary::audit::SummaryAudit};
    let (output, report) = inspect(INITIALIZE);
    assert!(report.is_memory_checked_core0());
    let resolved = output.vir().unwrap().resolve().unwrap();
    let cache = RelationReplayCache::new(&resolved, Default::default()).unwrap();
    let audit = SummaryAudit::from_report(&report);
    assert!(cache.accepts_summary_audit(&audit));
    let mut bad = audit.clone();
    let f = bad
        .functions
        .iter_mut()
        .find(|f| f.function == VirFunctionId::new(1))
        .unwrap();
    let obligation = report.functions()[&VirFunctionId::new(1)]
        .cfg()
        .obligations()
        .iter()
        .position(|o| {
            matches!(
                o.obligation().kind(),
                ResourceObligationKind::LoopResourcesPreserved { .. }
            )
        })
        .unwrap();
    let index = f
        .requirements
        .iter()
        .position(|(item, _)| {
            item.kind == nera::verifier::summary::EvidenceKind::Cfg && item.index == obligation
        })
        .unwrap();
    f.requirements.remove(index);
    assert!(!cache.accepts_summary_audit(&bad));
}
