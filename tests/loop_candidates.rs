use nera::*;

fn frontend(source: &str) -> FrontendOutput {
    let out = analyze(&SourceFile::from_text("candidates.nera", source));
    assert_eq!(
        out.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        out.issues()
    );
    out
}

fn without_invariants(source: &str) -> String {
    source
        .lines()
        .filter(|l| !l.trim_start().starts_with("invariant "))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn existing_targets_without_annotations_are_checked() {
    for source in [
        include_str!("../spec/cases/verify/loop-scalar-target.nera"),
        include_str!("../spec/cases/verify/loop-initialize-target.nera"),
        include_str!("../spec/cases/verify/loop-update-target.nera"),
    ] {
        let source = without_invariants(source);
        let out = frontend(&source);
        let unit = out.vir().unwrap();
        assert!(
            !unit.as_unit().specs.loop_invariants().is_empty(),
            "{source}"
        );
        let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
        assert!(
            report.is_memory_checked_core0(),
            "{source}\n{:?}\nattempts: {:?}",
            report.diagnostics(),
            report
                .functions()
                .values()
                .map(|f| f.cfg().loop_candidate_attempts())
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn candidates_do_not_hide_real_errors_or_explicit_failures() {
    for source in [
        "fn main()->u64 {let p=alloc<[u64;4]>(1); for i in 0usize..4usize {if i==2usize {continue;} p[i]=42;} let x=p[2]; free(p); return x;}",
        "fn main()->u64 {let p=alloc<[u64;4]>(1); for i in 0usize..4usize {let x=p[i]; p[i]=x;} free(p); return 0;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant i==0; i=i+1;} return i;}",
        "fn main()->u64 {let p=alloc<[u64;4]>(1); for i in 0usize..0usize {p[i]=42;} let x=p[0]; free(p); return x;}",
    ] {
        let out = frontend(source);
        let report =
            verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default()).unwrap();
        assert!(!report.is_memory_checked_core0(), "{source}");
    }
}

#[test]
fn failed_prefix_is_eliminated_and_scalar_candidate_is_rechecked() {
    let source = "fn main()->u64 {let p=alloc<[u64;4]>(1); let mut i=0usize;
        while i<4usize {if i!=2usize {p[i]=42;} i=i+1usize;}
        assert i==4usize; if i!=4usize {free(p); return 99;} free(p); return 42;}";
    let out = frontend(source);
    // Exercise invariant elimination independently of the newer disjunctive
    // partition engine, which can prove this safe program without candidates.
    let config = CfgAnalysisConfig {
        max_loop_partition_cuts: 0,
        ..Default::default()
    };
    let report = verify_program(&out.vir().unwrap().resolve().unwrap(), config).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let attempts = report.functions()[&VirFunctionId::new(0)]
        .cfg()
        .loop_candidate_attempts();
    assert!(attempts.len() >= 2, "{attempts:?}");
    assert!(attempts[0].rejected.iter().any(|o| matches!(
        o.obligation().kind(),
        ResourceObligationKind::LoopInvariantEstablished {
            back_edge: true,
            ..
        }
    )));
    assert!(attempts.last().unwrap().selected.len() < attempts[0].selected.len());
    assert!(attempts.last().unwrap().rejected.is_empty());
    let preview = nera::verification::verify_source(
        &SourceFile::from_text("candidate-elimination.nera", source),
        config,
    );
    let text =
        nera::verification::render_text(&preview, nera::verification::TextReportMode::Explain);
    assert!(text.contains("discarded-candidate-attempt/not-additional"));
}

#[test]
fn candidate_budgets_only_remove_precision_and_explicit_checks_remain() {
    let source = without_invariants(include_str!(
        "../spec/cases/verify/loop-initialize-target.nera"
    ));
    let out = frontend(&source);
    let unit = out.vir().unwrap().resolve().unwrap();
    assert!(
        verify_program(&unit, Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    for config in [
        CfgAnalysisConfig {
            max_loop_candidates: 0,
            ..Default::default()
        },
        CfgAnalysisConfig {
            max_loop_candidates: 1,
            ..Default::default()
        },
        CfgAnalysisConfig {
            max_loop_candidate_rounds: 0,
            ..Default::default()
        },
        CfgAnalysisConfig {
            max_loop_candidate_block_visits: 1,
            ..Default::default()
        },
    ] {
        let report = verify_program(&unit, config).unwrap();
        assert!(!report.is_memory_checked_core0(), "{config:?}");
        for function in report.functions().values() {
            assert!(
                function
                    .cfg()
                    .loop_candidate_attempts()
                    .iter()
                    .map(|a| a.block_visits)
                    .sum::<u64>()
                    <= config.max_loop_candidate_block_visits
            );
        }
    }
    let explicit =
        frontend("fn main()->u64 {let mut i=0; while i<3 {invariant i==0; i=i+1;} return i;}");
    assert!(
        !verify_program(
            &explicit.vir().unwrap().resolve().unwrap(),
            CfgAnalysisConfig {
                max_loop_candidates: 0,
                max_loop_candidate_rounds: 0,
                ..Default::default()
            }
        )
        .unwrap()
        .is_memory_checked_core0()
    );
}

#[test]
fn deterministic_discovery_and_audit_bind_candidates_and_budget() {
    use nera::verifier::{relation::audit::RelationReplayCache, summary::audit::SummaryAudit};
    let source = without_invariants(include_str!(
        "../spec/cases/verify/loop-initialize-target.nera"
    ));
    let out = frontend(&source);
    let unit = out.vir().unwrap();
    assert_eq!(
        unit.stable_dump(),
        frontend(&source).vir().unwrap().stable_dump()
    );
    let resolved = unit.resolve().unwrap();
    let report = verify_program(&resolved, Default::default()).unwrap();
    assert!(report.is_memory_checked_core0());
    let audit = SummaryAudit::from_report(&report);
    let cache = RelationReplayCache::new(&resolved, Default::default()).unwrap();
    assert!(cache.accepts_summary_audit(&audit));
    let mut reordered = unit.as_unit().clone();
    reordered.specs.loop_invariants_mut().reverse();
    let owners: Vec<_> = reordered
        .specs
        .loop_invariants_mut()
        .iter_mut()
        .enumerate()
        .map(|(index, i)| {
            i.id = VirSpecLoopInvariantId::new(index as u32);
            (i.clause, i.id)
        })
        .collect();
    for (clause, id) in owners {
        reordered.specs.clauses_mut()[clause.get() as usize].owner =
            VirSpecClauseOwner::LoopInvariant(id);
    }
    let reordered = reordered.into_validated().unwrap();
    assert!(
        verify_program(&reordered.resolve().unwrap(), Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    let reordered_resolved = reordered.resolve().unwrap();
    let reordered_cache =
        RelationReplayCache::new(&reordered_resolved, Default::default()).unwrap();
    assert!(!reordered_cache.accepts_summary_audit(&audit));
    let disabled = RelationReplayCache::new(
        &resolved,
        CfgAnalysisConfig {
            max_loop_candidate_rounds: 0,
            ..Default::default()
        },
    )
    .unwrap();
    assert!(!disabled.accepts_summary_audit(&audit));
    let changed = frontend(&format!("// unrelated comment\n{source}"));
    assert!(
        verify_program(
            &changed.vir().unwrap().resolve().unwrap(),
            Default::default()
        )
        .unwrap()
        .is_memory_checked_core0()
    );
    let mut raw = unit.as_unit().clone();
    // Type-derived resource assumptions cannot be substituted for candidates.
    let c = raw
        .specs
        .clauses_mut()
        .iter_mut()
        .find(|c| matches!(c.origin, VirSpecClauseOrigin::InferredLoop { .. }))
        .unwrap();
    c.origin = VirSpecClauseOrigin::InferredType {
        origin: c.origin.origin(),
    };
    assert!(raw.validate().is_err());
    let mut wrong_owner = unit.as_unit().clone();
    let contract_clause = wrong_owner
        .specs
        .clauses_mut()
        .iter_mut()
        .find(|c| matches!(c.owner, VirSpecClauseOwner::Contract { .. }))
        .unwrap();
    contract_clause.origin = VirSpecClauseOrigin::InferredLoop {
        origin: contract_clause.origin.origin(),
    };
    assert!(wrong_owner.validate().is_err());
    let mut old = unit.as_unit().clone();
    old.version = VirUnitVersion::V26;
    assert!(old.validate().is_err());
}

#[test]
fn discovery_is_erased_and_nested_loops_use_independent_interfaces() {
    let original = include_str!("../spec/cases/verify/loop-initialize-target.nera");
    let erased = original
        .split_inclusive('\n')
        .map(|line| {
            if line.trim_start().starts_with("invariant ") {
                line.chars()
                    .map(|c| if c == '\n' { '\n' } else { ' ' })
                    .collect::<String>()
            } else {
                line.to_owned()
            }
        })
        .collect::<String>();
    assert_eq!(
        frontend(original).vir().unwrap().runtime().stable_dump(),
        frontend(&erased).vir().unwrap().runtime().stable_dump()
    );
    let out = frontend(
        "fn main()->u64 {let mut i=0; while i<3 {
        let mut j=0; while j<4 {j=j+1;} if j!=4 {return 99;} i=i+1;
    } assert i==3; return i;}",
    );
    assert_eq!(
        out.vir().unwrap().as_unit().specs.loop_invariants().len(),
        2
    );
    assert!(
        verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn unsupported_discovery_and_safe_zero_iterations_use_original_analysis() {
    for source in [
        "fn main()->u64 {let mut i=5; while i<3 {i=i+1;} return i;}",
        "fn main()->u64 {let mut i=0; while i<3 {i=step(i);} return 42;} fn step(i:u64)->u64 {return i+1;}",
    ] {
        let out = frontend(source);
        let report =
            verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default()).unwrap();
        assert!(
            report.is_memory_checked_core0(),
            "{:?}",
            report.diagnostics()
        );
        assert!(
            report
                .functions()
                .values()
                .all(|f| f.cfg().loop_candidate_attempts().is_empty())
        );
    }
}

#[test]
fn discovery_limit_retains_independent_regions_without_skipping_uncovered_code() {
    let source = format!(
        "fn main()->u64 {{{} return 42;}}",
        "for i in 0..3 {}".repeat(17)
    );
    let out = frontend(&source);
    // The first sixteen disjoint regions are complete interfaces. The last
    // loop is still analyzed normally, not skipped or assumed safe.
    assert_eq!(
        out.vir().unwrap().as_unit().specs.loop_invariants().len(),
        16
    );
    assert!(
        verify_program(&out.vir().unwrap().resolve().unwrap(), Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    let bad = frontend(&source.replace(
        "return 42;",
        "let p=alloc<u64>(1); let value=*p; free(p); return value;",
    ));
    assert!(
        !verify_program(&bad.vir().unwrap().resolve().unwrap(), Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
}
