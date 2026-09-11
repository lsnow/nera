#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::verifier::provenance::{PROVENANCE_OBSERVATION_VERSION, ProvenanceIssue};
#[path = "support/preview_checks.rs"]
mod preview_checks;
use nera::verifier::relation::audit::RelationReplayCache;
use nera::*;

const SOURCE: &str = "fn main() -> u64 { let p = alloc<u64>(2); let x = &raw *p;
    let y = x + 8; let d = ptr_byte_distance(x,y); free(p);
    if d == 8usize { return 42; } return 0; }";

#[test]
fn pointer_events_link_complete_resource_obligations_and_numeric_queries() {
    frontend_checks::checked("provenance-audit.nera", SOURCE, 42);
    for source in [
        SOURCE,
        include_str!("../spec/cases/verify/provenance-flow.nera"),
        include_str!("../spec/cases/verify/provenance-instance.nera"),
        include_str!("../spec/cases/verify/native-address-model.nera"),
    ] {
        let output = frontend_checks::accepted("provenance-audit.nera", source);
        let program = output.vir().unwrap().resolve().unwrap();
        let config = CfgAnalysisConfig::default();
        let report = verify_program(&program, config).unwrap();
        assert!(report.is_memory_checked_core0());
        assert_eq!(report, verify_program(&program, config).unwrap());
        let cache = RelationReplayCache::new(&program, config).unwrap();
        let mut count = 0;
        for (&id, f) in report.functions() {
            let cfg = f.cfg();
            let events = cfg.provenance_evidence();
            assert!(cache.accepts_memory_trace(
                id,
                events,
                cfg.relation_queries(),
                cfg.relation_evidence()
            ));
            for e in events {
                count += 1;
                assert_eq!(e.version, PROVENANCE_OBSERVATION_VERSION);
                assert!(cache.accepts_provenance(e));
                let queries: Vec<_> = cfg
                    .relation_queries()
                    .iter()
                    .filter(|q| {
                        q.finding == e.finding
                            && q.case_ordinal == e.case_ordinal
                            && q.edge_ordinal.is_none()
                    })
                    .map(|q| q.query_ordinal)
                    .collect();
                assert_eq!(e.query_ordinals, queries);
                assert!(!e.sources.is_empty());
                for source in &e.sources {
                    assert_eq!(source.site().function(), id);
                    assert_eq!(
                        output
                            .vir()
                            .unwrap()
                            .as_unit()
                            .source_map
                            .source_span_for_origin(source.origin())
                            .unwrap(),
                        source.source_position()
                    );
                }
            }
            if !events.is_empty() {
                assert!(!cache.accepts_memory_trace(
                    id,
                    &events[1..],
                    cfg.relation_queries(),
                    cfg.relation_evidence()
                ));
            }
            if !cfg.relation_queries().is_empty() {
                assert!(!cache.accepts_memory_trace(
                    id,
                    events,
                    &cfg.relation_queries()[1..],
                    cfg.relation_evidence()
                ));
            }
        }
        assert!(count > 0 && count < 512);
    }
}

#[test]
fn source_instance_path_guard_obligation_and_query_mutations_are_rejected() {
    let output = frontend_checks::accepted("mutation.nera", SOURCE);
    let program = output.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let preview = nera::verification::verify_unit(output.vir().unwrap().as_unit().clone(), config);
    preview_checks::observe(&preview);
    let report = preview.verification().unwrap();
    let cfg = report.functions()[&VirFunctionId::new(0)].cfg();
    let original = cfg
        .provenance_evidence()
        .iter()
        .find(|e| matches!(e.instruction, VirInstruction::PointerDistance { .. }))
        .unwrap();
    let cache = RelationReplayCache::new(&program, config).unwrap();
    for mutation in 0..10 {
        let mut bad = original.clone();
        match mutation {
            0 => bad.sources.clear(),
            1 => bad.finding = cfg.provenance_evidence()[0].finding,
            2 => bad.case_ordinal += 1,
            3 => bad.guard = PathCondition::unreachable(),
            4 => {
                bad.pointers[0].before = bad.pointers[0]
                    .before
                    .map(|p| p.with_paths(VirPointerPaths::default()))
            }
            5 => bad.instances[0].before.as_mut().unwrap().liveness = LivenessState::Dead,
            6 => {
                bad.obligations.pop().unwrap();
            }
            7 => {
                bad.query_ordinals.push(usize::MAX);
            }
            8 => bad.version += 1,
            _ => bad.config.max_block_visits += 1,
        }
        assert_ne!(bad, *original);
        assert!(!cache.accepts_provenance(&bad), "mutation {mutation}");
    }
    let query = cfg
        .relation_queries()
        .iter()
        .find(|q| q.finding == original.finding)
        .unwrap();
    let mut bad_query = query.clone();
    bad_query.query.kernel_version += 1;
    assert!(!cache.accepts_query(&bad_query));
    preview_checks::observe(&preview);
}

#[test]
fn free_and_opaque_owner_calls_invalidate_old_live_proposals() {
    for release in ["free(p);", "consume(p);"] {
        let source = format!(
            "fn main() -> u64 {{ let p=alloc<u64>(1); *p=42; let x=&raw *p;
            let before=x==x; {release} let after=x==x; return 0; }}
            fn consume(p: Own<u64>) {{ free(p); return; }}"
        );
        let output = frontend_checks::accepted("old-instance.nera", &source);
        let program = output.vir().unwrap().resolve().unwrap();
        let report = verify_program(&program, CfgAnalysisConfig::default()).unwrap();
        assert!(!report.is_memory_checked_core0());
        let cfg = report.functions()[&VirFunctionId::new(0)].cfg();
        let comparisons: Vec<_> = cfg
            .provenance_evidence()
            .iter()
            .filter(|e| matches!(e.instruction, VirInstruction::PointerCompare { .. }))
            .collect();
        assert_eq!(
            comparisons.len(),
            2,
            "{release}: {:?}",
            cfg.provenance_evidence()
                .iter()
                .map(|e| &e.instruction)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            comparisons[0].instances[0].before.unwrap().liveness,
            LivenessState::Live
        );
        assert_ne!(
            comparisons[1].instances[0].before.unwrap().liveness,
            LivenessState::Live
        );
        let cache = RelationReplayCache::new(&program, CfgAnalysisConfig::default()).unwrap();
        let mut stale = comparisons[1].clone();
        stale.instances = comparisons[0].instances.clone();
        assert!(!cache.accepts_provenance(&stale));
        assert!(
            cfg.provenance_evidence()
                .iter()
                .any(|e| e.instances.iter().any(|i| i
                    .before
                    .is_some_and(|i| i.liveness == LivenessState::Live)
                    && i.after.is_some_and(|i| i.liveness != LivenessState::Live)))
        );
        assert!(report.diagnostics().iter().any(|d| {
            d.provenance_notes()
                .iter()
                .any(|n| n.issue == ProvenanceIssue::InactiveInstance && !n.sources.is_empty())
        }));
    }
}

#[test]
fn provenance_diagnostics_distinguish_boundary_authority_and_initialization() {
    for (body, issue) in [
        (
            "let p=alloc<u64>(1); let q=alloc<u64>(1); let x=&raw *p; let y=&raw *q; let same=x==y; free(p); free(q);",
            ProvenanceIssue::DifferentInstances,
        ),
        (
            "let p=alloc<u64>(1); let x=p+8; let n=*x; free(p);",
            ProvenanceIssue::OnePastAccess,
        ),
        (
            "let p=alloc<u64>(1); let n=*p; free(p);",
            ProvenanceIssue::MissingInitialization,
        ),
    ] {
        let source = format!("fn main() -> u64 {{ {body} return 0; }}");
        let output = frontend_checks::accepted("diagnostic.nera", &source);
        let program = output.vir().unwrap().resolve().unwrap();
        let report = verify_program(&program, CfgAnalysisConfig::default()).unwrap();
        assert!(!report.is_memory_checked_core0());
        assert!(
            report
                .diagnostics()
                .iter()
                .any(|d| d.provenance_notes().iter().any(|n| n.issue == issue)),
            "{issue:?}: {:?}",
            report.diagnostics()
        );
    }
}

#[test]
fn evidence_budget_fails_closed_without_disabling_numeric_fast_paths() {
    let output = frontend_checks::accepted("budget.nera", SOURCE);
    let program = output.vir().unwrap().resolve().unwrap();
    let mut config = CfgAnalysisConfig {
        max_relation_evidence: 1,
        ..CfgAnalysisConfig::default()
    };
    let error = verify_program(&program, config).unwrap_err();
    assert!(error.to_string().contains("evidence budget"));
    config.max_relation_evidence = CfgAnalysisConfig::default().max_relation_evidence;
    config.relation_limits.max_steps = 0;
    assert!(
        verify_program(&program, config)
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn changed_memory_effects_and_missing_numeric_witnesses_require_fresh_replay() {
    let output = frontend_checks::accepted("effect.nera", SOURCE);
    let program = output.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let report = verify_program(&program, config).unwrap();
    let cfg = report.functions()[&VirFunctionId::new(0)].cfg();
    let old = cfg
        .provenance_evidence()
        .iter()
        .find(|e| matches!(e.instruction, VirInstruction::PointerDistance { .. }))
        .unwrap();
    let mut changed = output.vir().unwrap().as_unit().clone();
    let delta = changed.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .find_map(|i| match &mut i.instruction {
            VirInstruction::Constant {
                value: value @ VirConstant::U64(8),
                ..
            } => Some(value),
            _ => None,
        })
        .unwrap();
    *delta = VirConstant::U64(0);
    let changed = changed.into_validated().unwrap();
    let changed = changed.resolve().unwrap();
    let cache = RelationReplayCache::new(&changed, config).unwrap();
    assert!(!cache.accepts_provenance(old));
    assert!(!cache.accepts_memory_trace(
        VirFunctionId::new(0),
        cfg.provenance_evidence(),
        cfg.relation_queries(),
        cfg.relation_evidence()
    ));

    let cache = RelationReplayCache::new(&program, config).unwrap();
    let mut queries = cfg.relation_queries().to_vec();
    let witness = queries
        .iter_mut()
        .find_map(|q| match &mut q.query.witness {
            nera::verifier::relation::audit::QueryWitness::Bounds(bounds) if !bounds.is_empty() => {
                Some(bounds)
            }
            _ => None,
        })
        .unwrap();
    witness.clear();
    assert!(!cache.accepts_memory_trace(
        VirFunctionId::new(0),
        cfg.provenance_evidence(),
        &queries,
        cfg.relation_evidence()
    ));
}

#[test]
fn path_budget_loss_is_observed_without_becoming_authority() {
    let mut value = "42".to_owned();
    for _ in 0..10 {
        value = format!("[{value}]");
    }
    let source = format!(
        "fn main() -> u64 {{ let a={value}; let x=&raw a{};
        let same=x==x; return 0; }}",
        "[0]".repeat(10)
    );
    let output = frontend_checks::accepted("path-limit.nera", &source);
    let program = output.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let report = verify_program(&program, config).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(report.diagnostics().iter().any(|d| {
        d.provenance_notes()
            .iter()
            .any(|n| n.issue == ProvenanceIssue::MissingDomainPath)
    }));
    let cache = RelationReplayCache::new(&program, config).unwrap();
    let cfg = report.functions()[&VirFunctionId::new(0)].cfg();
    let mut trace = cfg.provenance_evidence().to_vec();
    trace.retain(|e| {
        !e.obligations
            .iter()
            .any(|o| o.status() == ObligationStatus::Unknown)
    });
    assert!(!cache.accepts_memory_trace(
        VirFunctionId::new(0),
        &trace,
        cfg.relation_queries(),
        cfg.relation_evidence()
    ));
}
