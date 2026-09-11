#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::verifier::relation::{RELATION_KERNEL_VERSION, audit::*, difference::*};
#[path = "support/preview_checks.rs"]
mod preview_checks;
use nera::{CfgAnalysisConfig, ObligationStatus, verify_program};

const CORPUS: &[(&str, &str)] = &[
    (
        "baseline",
        include_str!("../spec/cases/verify/relation-baseline.nera"),
    ),
    (
        "siblings",
        include_str!("../spec/cases/verify/sibling-slices.nera"),
    ),
    (
        "strided",
        include_str!("../spec/cases/verify/strided-regions.nera"),
    ),
    (
        "composition",
        include_str!("../spec/cases/verify/relation-composition.nera"),
    ),
];

#[test]
fn fixed_corpus_has_deterministic_queries_and_complete_replay() {
    for &(name, source) in CORPUS {
        let started = std::time::Instant::now();
        let output = frontend_checks::accepted("relation-audit.nera", source);
        let program = output.vir().unwrap().resolve().unwrap();
        let config = CfgAnalysisConfig::default();
        let verified = verify_program(&program, config).unwrap();
        let elapsed = started.elapsed();
        assert!(verified.is_memory_checked_core0(), "{name}");
        let replay = RelationReplayCache::new(&program, config).unwrap();
        let mut queries = 0;
        let mut visits = 0;
        let mut retained_cases = 0;
        for (&id, function) in verified.functions() {
            let trace = function.cfg().relation_queries();
            queries += trace.len();
            visits += function.cfg().block_visits();
            retained_cases += function
                .cfg()
                .blocks()
                .values()
                .map(|block| {
                    block.entry_conditional_state().cases().len()
                        + block
                            .instruction_conditional_states()
                            .iter()
                            .map(|s| s.cases().len())
                            .sum::<usize>()
                })
                .sum::<usize>();
            assert!(replay.accepts_trace(id, trace));
            for record in trace {
                assert_eq!(record.query.kernel_version, RELATION_KERNEL_VERSION);
                assert!(replay.accepts_query(record));
                assert_eq!(record.config, config);
            }
            if !trace.is_empty() {
                assert!(!replay.accepts_trace(id, &trace[1..]));
            }
        }
        assert!(queries > 0);
        assert!(
            queries <= 2048 && visits <= 64,
            "fixed corpus complexity envelope: {name}"
        );
        eprintln!(
            "relation-audit corpus={name} elapsed_us={} block_visits={visits} retained_cases={retained_cases} queries={queries}",
            elapsed.as_micros()
        );
    }
}

#[test]
fn witness_premise_origin_case_and_config_mutations_never_hit_the_cache() {
    let output = frontend_checks::accepted("relation-audit.nera", CORPUS[3].1);
    let program = output.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let preview = nera::verification::verify_unit(output.vir().unwrap().as_unit().clone(), config);
    preview_checks::observe(&preview);
    let verified = preview.verification().unwrap();
    let cache = RelationReplayCache::new(&program, config).unwrap();
    let records: Vec<_> = verified
        .functions()
        .values()
        .flat_map(|f| f.cfg().relation_queries())
        .collect();
    let original = (*records
        .iter()
        .find(|e| !e.query.relations.is_empty() && !e.sources.is_empty())
        .unwrap())
    .clone();
    let mut mutations = Vec::new();
    let mut changed = original.clone();
    changed.query.theory = "unreviewed-solver";
    mutations.push(changed);
    let mut changed = original.clone();
    changed.query.status = if original.query.status == ObligationStatus::Proven {
        ObligationStatus::Unknown
    } else {
        ObligationStatus::Proven
    };
    mutations.push(changed);
    let mut changed = original.clone();
    changed.query.guard = records
        .iter()
        .find(|q| q.query.guard != original.query.guard)
        .unwrap()
        .query
        .guard
        .clone();
    mutations.push(changed);
    let mut changed = original.clone();
    changed.query.relations.clear();
    mutations.push(changed);
    let mut changed = original.clone();
    changed.sources.clear();
    mutations.push(changed);
    let mut changed = original.clone();
    changed.query.kernel_version += 1;
    mutations.push(changed);
    let mut changed = original.clone();
    changed.case_ordinal = usize::MAX;
    mutations.push(changed);
    let mut changed = original.clone();
    changed.edge_ordinal = Some(255);
    mutations.push(changed);
    let mut changed = original.clone();
    changed.query_ordinal = usize::MAX;
    mutations.push(changed);
    let mut changed = original.clone();
    changed.config.max_block_visits += 1;
    mutations.push(changed);
    let mut changed = original.clone();
    changed.query.witness = QueryWitness::Bounds(Vec::new());
    mutations.push(changed);
    let mut changed = original.clone();
    changed.finding = records
        .iter()
        .find(|e| e.finding.site().function() != original.finding.site().function())
        .unwrap()
        .finding;
    mutations.push(changed);
    for changed in mutations {
        assert_ne!(changed, original);
        assert!(!cache.accepts_query(&changed));
    }
    preview_checks::observe(&preview);
}

#[test]
fn edge_prefixes_loan_pairs_and_accesses_are_audited() {
    let output = frontend_checks::accepted("relation-audit.nera", CORPUS[3].1);
    let program = output.vir().unwrap().resolve().unwrap();
    let verified = verify_program(&program, CfgAnalysisConfig::default()).unwrap();
    let records: Vec<_> = verified
        .functions()
        .values()
        .flat_map(|f| f.cfg().relation_queries())
        .collect();
    assert!(
        records
            .iter()
            .any(|e| e.edge_ordinal.is_some() && matches!(e.query.goal, QueryGoal::Ordered(..)))
    );
    assert!(
        records
            .iter()
            .any(|e| matches!(e.query.goal, QueryGoal::Contained(..)))
    );
    assert!(
        records
            .iter()
            .any(|e| matches!(e.query.goal, QueryGoal::CoversAccess(..)))
    );
    let output = frontend_checks::accepted("relation-audit.nera", CORPUS[1].1);
    let program = output.vir().unwrap().resolve().unwrap();
    let verified = verify_program(&program, CfgAnalysisConfig::default()).unwrap();
    assert!(
        verified
            .functions()
            .values()
            .flat_map(|f| f.cfg().relation_queries())
            .any(|e| matches!(e.query.goal, QueryGoal::Disjoint(..)))
    );
}

#[test]
fn evidence_overflow_fails_analysis_instead_of_publishing_partial_success() {
    let output = frontend_checks::accepted("relation-audit.nera", CORPUS[1].1);
    let program = output.vir().unwrap().resolve().unwrap();
    let result = verify_program(
        &program,
        CfgAnalysisConfig {
            max_relation_evidence: 0,
            ..Default::default()
        },
    );
    assert!(matches!(
        result,
        Err(nera::VerificationError::Cfg {
            error: nera::CfgAnalysisError::RelationEvidenceBudgetExceeded { .. },
            ..
        })
    ));
}

#[test]
fn relation_budget_does_not_break_existing_interval_fast_paths() {
    let source = "fn main()->u64 { let a=[42,0]; return a[0]; }";
    frontend_checks::checked("relation-audit.nera", source, 42);
    let output = frontend_checks::accepted("relation-audit.nera", source);
    let program = output.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig {
        relation_limits: DifferenceLimits {
            max_variables: 0,
            max_constraints: 0,
            max_steps: 0,
            max_derivations: 0,
            max_branches: 0,
        },
        ..Default::default()
    };
    assert!(
        verify_program(&program, config)
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn failed_range_diagnostics_retain_query_outcomes_and_sources() {
    let source = "fn main()->u64 { return get(1usize); } fn get(i:usize)->u64 { let a=[42,0]; return a[i]; }";
    let output = frontend_checks::accepted("relation-audit.nera", source);
    let program = output.vir().unwrap().resolve().unwrap();
    let verified = verify_program(&program, CfgAnalysisConfig::default()).unwrap();
    assert!(!verified.is_memory_checked_core0());
    let diagnostic = verified
        .diagnostics()
        .iter()
        .find(|d| {
            d.relation_queries()
                .iter()
                .any(|q| q.query.outcome == QueryOutcome::MissingRelation)
        })
        .unwrap();
    assert!(
        diagnostic
            .message()
            .contains("insufficient range relations")
    );
    assert!(
        diagnostic
            .relation_queries()
            .iter()
            .all(|q| q.finding == diagnostic.finding())
    );
    assert!(
        diagnostic
            .relation_queries()
            .iter()
            .any(|q| q.query.status == ObligationStatus::Unknown)
    );
}
