#[path = "support/frontend_checks.rs"]
mod frontend_checks;
#[path = "../src/bin/fuzz_support/provenance_cases.rs"]
mod provenance_cases;

use nera::verifier::relation::{audit::RelationReplayCache, difference::DifferenceLimits};
use nera::{CfgAnalysisConfig, VirFunctionId, VirRuntimeValue, interpret, verify_program};

#[test]
fn provenance_families_pin_verdicts_before_execution_and_replay_all_observations() {
    for ordinal in 0..provenance_cases::FAMILY_COUNT {
        for entropy in [0, 1, 7] {
            let source = provenance_cases::source(ordinal, entropy);
            let output = frontend_checks::accepted("provenance-acceptance.nera", &source);
            let program = output.vir().unwrap().resolve().unwrap();
            let config = CfgAnalysisConfig::default();
            let report = verify_program(&program, config).unwrap();
            assert_eq!(
                report.is_memory_checked_core0(),
                provenance_cases::expected_checked(ordinal),
                "family {ordinal}, entropy {entropy}: {:?}",
                report.diagnostics()
            );
            assert_eq!(report, verify_program(&program, config).unwrap());
            let cache = RelationReplayCache::new(&program, config).unwrap();
            for (&id, f) in report.functions() {
                let cfg = f.cfg();
                assert!(cache.accepts_memory_trace(
                    id,
                    cfg.provenance_evidence(),
                    cfg.relation_queries(),
                    cfg.relation_evidence()
                ));
            }
            if report.is_memory_checked_core0() {
                assert!(
                    report
                        .functions()
                        .values()
                        .all(|f| f.cfg().all_obligations_proven())
                );
                assert_eq!(
                    interpret(program.runtime()).unwrap().values(),
                    [VirRuntimeValue::U64(42)]
                );
                nera::backend::X86_64_UNKNOWN_LINUX_GNU
                    .codegen_program(program.runtime())
                    .unwrap();
            } else {
                assert!(!report.diagnostics().is_empty());
            }
        }
    }
}

#[test]
fn lower_budgets_do_not_promote_negative_provenance_families() {
    for ordinal in provenance_cases::POSITIVE_COUNT..provenance_cases::FAMILY_COUNT {
        let output = frontend_checks::accepted(
            "provenance-budget.nera",
            &provenance_cases::source(ordinal, 1),
        );
        let program = output.vir().unwrap().resolve().unwrap();
        for config in [
            CfgAnalysisConfig {
                max_guarded_cases_per_block: 1,
                max_guard_atoms_per_case: 0,
                ..Default::default()
            },
            CfgAnalysisConfig {
                relation_limits: DifferenceLimits {
                    max_steps: 0,
                    ..Default::default()
                },
                ..Default::default()
            },
            CfgAnalysisConfig {
                max_region_pairs_per_instruction: 0,
                ..Default::default()
            },
            CfgAnalysisConfig {
                max_relation_evidence: 0,
                ..Default::default()
            },
            CfgAnalysisConfig {
                max_block_visits: 1,
                ..Default::default()
            },
        ] {
            assert!(
                !verify_program(&program, config).is_ok_and(|v| v.is_memory_checked_core0()),
                "family {ordinal}: {config:?}"
            );
        }
    }
}

#[test]
fn a_safe_concrete_alias_call_is_not_a_generic_provenance_proof() {
    let output = frontend_checks::accepted("alias-limited.nera", &provenance_cases::source(11, 0));
    let program = output.vir().unwrap().resolve().unwrap();
    assert!(
        !verify_program(&program, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    // Deliberately an unverified interpreter observation, never native checked differential.
    assert_eq!(
        interpret(program.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn nesting_alias_and_loop_growth_has_bounded_deterministic_observations() {
    for (depth, aliases, iterations) in [(1usize, 1usize, 1), (2, 4, 4), (4, 8, 8), (6, 16, 16)] {
        let mut value = "42".to_owned();
        for _ in 0..depth {
            value = format!("[{value}]");
        }
        let copies: String = (0..aliases)
            .map(|i| format!("let p{i}=base; let same{i}=p{i}==base; "))
            .collect();
        let source = format!(
            "fn main() -> u64 {{ let a={value}; let base=&raw a{};
            {copies} for i in 0usize..{iterations}usize {{ let p=alloc<u64>(1);
            let x=&raw *p; let d=ptr_byte_distance(x,x+8); free(p); }} return 42; }}",
            "[0]".repeat(depth)
        );
        let started = std::time::Instant::now();
        let output = frontend_checks::accepted("provenance-growth.nera", &source);
        let program = output.vir().unwrap().resolve().unwrap();
        let report = verify_program(&program, CfgAnalysisConfig::default()).unwrap();
        assert!(
            report.is_memory_checked_core0(),
            "{depth}/{aliases}/{iterations}: {:?}",
            report.diagnostics()
        );
        let replay = verify_program(&program, CfgAnalysisConfig::default()).unwrap();
        assert_eq!(report, replay);
        assert_eq!(
            interpret(program.runtime()).unwrap().values(),
            [VirRuntimeValue::U64(42)]
        );
        let cfg = report.functions()[&VirFunctionId::new(0)].cfg();
        let retained: usize = cfg
            .blocks()
            .values()
            .map(|b| {
                b.entry_conditional_state().cases().len()
                    + b.instruction_conditional_states()
                        .iter()
                        .map(|s| s.cases().len())
                        .sum::<usize>()
            })
            .sum();
        let max_slots = cfg
            .blocks()
            .values()
            .flat_map(|b| b.instruction_conditional_states())
            .flat_map(|s| s.cases())
            .map(|s| s.allocations().len())
            .max()
            .unwrap_or(0);
        let queries = cfg.relation_queries().len();
        let events = cfg.provenance_evidence().len();
        assert!(
            cfg.block_visits() <= 64
                && retained <= 512
                && queries <= 2048
                && events <= 256
                && max_slots <= 8
        );
        eprintln!(
            "provenance-growth depth={depth} aliases={aliases} iterations={iterations} visits={} retained_cases={retained} max_slots={max_slots} queries={queries} events={events} elapsed_us={}",
            cfg.block_visits(),
            started.elapsed().as_micros()
        );
    }
}

#[test]
fn earlier_combined_source_fixture_remains_contract_free_and_checked() {
    for family in 0..provenance_cases::POSITIVE_COUNT {
        let output = frontend_checks::accepted(
            "no-explicit-contracts.nera",
            &provenance_cases::source(family, 0),
        );
        let unit = output.vir().unwrap().as_unit();
        assert!(
            unit.specs
                .clauses()
                .iter()
                .all(|clause| !matches!(clause.origin, nera::VirSpecClauseOrigin::Explicit { .. }))
        );
        assert!(unit.specs.proves().is_empty());
        assert!(unit.specs.trust_entries().is_empty());
    }
    frontend_checks::checked(
        "native-address-model.nera",
        include_str!("../spec/cases/verify/native-address-model.nera"),
        42,
    );
}
