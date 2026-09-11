#[path = "support/frontend_checks.rs"]
mod frontend_checks;
#[path = "../src/bin/fuzz_support/relation_cases.rs"]
mod relation_cases;

use nera::verifier::relation::{audit::RelationReplayCache, difference::DifferenceLimits};
use nera::{CfgAnalysisConfig, ResourceObligationKind, VirRuntimeValue, interpret, verify_program};

#[test]
fn relation_matrix_checks_all_resources_before_differential_and_replays_evidence() {
    for ordinal in 0..relation_cases::FAMILY_COUNT * 2 {
        let source = relation_cases::source(ordinal, ordinal.wrapping_mul(0x9e37_79b9));
        let output = frontend_checks::accepted("relation-acceptance.nera", &source);
        let program = output.vir().unwrap().resolve().unwrap();
        let config = CfgAnalysisConfig::default();
        let verified = verify_program(&program, config).unwrap();
        assert_eq!(
            verified.is_memory_checked_core0(),
            relation_cases::expected_checked(ordinal),
            "family {ordinal}: {:#?}",
            verified.diagnostics()
        );
        assert_eq!(verified, verify_program(&program, config).unwrap());
        if verified.is_memory_checked_core0() {
            assert!(
                verified
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
            let cache = RelationReplayCache::new(&program, config).unwrap();
            for (&id, function) in verified.functions() {
                assert!(cache.accepts_trace(id, function.cfg().relation_queries()));
                for evidence in function.cfg().relation_evidence() {
                    assert!(cache.accepts_relation(evidence));
                }
            }
        } else {
            assert!(!verified.diagnostics().is_empty());
        }
    }
}

#[test]
fn budget_reduction_never_promotes_negative_relation_families() {
    for family in relation_cases::POSITIVE_COUNT..relation_cases::FAMILY_COUNT {
        let source = relation_cases::source(family, 42);
        let output = frontend_checks::accepted("relation-budget.nera", &source);
        let program = output.vir().unwrap().resolve().unwrap();
        for config in [
            CfgAnalysisConfig {
                relation_limits: DifferenceLimits {
                    max_steps: 0,
                    ..Default::default()
                },
                ..Default::default()
            },
            CfgAnalysisConfig {
                max_guarded_cases_per_block: 1,
                max_guard_atoms_per_case: 0,
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
                "family {family}, {config:?}"
            );
        }
    }
}

#[test]
fn numeric_evidence_and_a_successful_run_do_not_certify_all_paths() {
    // The zero-iteration concrete path is safe, but the generic callee still
    // has no index bound. A numeric trace must not bypass that obligation.
    let source = "fn main()->u64 { return get(false,0usize); }
        fn get(b:bool,i:usize)->u64 { let a=[42,0]; if b { return a[i]; } return 42; }";
    let out = frontend_checks::accepted("unchecked-path.nera", source);
    let program = out.vir().unwrap().resolve().unwrap();
    let verified = verify_program(&program, CfgAnalysisConfig::default()).unwrap();
    assert!(!verified.is_memory_checked_core0());
    assert_eq!(
        interpret(program.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
    assert!(
        verified
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| matches!(
                o.obligation().kind(),
                ResourceObligationKind::IndexWithinBounds { .. }
            ) && !o.obligation().is_proven())
    );
}

#[test]
fn combined_heap_prefix_and_three_child_call_case_is_checked() {
    frontend_checks::checked(
        "relation-acceptance.nera",
        include_str!("../spec/cases/verify/relation-acceptance.nera"),
        42,
    );
}

#[test]
fn nonzero_subslice_calls_remain_explicitly_limited_without_false_safety_claims() {
    let source = include_str!("../spec/cases/verify/relation-acceptance-limited.nera");
    let output = frontend_checks::accepted("relation-limited.nera", source);
    let program = output.vir().unwrap().resolve().unwrap();
    let verified = verify_program(&program, CfgAnalysisConfig::default()).unwrap();
    assert!(!verified.is_memory_checked_core0());
    assert!(
        verified
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| o.obligation().status() == nera::ObligationStatus::Unknown)
    );
    // This particular run is safe, but it is NOT a checked differential.
    assert_eq!(
        interpret(program.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn relation_variable_growth_records_precision_and_deterministic_work() {
    for count in [2usize, 4, 8, 12] {
        let source = format!(
            "fn main()->u64 {{ return read({}); }}
            fn read({})->u64 {{ let a=[{}]; {} return a[x0]; {} return 0; }}",
            (0..count)
                .map(|i| format!("{i}usize"))
                .collect::<Vec<_>>()
                .join(","),
            (0..count)
                .map(|i| format!("x{i}:usize"))
                .collect::<Vec<_>>()
                .join(","),
            vec!["42"; count].join(","),
            (0..count)
                .map(|i| if i + 1 < count {
                    format!("if x{i}<x{} {{", i + 1)
                } else {
                    format!("if x{i}<{count}usize {{")
                })
                .collect::<String>(),
            "}".repeat(count)
        );
        let start = std::time::Instant::now();
        let output = frontend_checks::accepted("relation-variable-growth.nera", &source);
        let program = output.vir().unwrap().resolve().unwrap();
        let verified = verify_program(&program, CfgAnalysisConfig::default()).unwrap();
        let visits: u64 = verified
            .functions()
            .values()
            .map(|f| f.cfg().block_visits())
            .sum();
        let queries: usize = verified
            .functions()
            .values()
            .map(|f| f.cfg().relation_queries().len())
            .sum();
        let states: usize = verified
            .functions()
            .values()
            .flat_map(|f| f.cfg().blocks().values())
            .map(|b| {
                b.entry_conditional_state().cases().len()
                    + b.instruction_conditional_states()
                        .iter()
                        .map(|s| s.cases().len())
                        .sum::<usize>()
            })
            .sum();
        assert!(visits <= 256 && queries <= 2048);
        let checked = verified.is_memory_checked_core0();
        if count == 2 {
            assert!(checked);
        }
        if checked {
            assert_eq!(
                interpret(program.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(42)]
            );
        }
        assert_eq!(
            verified,
            verify_program(&program, CfgAnalysisConfig::default()).unwrap()
        );
        eprintln!(
            "relation-growth roots={count} checked={checked} elapsed_us={} visits={visits} states={states} queries={queries}",
            start.elapsed().as_micros()
        );
    }
}
