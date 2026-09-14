#[path = "support/contract_baseline.rs"]
mod fixture;
#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::verifier::summary::SummaryState;
use nera::{
    CfgAnalysisConfig, FrontendStatus, ObligationStatus, ResourceObligationKind, SourceFile,
    VirFunctionId, VirRuntimeValue, analyze, interpret, verify_program,
};

#[test]
fn scalar_and_cell_frames_are_parsed_without_claiming_general_arena_proofs() {
    for (name, source) in [("scalar", fixture::SCALAR), ("cell", fixture::CELL)] {
        let output = analyze(&SourceFile::from_text(name, source));
        assert_eq!(
            output.status(),
            FrontendStatus::AcceptedProposal,
            "{name}: {:?}",
            output.issues()
        );
        assert!(output.vir().is_some());
    }
}

#[test]
fn pointer_old_and_non_entry_footprints_remain_gated() {
    for clause in [
        "ensures result == old(value);",
        "reads result[0..1];",
        "writes result[0..1];",
    ] {
        let source = format!(
            "fn main()->u64 {{return 0;}} fn target(value: &mut u64)->u64\n{clause}\n{{return 0;}}"
        );
        let output = analyze(&SourceFile::from_text("contract-gate.nera", &source));
        assert_eq!(
            output.status(),
            FrontendStatus::Unsupported,
            "{clause}: {:?}",
            output.issues()
        );
        assert!(output.vir().is_none());
    }
}

#[test]
fn scalar_and_cell_runtime_baselines_do_not_claim_contract_proofs() {
    for (name, source) in [("scalar", fixture::SCALAR), ("cell", fixture::CELL)] {
        let erased = fixture::erased(source);
        assert_eq!(source.len(), erased.len());
        frontend_checks::checked(name, &erased, 42);
        let output = frontend_checks::accepted(name, &erased);
        let unit = output.vir().unwrap();
        assert!(unit.as_unit().specs.trust_entries().is_empty());
        let report =
            verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
        assert!(report.functions().values().all(|f| f.proofs().is_empty()));
    }
}

#[test]
fn arena_runtime_baseline_records_the_actual_boundary() {
    let source = fixture::erased(fixture::ARENA);
    let output = analyze(&SourceFile::from_text("arena-erased.nera", &source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let unit = output.vir().unwrap();
    let report = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    // A bool-returning cursor update does not currently export its new heap value
    // to the next slice range. Do not accept an arbitrary failure as this gap.
    assert!(
        report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| matches!(
                o.obligation().kind(),
                ResourceObligationKind::SliceRangeWithinBounds { .. }
            ) && o.obligation().status() == ObligationStatus::Unknown)
    );
    assert!(unit.as_unit().specs.trust_entries().is_empty());
    // Concrete success does not turn the abstract Unknown into a proof.
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(49)]
    );
}

#[test]
fn reserve_runtime_covers_capacity_failure_without_claiming_heap_postconditions() {
    let source = fixture::erased(fixture::ARENA);
    let reserve = &source[source.find("fn reserve(").unwrap()..source.find("fn take(").unwrap()];
    for (cursor, end, expected_success, expected_cursor) in [
        (0, 2, true, 2),
        (2, 4, true, 4),
        (4, 7, false, 4),
        (4, 3, false, 4),
        (4, 6, true, 6),
        (4, 4, true, 4),
    ] {
        let check = format!("if cursor == {expected_cursor}usize {{return 42;}}");
        let branch = if expected_success {
            format!("if ok {{{check}}}")
        } else {
            format!("if ok {{return 99;}} {check}")
        };
        let main = format!(
            "fn main()->u64 {{let mut cursor={cursor}usize; let ok=reserve(&mut cursor,6usize,{end}usize); {branch} return 99;}}\n{reserve}"
        );
        frontend_checks::checked("reserve-runtime.nera", &main, 42);
    }
}

#[test]
fn clause_counts_distinguish_targets_from_unannotated_runtime_baselines() {
    for (source, expected) in [
        (fixture::SCALAR, 4),
        (fixture::CELL, 4),
        (fixture::ARENA, 12),
    ] {
        assert_eq!(
            source
                .lines()
                .filter(|line| fixture::is_contract_line(line))
                .count(),
            expected
        );
        assert!(
            !fixture::erased(source)
                .lines()
                .any(fixture::is_contract_line)
        );
        assert!(
            !source.contains('\''),
            "ordinary callers have no explicit lifetime syntax"
        );
    }
}

#[test]
fn raw_caller_and_callee_are_checked_independently_before_publication() {
    for (argument, wrong_body) in [(1, false), (2, false), (0, false), (1, true)] {
        let unit = fixture::scalar_unit(argument, wrong_body)
            .into_validated()
            .unwrap();
        let resolved = unit.resolve().unwrap();
        let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert_eq!(
            report,
            verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
        );
        assert!(unit.as_unit().specs.trust_entries().is_empty());
        let caller = &report.functions()[&VirFunctionId::new(0)];
        let callee = &report.functions()[&VirFunctionId::new(1)];
        assert_eq!(
            report.is_memory_checked_core0(),
            argument != 0 && !wrong_body
        );
        if argument == 0 {
            assert!(caller.cfg().obligations().iter().any(|o| matches!(
                o.obligation().kind(),
                ResourceObligationKind::CallContractPrecondition { .. }
            ) && o.obligation().status()
                == ObligationStatus::Refuted));
        } else if wrong_body {
            assert!(
                callee
                    .postconditions()
                    .iter()
                    .any(|p| p.check().status == ObligationStatus::Refuted)
            );
            assert_ne!(callee.summary().state, SummaryState::Closed);
            assert_ne!(caller.summary().state, SummaryState::Closed);
        } else {
            assert_eq!(callee.summary().state, SummaryState::Closed);
            assert_eq!(caller.summary().state, SummaryState::Closed);
            assert_eq!(
                interpret(resolved.runtime()).unwrap().values(),
                [VirRuntimeValue::U64(argument)]
            );
        }
    }
}

#[test]
fn measure_contract_baseline_when_requested() {
    if std::env::var_os("NERA_CONTRACT_BASELINE_MEASURE").is_none() {
        return;
    }
    println!(
        "case,sample,checked,relation_queries,block_visits,refinement_visits,obligations,postconditions,verify_us"
    );
    for (name, source, expected) in [
        ("scalar-erased", fixture::SCALAR, true),
        ("cell-erased", fixture::CELL, true),
        ("arena-erased", fixture::ARENA, false),
    ] {
        let output = frontend_checks::accepted(name, &fixture::erased(source));
        measure(name, output.vir().unwrap(), expected);
    }
    measure(
        "raw-scalar",
        &fixture::scalar_unit(1, false).into_validated().unwrap(),
        true,
    );
}

fn measure(name: &str, unit: &nera::ValidatedVirUnit, expected: bool) {
    let resolved = unit.resolve().unwrap();
    for sample in 0..5 {
        let start = std::time::Instant::now();
        let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        let micros = start.elapsed().as_micros();
        assert_eq!(report.is_memory_checked_core0(), expected);
        let functions: Vec<_> = report.functions().values().collect();
        let queries: usize = functions
            .iter()
            .map(|f| f.cfg().relation_queries().len())
            .sum();
        let visits: u64 = functions.iter().map(|f| f.cfg().block_visits()).sum();
        let refinements: u64 = functions
            .iter()
            .map(|f| f.cfg().refinement_block_visits())
            .sum();
        let obligations: usize = functions.iter().map(|f| f.cfg().obligations().len()).sum();
        let post: usize = functions.iter().map(|f| f.postconditions().len()).sum();
        println!(
            "{name},{sample},{expected},{queries},{visits},{refinements},{obligations},{post},{micros}"
        );
    }
}
