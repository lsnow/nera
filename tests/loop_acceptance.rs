use nera::verification::{TextReportMode, render_text, verify_source};
use nera::*;

fn erase(source: &str) -> String {
    source
        .lines()
        .filter(|l| !l.trim_start().starts_with("invariant "))
        .collect::<Vec<_>>()
        .join("\n")
}

fn cases() -> Vec<(&'static str, String, bool)> {
    let mut cases = Vec::new();
    for (name, source) in [
        (
            "scalar",
            include_str!("../spec/cases/verify/loop-scalar-target.nera"),
        ),
        (
            "update",
            include_str!("../spec/cases/verify/loop-update-target.nera"),
        ),
        (
            "initialize",
            include_str!("../spec/cases/verify/loop-initialize-target.nera"),
        ),
        (
            "arena",
            include_str!("../spec/cases/verify/loop-arena-initialize.nera"),
        ),
    ] {
        cases.push((name, source.to_owned(), true));
        cases.push((name, erase(source), true));
    }
    let bad = include_str!("../spec/cases/verify/loop-arena-initialize.nera")
        .replace("let value = p[1];", "let value = p[6];");
    cases.push(("arena-uninitialized", bad, false));
    cases
}

#[test]
fn diagnostic_text_distinguishes_entry_backedge_and_exit_failures() {
    for (source, marker) in [
        (
            "fn main()->u64 {let mut i=4; while i<3 {invariant i<=3; i=i+1;} return i;}",
            "entry",
        ),
        (
            "fn main()->u64 {let mut i=0; while i<3 {invariant i==0; i=i+1;} return i;}",
            "back edge",
        ),
        (
            "fn main()->u64 ensures result==4; {let mut i=0; while i<3 {invariant i<=3; i=i+1;} return i;}",
            "postcondition",
        ),
    ] {
        let preview = verify_source(
            &SourceFile::from_text("loop-diagnostics.nera", source),
            Default::default(),
        );
        assert!(!preview.is_checked());
        let text = render_text(&preview, TextReportMode::Explain);
        assert!(
            text.contains(marker) && text.contains("loop-diagnostics.nera"),
            "{text}"
        );
    }
}

#[test]
fn acceptance_matrix_records_failure_instead_of_zero_cost_success() {
    for (name, source, expected) in cases() {
        let output = analyze(&SourceFile::from_text(name, &source));
        let unit = output.vir().unwrap();
        assert!(unit.as_unit().specs.trust_entries().is_empty());
        let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
        assert_eq!(
            report.is_memory_checked_core0(),
            expected,
            "{name}: {:?}",
            report.diagnostics()
        );
    }
}

#[test]
fn measure_loop_acceptance_when_requested() {
    if std::env::var_os("NERA_LOOP_ACCEPTANCE_MEASURE").is_none() {
        return;
    }
    println!(
        "case,mode,sample,checked,caller_lines,core_lines,interface_clauses,loop_clauses,inferred_candidates,attempts,attempt_visits,final_block_visits,refinement_visits,loop_checks,relation_queries,verify_us"
    );
    for (name, source, expected) in cases() {
        let output = analyze(&SourceFile::from_text(name, &source));
        let unit = output.vir().unwrap();
        let resolved = unit.resolve().unwrap();
        let clauses = source.matches("invariant ").count();
        let mode = if clauses == 0 {
            "automatic"
        } else {
            "explicit"
        };
        let main = source.find("fn main").unwrap();
        let split = source[main..]
            .find("\nfn ")
            .map_or(source.len(), |n| main + n);
        let lines = |s: &str| {
            s.lines()
                .filter(|l| !l.trim().is_empty() && !l.trim_start().starts_with("//"))
                .count()
        };
        let interface = source.matches("requires ").count() + source.matches("ensures ").count();
        let inferred = unit
            .as_unit()
            .specs
            .loop_invariants()
            .iter()
            .filter(|i| {
                matches!(
                    unit.as_unit().specs.clause(i.clause).unwrap().origin,
                    VirSpecClauseOrigin::InferredLoop { .. }
                )
            })
            .count();
        for sample in 0..3 {
            let start = std::time::Instant::now();
            let report = verify_program(&resolved, Default::default()).unwrap();
            let micros = start.elapsed().as_micros();
            assert_eq!(report.is_memory_checked_core0(), expected);
            let fs: Vec<_> = report.functions().values().collect();
            let attempts: Vec<_> = fs
                .iter()
                .flat_map(|f| f.cfg().loop_candidate_attempts())
                .collect();
            let checks = fs
                .iter()
                .flat_map(|f| f.cfg().obligations())
                .filter(|o| {
                    matches!(
                        o.obligation().kind(),
                        ResourceObligationKind::LoopInvariantEstablished { .. }
                            | ResourceObligationKind::LoopResourcesPreserved { .. }
                    )
                })
                .count();
            println!(
                "{name},{mode},{sample},{expected},{},{},{interface},{clauses},{inferred},{},{},{},{},{checks},{},{micros}",
                lines(&source[..split]),
                lines(&source[split..]),
                attempts.len(),
                attempts.iter().map(|a| a.block_visits).sum::<u64>(),
                fs.iter().map(|f| f.cfg().block_visits()).sum::<u64>(),
                fs.iter()
                    .map(|f| f.cfg().refinement_block_visits())
                    .sum::<u64>(),
                fs.iter()
                    .map(|f| f.cfg().relation_queries().len())
                    .sum::<usize>()
            );
        }
    }
}
