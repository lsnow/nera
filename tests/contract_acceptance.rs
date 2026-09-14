use nera::*;

const INLINE: &str = "fn main()->u64 {let first=40+1; assert first==41; let second=first+1; assert second==42; return second;}";
const INTERFACE: &str = include_str!("../spec/cases/verify/contract-pure.nera");

#[test]
fn caller_and_callee_failures_retain_distinct_sites() {
    let base = "fn main()->u64 {return f(1);} fn f(x:u64)->u64 requires x==1; ensures result==1; {return x;}";
    for (source, caller) in [
        (base.replace("f(1)", "f(2)"), true),
        (base.replace("return x;", "return 2;"), false),
    ] {
        let output = analyze(&SourceFile::from_text("contract-diagnostics.nera", &source));
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .unwrap();
        assert!(!report.is_memory_checked_core0());
        if caller {
            assert!(
                report.functions()[&VirFunctionId::new(0)]
                    .cfg()
                    .obligations()
                    .iter()
                    .any(|o| matches!(
                        o.obligation().kind(),
                        ResourceObligationKind::CallContractPrecondition { .. }
                    ) && !o.obligation().status().is_proven())
            );
        } else {
            assert!(
                report
                    .diagnostics()
                    .iter()
                    .any(|d| d.kind() == VerifierDiagnosticKind::RefutedPostcondition
                        && d.function() == VirFunctionId::new(1))
            );
        }
        assert!(
            report
                .diagnostics()
                .iter()
                .all(|d| !source[d.source_span().start()..d.source_span().end()].is_empty())
        );
    }
}

#[test]
fn inline_and_interface_have_equal_results_without_trust() {
    for source in [INLINE, INTERFACE] {
        let output = analyze(&SourceFile::from_text("contract-cost.nera", source));
        let unit = output.vir().unwrap();
        assert!(unit.as_unit().specs.trust_entries().is_empty());
        let resolved = unit.resolve().unwrap();
        let report = verify_program(&resolved, Default::default()).unwrap();
        assert!(report.is_memory_checked_core0());
        assert_eq!(
            report,
            verify_program(&resolved, Default::default()).unwrap()
        );
        assert_eq!(
            interpret(resolved.runtime()).unwrap().values(),
            [VirRuntimeValue::U64(42)]
        );
    }
}

#[test]
fn measure_contract_acceptance_when_requested() {
    if std::env::var_os("NERA_CONTRACT_ACCEPTANCE_MEASURE").is_none() {
        return;
    }
    println!(
        "case,sample,checked,functions,relation_queries,block_visits,refinement_visits,obligations,postconditions,scc_iterations,scc_body_analyses,verify_us"
    );
    for (name, source) in [
        ("scalar-inline", INLINE),
        ("scalar-interface", INTERFACE),
        (
            "arena-interface",
            include_str!("../spec/cases/verify/contract-arena.nera"),
        ),
        (
            "recursive-interface",
            include_str!("../spec/cases/verify/contract-recursive.nera"),
        ),
    ] {
        let output = analyze(&SourceFile::from_text(name, source));
        let resolved = output.vir().unwrap().resolve().unwrap();
        for sample in 0..5 {
            let start = std::time::Instant::now();
            let report = verify_program(&resolved, Default::default()).unwrap();
            let elapsed = start.elapsed().as_micros();
            assert!(report.is_memory_checked_core0());
            let fs: Vec<_> = report.functions().values().collect();
            // Shared SCC analysis is counted once, not once per member.
            let sccs: Vec<_> = report
                .functions()
                .iter()
                .filter_map(|(id, f)| {
                    f.summary()
                        .recursion
                        .as_ref()
                        .filter(|scc| scc.members.iter().min() == Some(id))
                })
                .collect();
            println!(
                "{name},{sample},true,{},{},{},{},{},{},{},{},{elapsed}",
                fs.len(),
                fs.iter()
                    .map(|f| f.cfg().relation_queries().len())
                    .sum::<usize>(),
                fs.iter().map(|f| f.cfg().block_visits()).sum::<u64>(),
                fs.iter()
                    .map(|f| f.cfg().refinement_block_visits())
                    .sum::<u64>(),
                fs.iter()
                    .map(|f| f.cfg().obligations().len())
                    .sum::<usize>(),
                fs.iter().map(|f| f.postconditions().len()).sum::<usize>(),
                sccs.iter().map(|s| s.iterations as u64).sum::<u64>(),
                sccs.iter().map(|s| s.body_analyses).sum::<usize>()
            );
        }
    }
}
