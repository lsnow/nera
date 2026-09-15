use nera::*;

const RELEASE: &str = "fn main()->u64 {
    let memory=alloc<u64>(1); let mut iteration=0;
    while iteration<2 {
        if iteration==0 { free(memory); }
        iteration=iteration+1;
    }
    return iteration;
}";

#[test]
fn conditional_resource_invariants_check_real_phases_without_restoring_authority() {
    checked(
        "fn main()->u64 {let p=alloc<u64>(1); let mut i=0;
        while i<3 {invariant i!=0 || alive(p.region); if i==0 {free(p);} i=i+1;}
        return i;}",
        3,
    );
    checked(
        "fn main()->u64 {let p=alloc<u64>(1); *p=7; let mut i=0;
        while i<3 {invariant i!=0 || readable(p,0usize..1usize); if i==0 {free(p);} i=i+1;}
        return i;}",
        3,
    );
    for source in [
        "fn main()->u64 {let p=alloc<u64>(1); let mut i=0; while i<3 {invariant i==0 || alive(p.region); if i==0 {free(p);} i=i+1;} return i;}",
        "fn main()->u64 {let p=alloc<u64>(1); let mut i=0; while i<3 {invariant i!=0 || alive(p.region); free(p); i=i+1;} return i;}",
        "fn main()->u64 {let p=alloc<u64>(1); let mut i=0; while i<3 {invariant i!=0 || initialized(p); if i==0 {free(p);} i=i+1;} return i;}",
    ] {
        let (_, report) = inspect(source, Default::default());
        assert!(!report.is_memory_checked_core0(), "{source}");
    }
}

#[test]
fn comparison_candidates_preserve_nested_disjunction_not_a_two_counter_special_case() {
    // Skipping element 2 does not make the actually written element 3 unreadable.
    // The missing-element read remains a rejection in loop_candidates.
    checked(
        "fn main()->u64 {let p=alloc<[u64;4]>(1); for i in 0usize..4usize {if i==2usize {continue;} p[i]=42;} let x=p[3]; free(p); return x;}",
        42,
    );
    for threshold in [0, 1] {
        let source = format!(
            "fn main()->u64 {{let p=alloc<u64>(1);let mut i=0;
            while i<3 {{ let mut j=0; while j<3 {{
                if i=={threshold} {{if j=={threshold} {{free(p);}}}} j=j+1;
            }} i=i+1;}} return i;}}"
        );
        checked(&source, 3);
        if threshold == 0 {
            let (_, report) = inspect(
                &source,
                CfgAnalysisConfig {
                    max_loop_partition_cuts: 0,
                    ..Default::default()
                },
            );
            assert!(!report.is_memory_checked_core0());
        }
    }
}

fn inspect(source: &str, config: CfgAnalysisConfig) -> (FrontendOutput, ProgramVerification) {
    let output = analyze(&SourceFile::from_text("loop-partitions.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let report = verify_program(&output.vir().unwrap().resolve().unwrap(), config).unwrap();
    (output, report)
}

fn checked(source: &str, result: u64) {
    let (output, report) = inspect(source, Default::default());
    assert!(
        report.is_memory_checked_core0(),
        "{source}\n{:?}",
        report.diagnostics()
    );
    for function in report.functions().values() {
        if !function.cfg().loop_blocks().is_empty() {
            assert!(function.cfg().closure_audited());
        }
    }
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        report,
        verify_program(&resolved, Default::default()).unwrap()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(result)]
    );
}

#[test]
fn final_closure_budget_is_required_even_after_inference_converges() {
    for source in [
        RELEASE,
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=i+1;} return i;}",
        "fn main()->u64 {while true {} return 0;}",
        "fn main()->u64 {let mut i=0; while i<0 {i=i+1;} return i;}",
        "fn main()->u64 {return worker();} fn worker()->u64 {let mut i=0; while i<3 {i=i+1;} return i;}",
    ] {
        let output = analyze(&SourceFile::from_text("closure-budget.nera", source));
        let program = output.vir().unwrap().resolve().unwrap();
        let checked = verify_program(&program, Default::default()).unwrap();
        assert!(
            checked.is_memory_checked_core0(),
            "{:?}",
            checked.diagnostics()
        );
        for limit in [0, 1] {
            let result = verify_program(
                &program,
                CfgAnalysisConfig {
                    max_closure_audit_steps: limit,
                    ..Default::default()
                },
            );
            assert!(
                !result.as_ref().is_ok_and(|r| r.is_memory_checked_core0()),
                "{source}: {result:?}"
            );
        }
    }
}

#[test]
fn conditional_release_is_not_a_first_iteration_or_two_iteration_special_case() {
    checked(RELEASE, 2);
    for threshold in [0, 1, 3] {
        for bound in [0, 2, 8] {
            checked(
                &format!(
                    "fn main()->u64 {{return release_once({bound});}}
                fn release_once(limit:u64)->u64 {{
                    let storage=alloc<u64>(1); let mut cursor=0;
                    while cursor<limit {{
                        if cursor=={threshold} {{free(storage);}}
                        cursor=cursor+1;
                    }} return cursor;
                }}"
                ),
                bound,
            );
        }
    }
}

#[test]
fn continue_break_and_nested_loops_keep_actual_resource_transitions() {
    checked(
        "fn main()->u64 {let p=alloc<u64>(1);let mut i=0;
        while i<4 {
            if i==0 {free(p);i=i+1;continue;}
            if i==2 {break;}
            i=i+1;
        } return i;}",
        2,
    );
    checked(
        "fn main()->u64 {let p=alloc<u64>(1);let mut i=0;
        while i<2 {if i==0 {free(p);} let mut j=0;
            while j<2 {j=j+1;}
            i=i+1;
        } return i;}",
        2,
    );
}

#[test]
fn repeated_release_reset_wrapping_and_post_release_read_never_become_checked() {
    for source in [
        RELEASE
            .replace(
                "let memory=alloc<u64>(1);",
                "let memory=alloc<u64>(1); *memory=42; let reference=&*memory;",
            )
            .replace("return iteration;", "return *reference;"),
        RELEASE.replace("iteration==0", "iteration<2"),
        RELEASE.replace("iteration=iteration+1;", "iteration=0;"),
        RELEASE.replace(
            "iteration=iteration+1;",
            "iteration=iteration+18446744073709551615;iteration=iteration+1;",
        ),
        RELEASE.replace(
            "iteration=iteration+1;",
            "if iteration==1 {let value=*memory;} iteration=iteration+1;",
        ),
    ] {
        let (_, report) = inspect(&source, Default::default());
        assert!(!report.is_memory_checked_core0(), "{source}");
    }
}

#[test]
fn exhausted_partitions_conservatively_lose_proofs_instead_of_dropping_paths() {
    for budget in [0, 1] {
        let (_, report) = inspect(
            RELEASE,
            CfgAnalysisConfig {
                max_guarded_cases_per_block: budget,
                max_refinement_passes: 0,
                ..Default::default()
            },
        );
        assert!(!report.is_memory_checked_core0());
        assert!(report.functions().values().any(|f| {
            f.cfg()
                .guarded_precision_losses()
                .values()
                .any(|losses| losses.contains(&GuardedStatePrecisionLoss::LoopPartitionBudget))
        }));
    }
}

#[test]
fn large_trip_counts_do_not_require_iteration_unrolling() {
    let source = RELEASE.replace("iteration<2", "iteration<1000000000");
    let (_, report) = inspect(&source, Default::default());
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    assert!(
        report
            .functions()
            .values()
            .all(|f| f.cfg().block_visits() < 100)
    );
    // Deliberately do not interpret one billion iterations.
}
