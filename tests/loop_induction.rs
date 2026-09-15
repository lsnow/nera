use nera::*;

fn inspect(source: &str) -> (FrontendOutput, ProgramVerification) {
    let output = analyze(&SourceFile::from_text("loop-induction.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .unwrap();
    (output, report)
}

#[test]
fn scalar_induction_checks_entry_backedge_and_arbitrary_parameter_exit() {
    for source in [
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=i+1;} assert i==3; return i;}",
        "fn main()->u64 {return count(6);} fn count(n:u64)->u64 ensures result==n; {let mut i=0; while i<n {invariant i<=n; i=i+1;} return i;}",
    ] {
        let (output, report) = inspect(source);
        assert!(
            report.is_memory_checked_core0(),
            "{:?}",
            report.diagnostics()
        );
        let checks: Vec<_> = report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .filter(|o| {
                matches!(
                    o.obligation().kind(),
                    ResourceObligationKind::LoopInvariantEstablished { .. }
                )
            })
            .collect();
        assert!(checks.iter().any(|o| matches!(
            o.obligation().kind(),
            ResourceObligationKind::LoopInvariantEstablished {
                back_edge: false,
                ..
            }
        )));
        assert!(checks.iter().any(|o| matches!(
            o.obligation().kind(),
            ResourceObligationKind::LoopInvariantEstablished {
                back_edge: true,
                ..
            }
        )));
        assert!(checks.iter().all(|o| o.obligation().is_proven()));
        assert!(
            output
                .vir()
                .unwrap()
                .as_unit()
                .specs
                .trust_entries()
                .is_empty()
        );
        interpret(output.vir().unwrap().resolve().unwrap().runtime()).unwrap();
    }
}

#[test]
fn false_initial_false_inductive_and_overflow_loops_never_publish_checked() {
    for source in [
        "fn main()->u64 {let mut i=4; while i<3 {invariant i<=3; i=i+1;} return i;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant i==0; i=i+1;} return i;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=i+2;} return i;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant false; i=i+1;} return i;}",
        "fn main()->u64 {let mut i=18446744073709551614; while i<=18446744073709551615 {invariant 18446744073709551614<=i; i=i+1;} return i;}",
    ] {
        let (_, report) = inspect(source);
        assert!(!report.is_memory_checked_core0(), "{source}");
        assert!(
            report
                .functions()
                .values()
                .any(|f| !f.cfg().all_obligations_proven())
        );
    }
}

#[test]
fn each_backedge_and_local_assert_remain_independent_obligations() {
    let (_, report) = inspect(
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; if i==0 {i=i+1; continue;} i=i+2;} return i;}",
    );
    let edges: Vec<_> = report.functions()[&VirFunctionId::new(0)]
        .cfg()
        .obligations()
        .iter()
        .filter(|o| {
            matches!(
                o.obligation().kind(),
                ResourceObligationKind::LoopInvariantEstablished {
                    back_edge: true,
                    ..
                }
            )
        })
        .collect();
    assert_eq!(edges.len(), 2);
    assert_ne!(edges[0].block(), edges[1].block());
    assert!(edges.iter().any(|o| !o.obligation().is_proven()));
    assert!(!report.is_memory_checked_core0());
    let (_, report) = inspect(
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; assert i==0; i=i+1;} return i;}",
    );
    assert!(!report.is_memory_checked_core0());
    assert!(
        report.functions()[&VirFunctionId::new(0)]
            .proofs()
            .iter()
            .any(|p| !p.status().is_proven())
    );
}

#[test]
fn zero_iteration_no_backedge_and_divergence_do_not_invent_returns() {
    for source in [
        "fn main()->u64 {let mut i=0; while false {invariant i<=3; i=i+1;} return 0;}",
        "fn main()->u64 {while true {invariant true; return 5;} return 0;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=i+1; if i==1 {break;}} return i;}",
    ] {
        let (_, report) = inspect(source);
        assert!(
            report.is_memory_checked_core0(),
            "{source}: {:?}",
            report.diagnostics()
        );
    }
    let (_, report) = inspect("fn main(){while true {invariant true; continue;} return;}");
    assert!(report.is_memory_checked_core0());
    assert!(
        report.functions()[&VirFunctionId::new(0)]
            .cfg()
            .returns()
            .is_empty()
    );
    // WordAdd is wrapping; overflow alone is not a memory fault. No claim of
    // termination or monotonicity follows from the invariant `true`.
    let (_, report) =
        inspect("fn main(){let mut i=0; while true {invariant true; i=i+1;} return;}");
    assert!(report.is_memory_checked_core0());
    assert!(
        report.functions()[&VirFunctionId::new(0)]
            .cfg()
            .returns()
            .is_empty()
    );
}

#[test]
fn work_is_independent_of_iteration_count_and_budgets_fail_closed() {
    let mut visits = Vec::new();
    for n in [1, 10_000, u64::MAX] {
        let source = format!(
            "fn main()->u64 {{let mut i=0; while i<{n} {{invariant i<={n}; i=i+1;}} assert i=={n}; return i;}}"
        );
        let (output, report) = inspect(&source);
        assert!(report.is_memory_checked_core0());
        let resolved = output.vir().unwrap().resolve().unwrap();
        let cfg = analyze_function_cfg_with_config(
            &resolved,
            VirFunctionId::new(0),
            CfgAnalysisConfig {
                max_block_visits: 32,
                ..Default::default()
            },
        )
        .unwrap();
        assert!(cfg.all_obligations_proven());
        assert!(cfg.widened_blocks().is_empty());
        visits.push(cfg.block_visits());
        assert!(matches!(
            analyze_function_cfg_with_config(
                &resolved,
                VirFunctionId::new(0),
                CfgAnalysisConfig {
                    max_block_visits: 1,
                    ..Default::default()
                }
            ),
            Err(CfgAnalysisError::BlockVisitLimitExceeded { .. })
        ));
        assert!(
            analyze_function_cfg_with_config(
                &resolved,
                VirFunctionId::new(0),
                CfgAnalysisConfig {
                    max_relation_evidence: 0,
                    ..Default::default()
                }
            )
            .is_err()
        );
    }
    assert!(visits.iter().all(|n| *n == visits[0]));
}

#[test]
fn failed_induction_blocks_caller_contract_and_summary_replay_rejects_omissions() {
    use nera::verifier::{relation::audit::RelationReplayCache, summary::audit::SummaryAudit};
    let good = "fn main()->u64 {return count(6);} fn count(n:u64)->u64 ensures result==n; {let mut i=0; while i<n {invariant i<=n; i=i+1;} return i;}";
    let (output, report) = inspect(good);
    assert!(report.is_memory_checked_core0());
    let resolved = output.vir().unwrap().resolve().unwrap();
    let cache = RelationReplayCache::new(&resolved, Default::default()).unwrap();
    let audit = SummaryAudit::from_report(&report);
    assert!(cache.accepts_summary_audit(&audit));
    let mut bad_audit = audit.clone();
    let function = bad_audit
        .functions
        .iter_mut()
        .find(|f| f.function == VirFunctionId::new(1))
        .unwrap();
    let index = function
        .requirements
        .iter()
        .position(|(_, finding)| {
            matches!(
                finding.site(),
                VerifierFindingSite::Spec {
                    location: VirSpecLocation::Runtime(_),
                    ..
                }
            )
        })
        .unwrap();
    function.requirements.remove(index);
    assert!(!cache.accepts_summary_audit(&bad_audit));
    let (_, mutated) = inspect(
        "fn main()->u64 {return change(0);} fn change(n:u64)->u64 requires n<=3; ensures result==old(n); {let mut m=n; while m<3 {invariant m<=3; m=m+1;} return m;}",
    );
    assert!(!mutated.is_memory_checked_core0());
    assert!(
        mutated.functions()[&VirFunctionId::new(1)]
            .cfg()
            .all_obligations_proven()
    );
    assert!(
        mutated.functions()[&VirFunctionId::new(1)]
            .postconditions()
            .iter()
            .any(|p| !p.check().status.is_proven())
    );
    let (_, report) = inspect(&good.replace("i=i+1", "i=i+2"));
    assert!(!report.is_memory_checked_core0());
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

#[test]
fn raw_loop_mutations_cannot_skip_checks_or_reuse_first_iteration_values() {
    let (output, _) =
        inspect("fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=i+1;} return i;}");
    for mutation in 0..3 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let boundary = unit.specs.loop_invariants_mut()[0]
            .boundary
            .as_mut()
            .unwrap();
        match mutation {
            0 => boundary.back_edges.clear(),
            1 => boundary.bindings[0].entry = boundary.bindings[0].head,
            _ => {
                for instruction in unit
                    .runtime
                    .functions
                    .iter_mut()
                    .flat_map(|f| &mut f.blocks)
                    .flat_map(|b| &mut b.instructions)
                {
                    if let VirInstruction::Constant {
                        value: VirConstant::U64(n),
                        ..
                    } = &mut instruction.instruction
                        && *n == 1
                    {
                        *n = 4;
                    }
                }
                let unit = unit.into_validated().unwrap();
                assert!(
                    !verify_program(&unit.resolve().unwrap(), Default::default())
                        .unwrap()
                        .is_memory_checked_core0()
                );
                continue;
            }
        }
        assert!(unit.validate().is_err());
    }
}

#[test]
fn scalar_profile_rejects_unimplemented_loop_effects_and_snapshot_theories() {
    for source in [
        "fn main(){for i in 0..3 {invariant i==0 || i<=3;} return;}",
        "fn main(){while true {invariant true; while true {continue;} break;} return;}",
        "fn main(){while true {invariant true; let p=alloc<u64>(1); free(p); break;} return;}",
        "fn main(){while cond() {invariant true; break;} return;} fn cond()->bool{let p=alloc<u64>(1); free(p); return true;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant old(i)<=i; i=i+1;} return i;}",
        "fn main()->u64 {let mut i=0; while i<3 {invariant i==0 || i<=3; i=i+1;} return i;}",
    ] {
        let output = analyze(&SourceFile::from_text("unsupported-loop.nera", source));
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
fn supplied_resource_ledger_cannot_be_erased_by_scalar_head_abstraction() {
    let (output, _) =
        inspect("fn main()->u64 {let mut i=0; while i<3 {invariant i<=3; i=i+1;} return i;}");
    let mut state = ResourceState::new();
    state
        .define_allocation(
            AbstractAllocationId::new(0),
            AbstractAllocation::new(VirRegionId::new(0), 8, 8).unwrap(),
        )
        .unwrap();
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert!(matches!(
        analyze_function_cfg_with_entry(
            &resolved,
            VirFunctionId::new(0),
            &state,
            Default::default()
        ),
        Err(CfgAnalysisError::LoopInvariantResourceStateUnsupported)
    ));
}

#[test]
fn finite_counter_models_agree_with_every_checked_candidate() {
    for start in 0..4u64 {
        for bound in 0..4u64 {
            for step in [1, 2] {
                let source = format!(
                    "fn main()->u64 {{let mut i={start}; while i<{bound} {{invariant i<={bound}; i=i+{step};}} return i;}}"
                );
                let (_, report) = inspect(&source);
                if report.is_memory_checked_core0() {
                    let mut i = start;
                    assert!(i <= bound);
                    while i < bound {
                        i += step;
                        assert!(i <= bound, "{source}");
                    }
                }
            }
        }
    }
}
