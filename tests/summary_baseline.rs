#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::*;

const BASELINE: &str = include_str!("../spec/cases/verify/summary-baseline.nera");

#[test]
fn existing_interfaces_cover_wrappers_effects_payloads_and_mutual_recursion() {
    frontend_checks::checked("summary-baseline.nera", BASELINE, 42);
    frontend_checks::checked(
        "summary-baseline-other-branch.nera",
        &BASELINE.replace("choose(true)", "choose(false)"),
        0,
    );
    let output = frontend_checks::accepted("summary-baseline.nera", BASELINE);
    let unit = output.vir().unwrap().as_unit();
    assert!(
        unit.specs
            .clauses()
            .iter()
            .all(|clause| matches!(clause.origin, VirSpecClauseOrigin::InferredType { .. }))
    );
    assert!(unit.specs.proves().is_empty());
    assert!(unit.specs.trust_entries().is_empty());
    let resolved = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert_eq!(
        report,
        verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
    );
}

#[test]
fn body_relations_distinguish_closed_acyclic_summaries_from_recursive_fallback() {
    for (name, source) in [
        (
            "owner-identity",
            "fn main()->u64 { let p=alloc<u64>(1); *p=42; let old=&raw *p; let q=pass(p); let new=&raw *q; if old==new { return 42; } return 0; } fn pass(p:Own<u64>)->Own<u64> { return p; }",
        ),
        (
            "returned-index",
            "fn main()->u64 { let a=[42]; return a[index()]; } fn index()->usize { return 0usize; }",
        ),
        (
            "conditional-index",
            "fn main()->u64 { let a=[42]; let i=index(); if valid(i) { return a[i]; } return 0; } fn index()->usize { return 0usize; } fn valid(i:usize)->bool { return i<1usize; }",
        ),
        (
            "recursive-index",
            "fn main()->u64 { let a=[42]; return a[index(0)]; } fn index(n:u64)->usize { if n==2 { return 0usize; } return index(n+1); }",
        ),
    ] {
        let output = frontend_checks::accepted(name, source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(report.is_memory_checked_core0(), "{name}: body summary");
        assert_eq!(
            interpret(resolved.runtime()).unwrap().values(),
            [VirRuntimeValue::U64(42)]
        );
        assert_eq!(
            report,
            verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
        );
        if name == "recursive-index" {
            let config = CfgAnalysisConfig {
                summary_limits: verifier::summary::SccLimits {
                    max_iterations: 0,
                    ..Default::default()
                },
                ..Default::default()
            };
            let fallback = verify_program(&resolved, config).unwrap();
            assert!(!fallback.is_memory_checked_core0());
            assert!(
                fallback.functions()[&VirFunctionId::new(0)]
                    .cfg()
                    .obligations()
                    .iter()
                    .any(
                        |record| record.obligation().status() == ObligationStatus::Unknown
                            && matches!(
                                record.obligation().kind(),
                                ResourceObligationKind::IndexWithinBounds { .. }
                            )
                    )
            );
        }
    }
}

#[test]
fn local_guard_controls_do_not_need_an_interprocedural_relation() {
    frontend_checks::checked(
        "local-index.nera",
        "fn main()->u64 { let a=[42]; let i=0usize; return a[i]; }",
        42,
    );
    for (index, expected) in [(0, 42), (5, 0)] {
        frontend_checks::checked(
            "local-guard.nera",
            &format!(
                "fn main()->u64 {{ let a=[42]; let i=index(); if i<1usize {{ return a[i]; }} return 0; }} fn index()->usize {{ return {index}usize; }}"
            ),
            expected,
        );
    }
}

#[test]
fn projected_subviews_advance_without_opening_conditional_interfaces() {
    let source = "fn main()->u64 { let a=[1,42]; let p=tail(&a[..]); return p[0]; } fn tail(p:&[u64])->&[u64] { return &p[1..]; }";
    let output = analyze(&SourceFile::from_text(
        "summary-interface-gate.nera",
        source,
    ));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{source}: {:?}",
        output.issues()
    );
    assert!(output.vir().is_some());

    for (source, message) in [
        (
            "fn choose(a:&u64,b:&u64,c:bool)->&u64 { if c { return a; } return b; } fn main()->u64 { return 0; }",
            "multiple path-dependent input sources",
        ),
        (
            "enum Choice { First, Second, } fn main()->u64 { let c=choose(true); match c { Choice::First => { return 42; }, Choice::Second => { return 0; }, } } fn choose(b:bool)->Choice { if b { return Choice::First; } return Choice::Second; }",
            "post-CFG initialization planning",
        ),
        (
            "enum Package { Empty, Full(Own<u64>), } fn pass(p:Package)->Package { return p; } fn main()->u64 { return 0; }",
            "conditional interface summary",
        ),
    ] {
        let output = analyze(&SourceFile::from_text(
            "summary-interface-gate.nera",
            source,
        ));
        assert_eq!(output.status(), FrontendStatus::Unsupported);
        assert!(
            output
                .issues()
                .iter()
                .any(|issue| issue.diagnostic().message().contains(message))
        );
        assert!(output.vir().is_none());
    }
}

#[test]
fn a_callee_memory_fault_cannot_be_hidden_by_a_successful_call_contract() {
    let source = "fn main()->u64 { bad(); return 42; } fn bad() { let p=alloc<u64>(1); let value=*p; free(p); return; }";
    let output = frontend_checks::accepted("summary-fault.nera", source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report.functions()[&VirFunctionId::new(1)]
            .cfg()
            .obligations()
            .iter()
            .any(|record| matches!(
                record.obligation().kind(),
                ResourceObligationKind::MemoryInitialized { .. }
            ) && record.obligation().status() == ObligationStatus::Refuted)
    );
    assert!(matches!(
        interpret(resolved.runtime()).unwrap_err().kind(),
        VirExecutionErrorKind::UninitializedRead { .. }
    ));
}

// Hand-built VIR: Check and a no-return loop have no new source syntax.
fn no_return_unit(check: Option<bool>) -> ValidatedVirUnit {
    let span = ByteSpan::new(0, 1).unwrap();
    let signature = VirSignature {
        parameters: vec![],
        results: vec![],
    };
    let instructions = check.map_or_else(Vec::new, |truth| {
        vec![
            VirInstruction::Constant {
                result: VirValue {
                    id: VirValueId::new(0),
                    ty: VirType::Bool,
                },
                value: VirConstant::Bool(truth),
            },
            VirInstruction::Check {
                condition: VirValueId::new(0),
            },
        ]
    });
    let functions = (0..2)
        .map(|id| {
            let body = if id == 0 {
                vec![VirInstruction::Call {
                    results: vec![],
                    target: VirCallTarget {
                        symbol: "f1".to_owned(),
                        signature: signature.clone(),
                        contract: VirContractId::new(1),
                        abi: None,
                    },
                    arguments: vec![],
                }]
            } else {
                instructions.clone()
            };
            VirFunction {
                id: VirFunctionId::new(id),
                name: format!("f{id}"),
                signature: signature.clone(),
                contract: VirContractId::new(id),
                entry: VirBlockId::new(0),
                source_span: span,
                blocks: vec![VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![],
                    source_span: span,
                    instructions: body
                        .into_iter()
                        .map(|instruction| SpannedVirInstruction {
                            instruction,
                            source_span: span,
                        })
                        .collect(),
                    terminator: SpannedVirTerminator {
                        source_span: span,
                        terminator: if id == 1 && check.is_none() {
                            VirTerminator::Jump {
                                target: VirBlockTarget {
                                    block: VirBlockId::new(0),
                                    arguments: vec![],
                                },
                            }
                        } else {
                            VirTerminator::Return { values: vec![] }
                        },
                    },
                }],
            }
        })
        .collect();
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        functions,
    )
    .into_validated()
    .unwrap()
}

#[test]
fn no_return_and_abort_do_not_mean_an_empty_successful_summary() {
    for check in [Some(true), Some(false), None] {
        let unit = no_return_unit(check);
        let resolved = unit.resolve().unwrap();
        let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert_eq!(report.is_memory_checked_core0(), check != Some(false));
        let cfg = report.functions()[&VirFunctionId::new(1)].cfg();
        assert_eq!(cfg.returns().is_empty(), check != Some(true));
        let summary = report.functions()[&VirFunctionId::new(1)].summary();
        let nera::verifier::summary::Knowledge::Known(returns) = &summary.normal_returns else {
            panic!("a final empty return set is not an unknown analysis");
        };
        assert_eq!(returns.is_empty(), check != Some(true));
        assert_eq!(
            summary.effects.may_read,
            nera::verifier::summary::Knowledge::Known(Vec::new())
        );
        if check == Some(false) {
            assert!(matches!(
                summary.state,
                nera::verifier::summary::SummaryState::Unknown(_)
            ));
            assert!(
                summary
                    .faults
                    .requirements
                    .iter()
                    .any(|r| r.status == ObligationStatus::Refuted)
            );
            assert!(cfg.obligations().iter().any(|record| matches!(
                record.obligation().kind(),
                ResourceObligationKind::CheckTrue { .. }
            ) && record.obligation().status()
                == ObligationStatus::Refuted));
        }
        let execution = interpret_with_config(
            resolved.runtime(),
            VirInterpreterConfig {
                max_steps: 32,
                ..Default::default()
            },
        );
        match check {
            Some(true) => assert!(execution.unwrap().values().is_empty()),
            Some(false) => assert!(matches!(
                execution.unwrap_err().kind(),
                VirExecutionErrorKind::CheckFailed
            )),
            None => assert!(matches!(
                execution.unwrap_err().kind(),
                VirExecutionErrorKind::StepLimitExceeded
            )),
        }
    }
}
