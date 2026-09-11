use nera::verification::*;
#[path = "support/preview_checks.rs"]
mod preview_checks;
use nera::*;

fn source(text: &str) -> SourceFile {
    SourceFile::from_text("preview.nera", text)
}
fn raw(text: &str) -> VirUnit {
    analyze(&source(text)).vir().unwrap().as_unit().clone()
}
const SAFE: &str = include_str!("../spec/cases/verify/summary-recursive.nera");

#[test]
fn source_report_is_exactly_the_canonical_result_with_borrowed_evidence() {
    let source = source(SAFE);
    let config = CfgAnalysisConfig::default();
    let preview = verify_source(&source, config);
    assert_eq!(preview.outcome(), PreviewOutcome::Checked);
    assert_eq!(
        preview.frontend_status(),
        Some(FrontendStatus::AcceptedProposal)
    );
    assert!(preview.is_resolved());
    let resolved = preview.validated_unit().unwrap().resolve().unwrap();
    assert_eq!(
        preview.verification().unwrap(),
        &verify_program(&resolved, config).unwrap()
    );
    assert_eq!(preview, verify_source(&source, config));
    assert_eq!(preview.source(), Some(&source));
    let counts = preview.counts().unwrap();
    assert_eq!(preview.obligations().unwrap().count(), counts.total());
    assert_eq!(counts.functions, preview.summaries().unwrap().count());
    assert_eq!(counts.summaries_closed, counts.functions);
    assert_eq!(
        preview.historical().unwrap().count(),
        counts.historical.total()
    );
    for obligation in preview.obligations().unwrap() {
        assert_eq!(obligation.function, obligation.finding().site().function());
        let f = &preview.verification().unwrap().functions()[&obligation.function];
        if let ObligationEvidence::Cfg(e) = obligation.evidence {
            assert!(
                f.cfg()
                    .obligations()
                    .iter()
                    .any(|original| std::ptr::eq(original, e))
            );
        }
    }
    let versions = preview.versions();
    assert_eq!(versions.runtime, Some(resolved.runtime().semantic_profile));
    assert_eq!(
        versions.unit,
        Some(preview.validated_unit().unwrap().as_unit().version)
    );
    assert_eq!(
        versions.summary_schema,
        nera::verifier::summary::SUMMARY_SCHEMA_VERSION
    );
    assert_eq!(
        versions.relation_kernel,
        nera::verifier::relation::RELATION_KERNEL_VERSION
    );
    assert!(!versions.external_solver);
    assert!(
        preview
            .implementation_trust_boundary()
            .contains(&TrustedComponent::Frontend)
    );
    assert!(NATIVE_EXECUTION_BOUNDARY.contains(&TrustedComponent::Backend));
}

#[test]
fn refuted_and_unknown_are_completed_analysis_not_unsupported_or_executable_witnesses() {
    for (text, status) in [
        (
            "fn main()->u64 { let a=[42]; let i=2usize; return a[i]; }",
            ObligationStatus::Refuted,
        ),
        (
            "fn get(i:usize)->u64 { let a=[42]; return a[i]; }",
            ObligationStatus::Unknown,
        ),
    ] {
        let preview = verify_source(&source(text), Default::default());
        assert_eq!(preview.outcome(), PreviewOutcome::Unproved, "{preview:?}");
        assert!(preview.failure().is_none());
        assert!(preview.obligations().unwrap().any(|o| o.status() == status));
        assert!(!preview.diagnostics().unwrap().is_empty());
        assert!(!preview.is_checked());
    }
}

#[test]
fn missing_frontend_and_analysis_results_are_not_zero_obligation_success() {
    for source in [
        source(""),
        source("fn main( {"),
        SourceFile::new("invalid.nera", vec![255]),
    ] {
        let preview = verify_source(&source, Default::default());
        assert_eq!(
            preview.outcome(),
            PreviewOutcome::Rejected(PreviewStage::Frontend)
        );
        assert!(preview.counts().is_none());
        assert!(preview.obligations().is_none());
        assert!(preview.trust_report().is_none());
        assert_eq!(preview.versions().runtime, None);
        assert!(preview.validated_unit().is_none());
        assert!(!preview.frontend_issues().is_empty());
    }
    let preview = verify_source(&source("fn 名字()->u64 { return 42; }"), Default::default());
    assert_eq!(
        preview.outcome(),
        PreviewOutcome::Unsupported {
            stage: PreviewStage::Frontend,
            kind: CapabilityFailureKind::RuntimeSemanticsUnsupported
        }
    );
    assert!(preview.verification().is_none());
}

#[test]
fn validation_and_resolution_remain_separate_and_never_claim_frontend_acceptance() {
    let original = raw("fn main()->u64 { return f(); } fn f()->u64 { return 42; }");
    let mut invalid = original.clone();
    invalid.runtime.entry = VirFunctionId::new(999);
    let report = verify_unit(invalid.clone(), Default::default());
    preview_checks::observe(&report);
    assert_eq!(
        report.outcome(),
        PreviewOutcome::Rejected(PreviewStage::Validation)
    );
    assert!(report.matches_unit(&invalid, Default::default()));
    assert!(report.versions().unit.is_none());
    assert!(matches!(
        report.failure(),
        Some(PreviewFailure::Validation(_))
    ));
    let mut external = original;
    for instruction in external
        .runtime
        .functions
        .iter_mut()
        .flat_map(|f| &mut f.blocks)
        .flat_map(|b| &mut b.instructions)
    {
        if let VirInstruction::Call { target, .. } = &mut instruction.instruction {
            target.symbol = "foreign".into();
        }
    }
    let report = verify_unit(external, Default::default());
    preview_checks::observe(&report);
    assert_eq!(
        report.outcome(),
        PreviewOutcome::Unsupported {
            stage: PreviewStage::Resolution,
            kind: CapabilityFailureKind::RuntimeSemanticsUnsupported
        }
    );
    assert_eq!(report.frontend_status(), None);
    assert!(report.source().is_none());
    assert!(report.validated_unit().is_some());
    assert!(!report.is_resolved());
    assert!(report.counts().is_none());
    assert!(matches!(
        report.failure(),
        Some(PreviewFailure::Resolution(_))
    ));
}

#[test]
fn mandatory_budgets_abort_analysis_but_summary_precision_loss_can_keep_skeleton_success() {
    for config in [
        CfgAnalysisConfig {
            max_block_visits: 0,
            ..Default::default()
        },
        CfgAnalysisConfig {
            max_relation_evidence: 0,
            ..Default::default()
        },
    ] {
        let report = verify_source(&source(SAFE), config);
        assert_eq!(report.outcome(), PreviewOutcome::BudgetAborted);
        assert!(report.is_resolved());
        assert!(report.versions().runtime.is_some());
        assert!(report.counts().is_none());
        assert!(report.verification().is_none());
        assert_eq!(report.config(), config);
    }
    let config = CfgAnalysisConfig {
        summary_limits: nera::verifier::summary::SccLimits {
            max_iterations: 0,
            ..Default::default()
        },
        ..Default::default()
    };
    for (text, expected) in [
        (
            "fn main()->u64 { return f(0); } fn f(n:u64)->u64 { if n==3 { return 42; } return f(n+1); }",
            PreviewOutcome::Checked,
        ),
        (
            "fn main()->u64 { let a=[42]; return a[f(0)]; } fn f(n:u64)->usize { if n==3 { return 0usize; } return f(n+1); }",
            PreviewOutcome::Unproved,
        ),
    ] {
        let report = verify_source(&source(text), config);
        assert_eq!(report.outcome(), expected, "{report:?}");
        assert!(report.counts().unwrap().summaries_unknown > 0);
        assert!(report.failure().is_none());
        assert_eq!(
            report.is_checked(),
            report.verification().unwrap().is_memory_checked_core0()
        );
    }
}

#[test]
fn spec_proofs_trust_and_contract_analysis_error_have_distinct_accounting() {
    let base = raw("fn main()->u64 { return 42; }");
    for truth in [true, false] {
        let mut unit = base.clone();
        append_logic(&mut unit, truth, false);
        let report = verify_unit(unit, Default::default());
        preview_checks::observe(&report);
        assert_eq!(
            report.outcome(),
            if truth {
                PreviewOutcome::Checked
            } else {
                PreviewOutcome::Unproved
            }
        );
        assert_eq!(report.counts().unwrap().proofs.total(), 1);
        assert_eq!(report.counts().unwrap().proofs.refuted, usize::from(!truth));
        assert!(report.trust_report().unwrap().entries().is_empty());
        let rendered = render_text(&report, TextReportMode::Explain);
        assert_eq!(rendered.matches("[Spec/").count(), 1);
        assert!(rendered.contains(if truth {
            "[Spec/Proven]"
        } else {
            "[Spec/Refuted]"
        }));
    }
    let mut trusted = base.clone();
    append_logic(&mut trusted, true, true);
    let report = verify_unit(trusted, Default::default());
    preview_checks::observe(&report);
    assert!(report.is_checked());
    assert_eq!(report.trust_report().unwrap().entries().len(), 1);
    for mode in [TextReportMode::Summary, TextReportMode::Explain] {
        let rendered = render_text(&report, mode);
        assert!(rendered.contains("explicit trust entries: 1"));
        assert!(rendered.contains("[trust] registered assumption: EntryPointAssumption"));
        assert!(!rendered.contains("[Spec/Proven]"));
    }
    assert_eq!(
        report.counts().unwrap().proofs.total(),
        0,
        "trust is not a proved obligation"
    );
    assert!(
        !report
            .implementation_trust_boundary()
            .contains(&TrustedComponent::Frontend)
    );
    let mut unsupported_contract = base;
    append_logic(&mut unsupported_contract, true, false);
    let contract = unsupported_contract.runtime.functions[0].contract;
    let clause = unsupported_contract
        .specs
        .proves_mut()
        .pop()
        .unwrap()
        .clause;
    let c = &mut unsupported_contract.specs.clauses_mut()[clause.get() as usize];
    c.owner = VirSpecClauseOwner::Contract {
        contract,
        position: VirContractPosition::Ensures,
    };
    c.location = VirSpecLocation::FunctionResult {
        function: VirFunctionId::new(0),
    };
    unsupported_contract
        .specs
        .contract_mut(contract)
        .unwrap()
        .clauses
        .push(clause);
    let report = verify_unit(unsupported_contract, Default::default());
    preview_checks::observe(&report);
    assert_eq!(report.outcome(), PreviewOutcome::AnalysisFailed);
    assert!(report.is_resolved());
    assert!(matches!(
        report.failure(),
        Some(PreviewFailure::Verification(
            VerificationError::ContractInstantiation
        ))
    ));
    assert!(report.counts().is_none());
    assert!(report.trust_report().is_none());
    let rendered = render_text(&report, TextReportMode::Summary);
    assert!(rendered.contains("AnalysisFailed"));
    assert!(rendered.contains("[analysis] validated VIR contract table"));
}

#[test]
fn exact_identity_and_effective_configuration_reject_stale_inputs() {
    let input = source(SAFE);
    let report = verify_source(&input, Default::default());
    assert!(report.matches_source(&input, Default::default()));
    let changed = SourceFile::new(input.path(), [input.bytes(), b"\n"].concat());
    assert!(!report.matches_source(&changed, Default::default()));
    assert!(!report.matches_source(
        &SourceFile::new("other.nera", input.bytes()),
        Default::default()
    ));
    assert!(!report.matches_source(
        &input,
        CfgAnalysisConfig {
            max_block_visits: 1,
            ..Default::default()
        }
    ));
    let mut unit = report.validated_unit().unwrap().as_unit().clone();
    assert!(report.matches_unit(&unit, Default::default()));
    unit.runtime
        .functions
        .last_mut()
        .unwrap()
        .name
        .push_str("_changed");
    assert!(!report.matches_unit(&unit, Default::default()));
}

fn append_logic(unit: &mut VirUnit, value: bool, trust: bool) {
    let function = VirFunctionId::new(0);
    let origin = unit
        .source_map
        .origin_at(VirLocation::FunctionEntry { function })
        .unwrap()
        .id;
    let term = VirSpecTermId::new(unit.specs.terms().len() as u32);
    let clause = VirSpecClauseId::new(unit.specs.clauses().len() as u32);
    let proof = VirSpecProveId::new(unit.specs.proves().len() as u32);
    let entry = VirTrustEntryId::new(unit.specs.trust_entries().len() as u32);
    let location = VirSpecLocation::FunctionEntry { function };
    unit.specs.terms_mut().push(VirSpecTerm {
        id: term,
        clause,
        ty: VirSpecType::Bool,
        kind: VirSpecTermKind::Bool(value),
        origin,
    });
    unit.specs.clauses_mut().push(VirSpecClause {
        id: clause,
        owner: if trust {
            VirSpecClauseOwner::TrustEntry(entry)
        } else {
            VirSpecClauseOwner::Prove(proof)
        },
        location,
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic { root: term },
    });
    if trust {
        unit.specs.trust_entries_mut().push(VirTrustEntry {
            id: entry,
            scope: VirTrustScope::FunctionEntry { function },
            policy: VirTrustPolicyKind::EntryPointAssumption,
            clause,
            origin,
        });
    } else {
        unit.specs.proves_mut().push(VirSpecProve {
            id: proof,
            function,
            location,
            clause,
            origin,
        });
    }
}
