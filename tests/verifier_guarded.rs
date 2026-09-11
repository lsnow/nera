#[path = "support/resource_payload_program.rs"]
mod resource_payload_program;

use nera::{
    CfgAnalysisConfig, GuardedStatePrecisionLoss, ObligationStatus, PathFact,
    ResourceObligationKind, VirBlockId, VirFunctionId, analyze_function_cfg,
    analyze_function_cfg_with_config,
};
use resource_payload_program::ConditionalUse;

#[test]
fn matching_guard_preserves_conditional_owner_exactly_once() {
    let validated = resource_payload_program::conditional_unit(ConditionalUse::MatchingGuard)
        .into_validated()
        .expect("conditional resource fixture validates");
    let resolved = validated.resolve().expect("conditional fixture resolves");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("guarded resource analysis converges");

    assert!(
        analysis.all_obligations_proven(),
        "matching guard must discharge every owner obligation: {:#?}",
        analysis.obligations()
    );
    let join = analysis.block(VirBlockId::new(3)).expect("join block");
    assert_eq!(join.entry_conditional_state().cases().len(), 2);
    assert!(join.entry_conditional_state().cases().iter().any(|case| {
        case.path_condition()
            .implies(PathFact::boolean(nera::VirValueId::new(32), true))
    }));
    assert!(join.entry_conditional_state().cases().iter().any(|case| {
        case.path_condition()
            .implies(PathFact::boolean(nera::VirValueId::new(32), false))
    }));
    assert_eq!(
        analysis
            .block(VirBlockId::new(5))
            .expect("guarded take block")
            .entry_conditional_state()
            .cases()
            .len(),
        1
    );
}

#[test]
fn unconditional_or_wrong_guard_cannot_recover_a_maybe_owner() {
    for conditional_use in [
        ConditionalUse::Unconditional,
        ConditionalUse::UnrelatedGuard,
    ] {
        let validated = resource_payload_program::conditional_unit(conditional_use)
            .into_validated()
            .expect("negative conditional fixture validates");
        let resolved = validated.resolve().expect("negative fixture resolves");
        let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
            .expect("negative guarded analysis converges");
        assert!(!analysis.all_obligations_proven());
        assert!(
            analysis.obligations().iter().any(|record| {
                matches!(
                    record.obligation().kind(),
                    ResourceObligationKind::ResourcePayloadAvailable { .. }
                ) && record.obligation().status() != ObligationStatus::Proven
            }),
            "{conditional_use:?}: {:#?}",
            analysis.obligations()
        );
        if conditional_use == ConditionalUse::UnrelatedGuard {
            assert!(
                analysis
                    .guarded_precision_losses()
                    .values()
                    .any(|losses| losses.contains(&GuardedStatePrecisionLoss::GuardProjection)),
                "dropping the original branch value at a CFG edge must be auditable"
            );
        }
    }
}

#[test]
fn case_budget_collapses_to_unknown_without_granting_owner_authority() {
    let validated = resource_payload_program::conditional_unit(ConditionalUse::MatchingGuard)
        .into_validated()
        .expect("budget fixture validates");
    let resolved = validated.resolve().expect("budget fixture resolves");
    let analysis = analyze_function_cfg_with_config(
        &resolved,
        VirFunctionId::new(0),
        CfgAnalysisConfig {
            max_guarded_cases_per_block: 1,
            ..CfgAnalysisConfig::default()
        },
    )
    .expect("budgeted guarded analysis converges");

    assert!(!analysis.all_obligations_proven());
    assert!(
        analysis
            .guarded_precision_losses()
            .values()
            .any(|losses| { losses.contains(&GuardedStatePrecisionLoss::CaseBudget) })
    );
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::ResourcePayloadAvailable { .. }
        ) && record.obligation().status() == ObligationStatus::Unknown
    }));
}

#[test]
fn unknown_obligation_replays_saved_predecessor_guards_with_a_fixed_budget() {
    let validated = resource_payload_program::scalar_refinement_unit()
        .into_validated()
        .expect("scalar refinement fixture validates");
    let resolved = validated.resolve().expect("refinement fixture resolves");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("obligation-directed refinement converges");
    let replay = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("deterministic replay converges");

    assert_eq!(analysis, replay);

    assert!(analysis.refined_blocks().contains(&VirBlockId::new(3)));
    assert_eq!(analysis.refinement_passes(), 1);
    assert_eq!(analysis.refinement_block_visits(), 2);
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::CheckTrue { .. }
        ) && record.obligation().status() == ObligationStatus::Refuted
    }));

    let budgeted = analyze_function_cfg_with_config(
        &resolved,
        VirFunctionId::new(0),
        CfgAnalysisConfig {
            max_refinement_passes: 0,
            ..CfgAnalysisConfig::default()
        },
    )
    .expect("zero-refinement budget remains a valid analysis");
    assert!(budgeted.refined_blocks().is_empty());
    assert!(
        budgeted
            .guarded_precision_losses()
            .values()
            .any(|losses| { losses.contains(&GuardedStatePrecisionLoss::RefinementPassBudget) })
    );
    assert!(budgeted.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::CheckTrue { .. }
        ) && record.obligation().status() == ObligationStatus::Unknown
    }));

    let visit_budgeted = analyze_function_cfg_with_config(
        &resolved,
        VirFunctionId::new(0),
        CfgAnalysisConfig {
            max_refinement_block_visits: 1,
            ..CfgAnalysisConfig::default()
        },
    )
    .expect("insufficient replay-visit budget remains a valid analysis");
    assert!(visit_budgeted.refined_blocks().is_empty());
    assert_eq!(visit_budgeted.refinement_block_visits(), 0);
    assert!(
        visit_budgeted
            .guarded_precision_losses()
            .values()
            .any(|losses| losses.contains(&GuardedStatePrecisionLoss::RefinementVisitBudget))
    );
    assert!(visit_budgeted.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::CheckTrue { .. }
        ) && record.obligation().status() == ObligationStatus::Unknown
    }));
}
