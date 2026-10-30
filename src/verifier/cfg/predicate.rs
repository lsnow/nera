//! Located Spec effects participate in the same CFG transfer and closure replay.
use super::*;
use crate::VirPredicateActionKind as Action;
use crate::verifier::{
    PredicateBinding, PredicateDefinition, PredicateEffect, PredicateHolder,
    check_predicate_evidence, transfer_predicate,
};

pub(super) fn apply(
    program: &ResolvedVirUnit<'_>,
    location: VirLocation,
    state: &mut ResourceState,
) -> Result<Vec<CfgObligation>, CfgAnalysisError> {
    let mut obligations = Vec::new();
    if !state.path_condition().is_reachable() {
        return Ok(obligations);
    }
    for action in program
        .as_unit()
        .specs
        .predicate_actions()
        .iter()
        .filter(|a| a.location == location)
    {
        let invalid = || CfgAnalysisError::InvalidFinding { location };
        let predicate = &program.as_unit().specs.predicates()[action.predicate.get() as usize];
        let module = program
            .as_unit()
            .source_map
            .source_span_for_origin(predicate.origin)
            .ok_or_else(invalid)?
            .source
            .get();
        let definition =
            PredicateDefinition::from_vir(&program.as_unit().memory, predicate, module)
                .map_err(|_| invalid())?;
        let bindings = |bindings: &[crate::VirPredicateBinding]| {
            bindings
                .iter()
                .map(|b| PredicateBinding {
                    pointer: b.pointer,
                    permission: b.permission,
                })
                .collect()
        };
        let effect = match &action.kind {
            Action::Fold {
                holder,
                bindings: b,
            } => PredicateEffect::FoldWithWitnesses {
                holder: PredicateHolder(*holder),
                bindings: bindings(b),
                witnesses: action.witnesses.clone(),
            },
            Action::Unfold {
                holder,
                bindings: b,
            } => PredicateEffect::UnfoldNamed {
                holder: PredicateHolder(*holder),
                bindings: bindings(b),
                action: action.id,
            },
            Action::Move {
                source,
                destination,
            } => PredicateEffect::Move {
                source: PredicateHolder(*source),
                destination: PredicateHolder(*destination),
            },
            Action::Finish { holder } => PredicateEffect::Finish {
                holder: PredicateHolder(*holder),
            },
        };
        let effect = if let Action::Unfold { holder, .. } | Action::Finish { holder } = &action.kind
        {
            PredicateEffect::WithArguments {
                holder: PredicateHolder(*holder),
                arguments: action.witnesses.clone(),
                effect: Box::new(effect),
            }
        } else {
            effect
        };
        let status = match transfer_predicate(state, &definition, module, &effect) {
            Ok(evidence) => {
                check_predicate_evidence(state, &evidence).map_err(|_| invalid())?;
                *state = evidence.output;
                ObligationStatus::Proven
            }
            // Missing facts and unsupported forms cannot establish an effect.
            // Keep the obligation even if later runtime operations succeed.
            Err(_) => ObligationStatus::Unknown,
        };
        let finding = VerifierFinding::predicate_action(program, action.id).ok_or_else(invalid)?;
        obligations.push(CfgObligation {
            block: location.block().ok_or_else(invalid)?,
            origin: CfgObligationOrigin::PredicateAction { id: action.id },
            finding,
            obligation: ResourceObligation::new(
                ResourceObligationKind::PredicateActionValid { action: action.id },
                status,
                finding.source_span(),
            ),
        });
    }
    Ok(obligations)
}
