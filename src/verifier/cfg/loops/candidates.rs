//! Obligation-directed candidate elimination. Each attempt starts from the
//! original entry; no hypothetical state or evidence crosses attempt boundaries.
use super::*;
use crate::{VirSpecClauseOrigin, VirSpecLoopInvariant, VirSpecLoopInvariantId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopCandidateAttempt {
    pub selected: Vec<VirSpecLoopInvariantId>,
    pub rejected: Vec<CfgObligation>,
    pub error: Option<CfgAnalysisError>,
    pub block_visits: u64,
}

pub(super) fn enabled(
    unit: &ResolvedVirUnit<'_>,
    i: &VirSpecLoopInvariant,
    selected: &BTreeSet<VirSpecLoopInvariantId>,
) -> bool {
    !matches!(
        unit.as_unit().specs.clause(i.clause).unwrap().origin,
        VirSpecClauseOrigin::InferredLoop { .. }
    ) || selected.contains(&i.id)
}

pub(in crate::verifier::cfg) fn analyze(
    unit: &ResolvedVirUnit<'_>,
    function: VirFunctionId,
    entry: &ResourceState,
    config: CfgAnalysisConfig,
    contracts: Option<&InstantiatedContracts>,
    registry: Option<&super::super::super::summary::SummaryRegistry>,
) -> Result<FunctionCfgAnalysis, CfgAnalysisError> {
    let mut baseline = analyze_function_cfg_attempt(
        unit,
        function,
        entry,
        config,
        contracts,
        registry,
        &BTreeSet::new(),
    );
    if baseline.as_ref().is_ok_and(|a| {
        a.all_obligations_proven()
            && a.summary_pending().is_empty()
            && a.widened_blocks().is_empty()
    }) {
        return baseline;
    }
    let mut candidates: Vec<_> = unit
        .as_unit()
        .specs
        .loop_invariants()
        .iter()
        .filter(|i| {
            i.function == function
                && matches!(
                    unit.as_unit().specs.clause(i.clause).unwrap().origin,
                    VirSpecClauseOrigin::InferredLoop { .. }
                )
        })
        .collect();
    // Candidate-table order is not a precision knob. Clause order is canonical
    // in the producer and independent of invariant identity renumbering.
    candidates.sort_by_key(|i| (i.boundary.as_ref().unwrap().header, i.clause));
    let mut selected: BTreeSet<_> = candidates
        .into_iter()
        .take(config.max_loop_candidates.min(32))
        .map(|i| i.id)
        .collect();
    let mut attempts = Vec::new();
    let mut remaining = config.max_loop_candidate_block_visits;
    for _ in 0..config.max_loop_candidate_rounds.min(32) {
        if selected.is_empty() || remaining == 0 {
            break;
        }
        let attempt_config = CfgAnalysisConfig {
            max_block_visits: config.max_block_visits.min(remaining),
            ..config
        };
        let result = analyze_function_cfg_attempt(
            unit,
            function,
            entry,
            attempt_config,
            contracts,
            registry,
            &selected,
        );
        let visits = result
            .as_ref()
            .map_or(attempt_config.max_block_visits, |a| a.block_visits());
        remaining = remaining.saturating_sub(visits);
        let rejected: Vec<_> = result.as_ref().map_or_else(
            |_| Vec::new(),
            |a| {
                a.obligations()
                    .iter()
                    .chain(a.summary_pending())
                    .filter(|o| !o.obligation().is_proven())
                    .copied()
                    .collect()
            },
        );
        attempts.push(LoopCandidateAttempt {
            selected: selected.iter().copied().collect(),
            rejected: rejected.clone(),
            error: result.as_ref().err().cloned(),
            block_visits: visits,
        });
        if let Ok(mut checked) = result
            && checked.all_obligations_proven()
            && checked.summary_pending().is_empty()
        {
            checked.loop_candidate_attempts = attempts;
            return Ok(checked);
        }
        let before = selected.len();
        for o in rejected {
            match o.obligation().kind() {
                ResourceObligationKind::LoopInvariantEstablished { invariant, .. } => {
                    selected.remove(&invariant);
                }
                ResourceObligationKind::LoopResourcesPreserved { invariant } => {
                    let header = unit.as_unit().specs.loop_invariants()[invariant.get() as usize]
                        .boundary
                        .as_ref()
                        .unwrap()
                        .header;
                    selected.retain(|id| {
                        unit.as_unit().specs.loop_invariants()[id.get() as usize]
                            .boundary
                            .as_ref()
                            .unwrap()
                            .header
                            != header
                    });
                }
                _ => {}
            }
        }
        if selected.len() == before {
            break;
        }
    }
    if let Ok(analysis) = &mut baseline {
        analysis.loop_candidate_attempts = attempts;
    }
    baseline
}
