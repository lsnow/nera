//! SCC orchestration only: bodies still use the canonical verifier; joins and
//! inclusion live in the summary domain. No provisional report is published.
use super::*;
use crate::verifier::summary::recursive as domain;
use crate::verifier::summary::{
    FunctionSummary, SccAnalysis, SccOutcome, SummaryRegistry, SummaryState,
};
use std::sync::Arc;

pub(super) fn analyze(
    program: &ResolvedVirUnit<'_>,
    members: &[VirFunctionId],
    contracts: &super::super::contract::InstantiatedContracts,
    config: CfgAnalysisConfig,
    published: &mut SummaryRegistry,
    unit: &Arc<str>,
) -> Result<BTreeMap<VirFunctionId, FunctionVerification>, VerificationError> {
    let mut fallback = BTreeMap::new();
    for &id in members {
        fallback.insert(
            id,
            analyze_one(program, id, contracts, config, published, unit)?,
        );
    }
    let limits = config.summary_limits;
    let mut audit = SccAnalysis {
        final_candidates: Arc::from([]),
        baseline_block_visits: fallback
            .values()
            .map(|f| {
                f.cfg()
                    .block_visits()
                    .saturating_add(f.cfg().refinement_block_visits())
            })
            .sum(),
        body_block_visits: 0,
        body_queries: 0,
        body_call_evidence: 0,
        members: members.to_vec(),
        iterations: 0,
        body_analyses: 0,
        peak_worlds: 0,
        peak_candidate_bytes: 0,
        widenings: 0,
        final_recheck: false,
        outcome: SccOutcome::Unsupported,
    };
    let name = |id| {
        program
            .runtime()
            .functions
            .iter()
            .find(|f| f.id == id)
            .unwrap()
            .name
            .clone()
    };
    let mut candidates = BTreeMap::<String, FunctionSummary>::new();
    if members.len() > limits.max_functions {
        audit.outcome = SccOutcome::FunctionBudget;
    } else {
        for (&id, result) in &fallback {
            let Some(candidate) = domain::seed(&result.summary) else {
                break;
            };
            candidates.insert(name(id), candidate);
        }
        if candidates.len() == members.len() {
            let mut final_pass = false;
            audit.outcome = SccOutcome::IterationBudget;
            loop {
                audit.peak_worlds = audit
                    .peak_worlds
                    .max(candidates.values().map(domain::world_count).sum());
                audit.peak_candidate_bytes = audit.peak_candidate_bytes.max(
                    candidates
                        .values()
                        .map(domain::candidate_bytes)
                        .fold(0usize, usize::saturating_add),
                );
                if candidates.values().any(|s| !domain::fits(s, limits))
                    || audit.peak_worlds > limits.max_worlds
                    || audit.peak_candidate_bytes > limits.max_candidate_bytes
                {
                    audit.outcome = SccOutcome::StateBudget;
                    break;
                }
                if audit.body_analyses.saturating_add(members.len()) > limits.max_body_analyses {
                    audit.outcome = SccOutcome::AnalysisBudget;
                    break;
                }
                if !final_pass && audit.iterations >= limits.max_iterations {
                    break;
                }
                if final_pass {
                    audit.final_recheck = true;
                } else {
                    audit.iterations += 1;
                }
                // Every member sees the same immutable candidate environment.
                // analyze_one also rechecks explicit requires at every call,
                // ensures at every return and the whole-body effect frame.
                // No declaration is converted into an independent assumption.
                let trial = published.trial(&candidates);
                let mut observed = BTreeMap::new();
                let mut complete = true;
                for &id in members {
                    audit.body_analyses += 1;
                    let Ok(result) = analyze_one(program, id, contracts, config, &trial, unit)
                    else {
                        complete = false;
                        break;
                    };
                    audit.body_block_visits = audit
                        .body_block_visits
                        .saturating_add(result.cfg().block_visits())
                        .saturating_add(result.cfg().refinement_block_visits());
                    audit.body_queries = audit
                        .body_queries
                        .saturating_add(result.cfg().relation_queries().len());
                    audit.body_call_evidence = audit.body_call_evidence.saturating_add(
                        result
                            .summary()
                            .call_uses
                            .iter()
                            .map(|c| c.observation.weight())
                            .sum::<usize>(),
                    );
                    if result.summary.state != SummaryState::Candidate || !result.is_verified() {
                        complete = false;
                    }
                    observed.insert(id, result);
                }
                if !complete {
                    audit.outcome = SccOutcome::Unsupported;
                    break;
                }
                let covered = observed
                    .iter()
                    .all(|(&id, r)| domain::covers(&candidates[&name(id)], &r.summary));
                if final_pass {
                    if !covered {
                        audit.outcome = SccOutcome::NotCovered;
                        break;
                    }
                    audit.outcome = SccOutcome::Closed;
                    audit.final_candidates = members
                        .iter()
                        .map(|id| domain::SccCandidate {
                            function: *id,
                            normal_returns: candidates[&name(*id)].normal_returns.clone(),
                        })
                        .collect::<Vec<_>>()
                        .into();
                    let mut ready = observed
                        .iter()
                        .map(|(&id, r)| (name(id), r.summary.clone()))
                        .collect();
                    for summary in BTreeMap::<String, FunctionSummary>::values_mut(&mut ready) {
                        domain::record(summary, &audit);
                    }
                    if !published.publish_component(&mut ready, &candidates) {
                        audit.outcome = SccOutcome::NotCovered;
                        break;
                    }
                    for (&id, result) in &mut observed {
                        result.summary = ready.remove(&name(id)).unwrap();
                        domain::record(&mut result.summary, &audit);
                    }
                    return Ok(observed);
                }
                if covered {
                    final_pass = true;
                    continue;
                }
                for (&id, result) in &observed {
                    audit.widenings += domain::join(
                        candidates.get_mut(&name(id)).unwrap(),
                        &result.summary,
                        audit.iterations > config.widen_after_updates,
                    );
                }
            }
        }
    }
    // No hypothesis, proof or diagnostic from an unsuccessful trial survives.
    audit.final_candidates = Arc::from([]);
    for result in fallback.values_mut() {
        domain::record(&mut result.summary, &audit);
    }
    Ok(fallback)
}
