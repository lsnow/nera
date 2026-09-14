use std::collections::BTreeSet;
mod memory;
pub(super) mod separation;

use crate::{
    ResolvedVirUnit, VirFunction, VirFunctionId, VirLocation, VirSpecClauseId, VirSpecClauseKind,
    VirSpecLocation, VirSpecProveId, VirTrustEntryId, VirTrustPolicyKind, VirTrustScope,
};

use super::cfg::FunctionCfgAnalysis;
use super::finding::VerifierFinding;
use super::resource::AbstractBool;
use super::transfer::ObligationStatus;
use super::vc::{SnapshotValues, VcLimits, VcNormalizer, VcQueryBudget, VcTermId, evaluate_bool};

/// Final result of one typed `Prove` obligation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecFailure {
    InsufficientFacts,
    FalsePredicate,
    ResourceConflict,
    InvalidWitness,
    UnsupportedTheory,
    BudgetExceeded,
}

impl SpecFailure {
    pub(crate) const fn description(self) -> &'static str {
        match self {
            Self::InsufficientFacts => "insufficient current-state facts",
            Self::FalsePredicate => "logical predicate is false",
            Self::ResourceConflict => "resource state or permission conflict",
            Self::InvalidWitness => {
                "witness is unavailable, undefined or does not establish the body"
            }
            Self::UnsupportedTheory => "required theory or heap-value facts are not supported",
            Self::BudgetExceeded => "proof budget exhausted",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecProof {
    failure: Option<SpecFailure>,
    queries: Vec<super::relation::audit::QueryEvidence>,
    prove: VirSpecProveId,
    finding: VerifierFinding,
    status: ObligationStatus,
}

impl SpecProof {
    #[must_use]
    pub const fn failure(&self) -> Option<SpecFailure> {
        self.failure
    }
    #[must_use]
    pub fn relation_queries(&self) -> &[super::relation::audit::QueryEvidence] {
        &self.queries
    }
    #[must_use]
    pub const fn prove(&self) -> VirSpecProveId {
        self.prove
    }

    #[must_use]
    pub const fn function(&self) -> VirFunctionId {
        self.finding.site().function()
    }

    #[must_use]
    pub const fn location(&self) -> VirSpecLocation {
        match self.finding.site() {
            super::finding::VerifierFindingSite::Spec { location, .. } => location,
            super::finding::VerifierFindingSite::Runtime(_) => {
                unreachable!()
            }
        }
    }

    #[must_use]
    pub const fn status(&self) -> ObligationStatus {
        self.status
    }

    #[must_use]
    pub const fn finding(&self) -> VerifierFinding {
        self.finding
    }

    #[must_use]
    pub const fn source_span(&self) -> crate::ByteSpan {
        self.finding.source_span()
    }
}

/// One validated assumption that actually entered the proof environment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TrustReportEntry {
    id: VirTrustEntryId,
    scope: VirTrustScope,
    policy: VirTrustPolicyKind,
    clause: VirSpecClauseId,
    finding: VerifierFinding,
}

impl TrustReportEntry {
    #[must_use]
    pub const fn id(self) -> VirTrustEntryId {
        self.id
    }

    #[must_use]
    pub const fn scope(self) -> VirTrustScope {
        self.scope
    }

    #[must_use]
    pub const fn policy(self) -> VirTrustPolicyKind {
        self.policy
    }

    #[must_use]
    pub const fn clause(self) -> VirSpecClauseId {
        self.clause
    }

    #[must_use]
    pub const fn finding(self) -> VerifierFinding {
        self.finding
    }

    #[must_use]
    pub const fn origin(self) -> crate::VirOriginId {
        self.finding.origin()
    }

    #[must_use]
    pub const fn source_span(self) -> crate::ByteSpan {
        self.finding.source_span()
    }
}

pub(super) fn prove_function_specs(
    unit: &ResolvedVirUnit<'_>,
    function: &VirFunction,
    cfg: &FunctionCfgAnalysis,
    config: crate::CfgAnalysisConfig,
) -> Option<Vec<SpecProof>> {
    let limits = VcLimits::default();
    let mut normalizer = VcNormalizer::new(limits);
    let mut query_budget = VcQueryBudget::new(limits);
    query_budget.relation_limits = config.relation_limits;
    let mut proofs = Vec::new();

    for prove in unit
        .as_unit()
        .specs
        .proves()
        .iter()
        .filter(|prove| prove.function == function.id)
    {
        let clause = unit
            .as_unit()
            .specs
            .clause(prove.clause)
            .expect("validated Prove clause remains present");
        let contains_exists = if let VirSpecClauseKind::Assertion { root } = clause.kind {
            memory::contains_exists(unit, root, limits, &mut query_budget)
        } else {
            Some(false)
        };
        let finding = VerifierFinding::prove(unit, prove.id)?;
        let mut queries = Vec::new();
        let mut results = Vec::new();
        let mut failure = None;
        for (case_ordinal, values) in contexts_at_location(cfg, prove.location)
            .unwrap_or_default()
            .into_iter()
            .enumerate()
        {
            let mut case_failure = None;
            let mut result =
                if contains_exists.is_none() || query_budget.exhausted || normalizer.exhausted {
                    ObligationStatus::Unknown
                } else {
                    match clause.kind {
                        VirSpecClauseKind::Logic { root } => {
                            let normalized = normalizer.normalize(unit, root);
                            let trusted =
                                trusted_terms(unit, function.id, prove.location, &mut normalizer);
                            normalized.ok().zip(trusted.ok()).map_or(
                                ObligationStatus::Unknown,
                                |(term, trusted)| {
                                    status(evaluate_bool(
                                        normalizer.arena(),
                                        term,
                                        &trusted,
                                        values,
                                        function,
                                        &mut query_budget,
                                    ))
                                },
                            )
                        }
                        VirSpecClauseKind::Assertion { root } => {
                            let (result, reason) = memory::prove(
                                unit,
                                function,
                                root,
                                values,
                                &mut normalizer,
                                &mut query_budget,
                                config,
                            );
                            if !result.is_proven() {
                                case_failure = reason;
                            }
                            result
                        }
                        _ => ObligationStatus::Unknown,
                    }
                };
            // Drain each case separately; a shared budget does not merge proof
            // premises, resource ledgers, witnesses or audit case identities.
            let observations = std::mem::take(&mut query_budget.relations).finish();
            if observations.is_none() {
                result = ObligationStatus::Unknown;
                case_failure = Some(SpecFailure::BudgetExceeded);
            }
            let mut observations = observations.unwrap_or_default();
            if observations.len() > config.max_relation_evidence.saturating_sub(queries.len()) {
                query_budget.exhausted = true;
                case_failure = Some(SpecFailure::BudgetExceeded);
                result = ObligationStatus::Unknown;
                observations.clear();
                queries.clear();
            }
            queries.extend(
                observations
                    .into_iter()
                    .enumerate()
                    .map(
                        |(query_ordinal, query)| super::relation::audit::QueryEvidence {
                            config,
                            finding,
                            sources: vec![finding],
                            sources_truncated: true,
                            case_ordinal,
                            edge_ordinal: None,
                            query_ordinal,
                            query,
                        },
                    ),
            );
            results.push(result);
            if !result.is_proven() && (failure.is_none() || result == ObligationStatus::Refuted) {
                failure = Some(
                    case_failure.unwrap_or(if result == ObligationStatus::Refuted {
                        SpecFailure::FalsePredicate
                    } else {
                        SpecFailure::InsufficientFacts
                    }),
                );
            }
        }
        let mut status = aggregate_results(results.into_iter());
        // A bad chosen witness does not disprove all possible witnesses. This
        // also covers resource conflicts encountered outside its lexical body.
        if contains_exists == Some(true) && !status.is_proven() {
            status = ObligationStatus::Unknown;
            if failure == Some(SpecFailure::FalsePredicate) {
                failure = Some(SpecFailure::InvalidWitness);
            }
        }
        if !status.is_proven() && (query_budget.exhausted || normalizer.exhausted) {
            status = ObligationStatus::Unknown;
            failure = Some(SpecFailure::BudgetExceeded);
        }
        if !status.is_proven() && failure.is_none() {
            failure = Some(SpecFailure::InsufficientFacts);
        }
        proofs.push(SpecProof {
            failure,
            queries,
            prove: prove.id,
            finding,
            status,
        });
    }
    Some(proofs)
}

pub(super) fn collect_trust_entries(unit: &ResolvedVirUnit<'_>) -> Option<Vec<TrustReportEntry>> {
    unit.as_unit()
        .specs
        .trust_entries()
        .iter()
        .map(|entry| {
            Some(TrustReportEntry {
                id: entry.id,
                scope: entry.scope,
                policy: entry.policy,
                clause: entry.clause,
                finding: VerifierFinding::trust_entry(unit, entry.id)?,
            })
        })
        .collect()
}

fn trusted_terms(
    unit: &ResolvedVirUnit<'_>,
    function: VirFunctionId,
    location: VirSpecLocation,
    normalizer: &mut VcNormalizer,
) -> Result<BTreeSet<VcTermId>, ()> {
    let mut trusted = BTreeSet::new();
    for entry in
        unit.as_unit().specs.trust_entries().iter().filter(|entry| {
            entry.scope.function() == function && entry.scope.location() == location
        })
    {
        let clause = unit
            .as_unit()
            .specs
            .clause(entry.clause)
            .expect("validated trust clause remains present");
        let VirSpecClauseKind::Logic { root } = clause.kind else {
            unreachable!("validated trust entry owns a logic clause")
        };
        trusted.insert(normalizer.normalize(unit, root).map_err(|_| ())?);
    }
    Ok(trusted)
}

/// Final guarded cases only; no picking independent facts from merged branches.
fn contexts_at_location(
    cfg: &FunctionCfgAnalysis,
    location: VirSpecLocation,
) -> Option<Vec<SnapshotValues<'_>>> {
    match location {
        VirSpecLocation::FunctionEntry { .. }
        | VirSpecLocation::Runtime(VirLocation::FunctionEntry { .. }) => {
            Some(vec![SnapshotValues::State(cfg.function_entry_state())])
        }
        VirSpecLocation::FunctionResult { .. } => Some(
            cfg.returns()
                .iter()
                .map(|r| SnapshotValues::Results(r.values()))
                .collect(),
        ),
        VirSpecLocation::Runtime(location) => {
            let block = cfg.block(location.block()?)?;
            let state = match location {
                VirLocation::BlockEntry { .. } | VirLocation::BlockParameter { .. } => {
                    block.entry_conditional_state()
                }
                VirLocation::Terminator { .. } => block.exit_conditional_state(),
                VirLocation::Instruction { ordinal, .. } => block
                    .instruction_conditional_states()
                    .get(ordinal as usize)?,
                VirLocation::CallEdge { instruction, .. } => block
                    .instruction_conditional_states()
                    .get(instruction as usize)?,
                _ => return None,
            };
            Some(state.cases().iter().map(SnapshotValues::State).collect())
        }
    }
}

fn aggregate_results(results: impl Iterator<Item = ObligationStatus>) -> ObligationStatus {
    let mut any = false;
    let mut unknown = false;
    for result in results {
        any = true;
        match result {
            ObligationStatus::Refuted => return ObligationStatus::Refuted,
            ObligationStatus::Unknown => unknown = true,
            ObligationStatus::Proven => {}
        }
    }
    if !any || unknown {
        ObligationStatus::Unknown
    } else {
        ObligationStatus::Proven
    }
}

const fn status(value: Option<AbstractBool>) -> ObligationStatus {
    match value {
        Some(AbstractBool::True) => ObligationStatus::Proven,
        Some(AbstractBool::False) => ObligationStatus::Refuted,
        Some(AbstractBool::Unknown) | None => ObligationStatus::Unknown,
    }
}
