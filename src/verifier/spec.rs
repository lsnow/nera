use std::collections::BTreeSet;

use crate::{
    ResolvedVirUnit, VirFunction, VirFunctionId, VirLocation, VirSpecClauseId, VirSpecClauseKind,
    VirSpecLocation, VirSpecProveId, VirTrustEntryId, VirTrustPolicyKind, VirTrustScope,
};

use super::cfg::{FunctionCfgAnalysis, FunctionReturnState};
use super::finding::VerifierFinding;
use super::resource::AbstractBool;
use super::transfer::ObligationStatus;
use super::vc::{
    SnapshotValues, VcArena, VcLimits, VcNormalizer, VcQueryBudget, VcTermId, evaluate_bool,
};

/// Final result of one typed `Prove` obligation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SpecProof {
    prove: VirSpecProveId,
    finding: VerifierFinding,
    status: ObligationStatus,
}

impl SpecProof {
    #[must_use]
    pub const fn prove(self) -> VirSpecProveId {
        self.prove
    }

    #[must_use]
    pub const fn function(self) -> VirFunctionId {
        self.finding.site().function()
    }

    #[must_use]
    pub const fn location(self) -> VirSpecLocation {
        match self.finding.site() {
            super::finding::VerifierFindingSite::Spec { location, .. } => location,
            super::finding::VerifierFindingSite::Runtime(_) => {
                unreachable!()
            }
        }
    }

    #[must_use]
    pub const fn status(self) -> ObligationStatus {
        self.status
    }

    #[must_use]
    pub const fn finding(self) -> VerifierFinding {
        self.finding
    }

    #[must_use]
    pub const fn source_span(self) -> crate::ByteSpan {
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
) -> Option<Vec<SpecProof>> {
    let limits = VcLimits::default();
    let mut normalizer = VcNormalizer::new(limits);
    let mut query_budget = VcQueryBudget::new(limits);
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
        let VirSpecClauseKind::Logic { root } = clause.kind else {
            unreachable!("validated Prove owns a logic clause")
        };
        let normalized = normalizer.normalize(unit, root);
        let trusted = trusted_terms(unit, function.id, prove.location, &mut normalizer);
        let status = normalized.ok().zip(trusted.ok()).map_or(
            ObligationStatus::Unknown,
            |(term, trusted)| {
                prove_at_location(
                    function,
                    cfg,
                    prove.location,
                    normalizer.arena(),
                    term,
                    &trusted,
                    &mut query_budget,
                )
            },
        );
        proofs.push(SpecProof {
            prove: prove.id,
            finding: VerifierFinding::prove(unit, prove.id)?,
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

fn prove_at_location(
    function: &VirFunction,
    cfg: &FunctionCfgAnalysis,
    location: VirSpecLocation,
    arena: &VcArena,
    term: VcTermId,
    trusted: &BTreeSet<VcTermId>,
    budget: &mut VcQueryBudget,
) -> ObligationStatus {
    match location {
        VirSpecLocation::FunctionEntry { .. } => status(evaluate_bool(
            arena,
            term,
            trusted,
            SnapshotValues::State(cfg.function_entry_state()),
            function,
            budget,
        )),
        VirSpecLocation::FunctionResult { .. } => aggregate_results(
            cfg.returns()
                .iter()
                .map(|returned| prove_return(arena, term, trusted, returned, function, budget)),
        ),
        VirSpecLocation::Runtime(location) => {
            let Some(block) = location.block().and_then(|id| cfg.block(id)) else {
                return if matches!(location, VirLocation::FunctionEntry { .. }) {
                    status(evaluate_bool(
                        arena,
                        term,
                        trusted,
                        SnapshotValues::State(cfg.function_entry_state()),
                        function,
                        budget,
                    ))
                } else {
                    ObligationStatus::Unknown
                };
            };
            let state = match location {
                VirLocation::BlockEntry { .. } | VirLocation::BlockParameter { .. } => {
                    block.entry_state()
                }
                VirLocation::Terminator { .. } => block.exit_state(),
                VirLocation::Instruction { ordinal, .. } => block
                    .instruction_states()
                    .get(ordinal as usize)
                    .unwrap_or_else(|| block.exit_state()),
                VirLocation::CallEdge { instruction, .. } => block
                    .instruction_states()
                    .get(instruction as usize)
                    .unwrap_or_else(|| block.exit_state()),
                VirLocation::FunctionEntry { .. } => unreachable!(),
            };
            status(evaluate_bool(
                arena,
                term,
                trusted,
                SnapshotValues::State(state),
                function,
                budget,
            ))
        }
    }
}

fn prove_return(
    arena: &VcArena,
    term: VcTermId,
    trusted: &BTreeSet<VcTermId>,
    returned: &FunctionReturnState,
    function: &VirFunction,
    budget: &mut VcQueryBudget,
) -> ObligationStatus {
    status(evaluate_bool(
        arena,
        term,
        trusted,
        SnapshotValues::Results(returned.values()),
        function,
        budget,
    ))
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
