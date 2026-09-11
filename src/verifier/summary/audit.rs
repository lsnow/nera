//! Read-only interprocedural observations. Replay uses the canonical verifier,
//! including SCC final rechecks; this is not a proof importer or a second kernel.
use super::*;
use crate::verifier::{AbstractAllocationId, AbstractValue, PathCondition};
use crate::{ProgramVerification, VerifierFinding, VirValueId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MappingLoss {
    Guard,
    AliasFrame,
    AbiOrResource,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResourceSubstitution {
    pub formal: ResourceName,
    pub allocation: AbstractAllocationId,
    pub base: u64,
    pub size: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorldInstantiation {
    pub alternative: usize,
    pub return_evidence: usize,
    pub guard: Vec<SummaryGuard>,
    pub resources: Vec<ResourceSubstitution>,
    /// May-write/free invalidation footprint in this world's formal namespace.
    /// `resources` translates it into actual caller allocations and byte bases.
    pub effects: SummaryEffects,
    pub results: Vec<AbstractValue>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallObservation {
    pub finding: Option<VerifierFinding>,
    pub case_ordinal: usize,
    pub instance_site: u64,
    pub guard: PathCondition,
    pub dependency: Option<SummaryBinding>,
    pub arguments: Vec<(VirValueId, Option<AbstractValue>)>,
    pub mapping_loss: Option<MappingLoss>,
    pub worlds: Vec<WorldInstantiation>,
}
impl CallObservation {
    pub fn weight(&self) -> usize {
        1 + self.arguments.len()
            + self.guard.facts().map_or(0, |f| f.len())
            + self
                .worlds
                .iter()
                .map(|w| {
                    1 + w.guard.len()
                        + w.resources.len()
                        + w.results.len()
                        + effect_weight(&w.effects)
                })
                .sum::<usize>()
    }
}
fn effect_weight(e: &SummaryEffects) -> usize {
    let count = |e: &Knowledge<Vec<SummaryFootprint>>| match e {
        Knowledge::Known(v) => v.len(),
        Knowledge::Unknown => 1,
    };
    count(&e.may_read)
        + count(&e.may_write)
        + match &e.may_free {
            Knowledge::Known(v) => v.len(),
            Knowledge::Unknown => 1,
        }
}

/// Explanations of precision loss, not new resource obligations or permissions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SummaryIssue {
    BodyObligation,
    Projection,
    Guard,
    AliasFrame,
    AbiOrResourceMapping,
    DependencyNotClosed,
    RecursiveNotClosed,
    CallPrecondition,
    FreshInstance,
    EvidenceBudget,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SummaryMetrics {
    pub cfg_visits: u64,
    pub refinement_visits: u64,
    pub alternatives: usize,
    pub worlds: usize,
    pub resources: usize,
    pub footprint_entries: usize,
    pub call_observations: usize,
    pub instantiations: usize,
    pub summary_evidence_weight: usize,
    pub relation_queries: usize,
    pub provenance_events: usize,
    /// Deterministic diagnostic bytes, NOT process memory consumption.
    pub summary_bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionSummaryAudit {
    pub function: VirFunctionId,
    pub summary: FunctionSummary,
    /// Positional indices in SummaryFaults resolve to canonical source findings.
    pub requirements: Vec<(SummaryFinding, VerifierFinding)>,
    /// Published body worlds index this list. Inductive calls instead index
    /// SccAnalysis.final_candidates, which retains the exact final hypothesis.
    pub returns: Vec<VerifierFinding>,
    pub queries: Vec<crate::verifier::relation::audit::QueryEvidence>,
    pub relations: Vec<crate::verifier::relation::RelationEvidence>,
    pub provenance: Vec<crate::verifier::provenance::ProvenanceEvidence>,
    pub guarded_precision_losses: std::collections::BTreeMap<
        crate::VirBlockId,
        std::collections::BTreeSet<crate::GuardedStatePrecisionLoss>,
    >,
    pub metrics: SummaryMetrics,
    pub issues: Vec<SummaryIssue>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SummaryAudit {
    pub version: u32,
    pub functions: Vec<FunctionSummaryAudit>,
    pub diagnostics: Vec<crate::VerifierDiagnostic>,
    pub trust: crate::VerifierTrustReport,
    pub memory_checked: bool,
}
impl SummaryAudit {
    /// Projection only. An audit, even one reconstructed from a diagnostic DTO,
    /// cannot enter the private publication registry.
    pub fn from_report(report: &ProgramVerification) -> Self {
        #[cfg(test)]
        crate::verification::scale_tests::assert_not_rendering();
        let functions = report
            .functions()
            .iter()
            .map(|(&id, f)| {
                let s = f.summary();
                let cfg = f.cfg();
                let requirements = s
                    .faults
                    .requirements
                    .iter()
                    .map(|r| {
                        let finding = match r.kind {
                            EvidenceKind::Cfg => cfg.obligations()[r.index].finding(),
                            EvidenceKind::Historical => cfg.summary_pending()[r.index].finding(),
                            EvidenceKind::Postcondition => f.postconditions()[r.index].finding(),
                            EvidenceKind::Proof => f.proofs()[r.index].finding(),
                        };
                        (r.clone(), finding)
                    })
                    .collect();
                let mut metrics = SummaryMetrics {
                    cfg_visits: cfg.block_visits(),
                    refinement_visits: cfg.refinement_block_visits(),
                    call_observations: s.call_uses.len(),
                    instantiations: s.call_uses.iter().map(|c| c.observation.worlds.len()).sum(),
                    summary_evidence_weight: s
                        .call_uses
                        .iter()
                        .map(|c| c.observation.weight())
                        .sum(),
                    relation_queries: cfg.relation_queries().len(),
                    provenance_events: cfg.provenance_evidence().len(),
                    summary_bytes: s.stable_dump().len(),
                    ..Default::default()
                };
                if let Knowledge::Known(alternatives) = &s.normal_returns {
                    metrics.alternatives = alternatives.len();
                    for world in alternatives.iter().flat_map(|a| &a.worlds) {
                        metrics.worlds += 1;
                        metrics.resources += world.resources.len();
                        metrics.footprint_entries += effect_weight(&world.effects);
                    }
                }
                let mut issues = std::collections::BTreeSet::new();
                if cfg
                    .guarded_precision_losses()
                    .values()
                    .flatten()
                    .any(|loss| {
                        matches!(
                            loss,
                            crate::GuardedStatePrecisionLoss::CaseBudget
                                | crate::GuardedStatePrecisionLoss::GuardAtomBudget
                                | crate::GuardedStatePrecisionLoss::GuardProjection
                        )
                    })
                {
                    issues.insert(SummaryIssue::Guard);
                }
                if s.faults.requirements.iter().any(|r| !r.status.is_proven()) {
                    issues.insert(SummaryIssue::BodyObligation);
                }
                if matches!(s.state, SummaryState::Unknown(_)) {
                    issues.insert(SummaryIssue::Projection);
                }
                if !s.audit_complete {
                    issues.insert(SummaryIssue::EvidenceBudget);
                }
                if s.recursion
                    .as_ref()
                    .is_some_and(|r| r.outcome != SccOutcome::Closed)
                {
                    issues.insert(SummaryIssue::RecursiveNotClosed);
                }
                for call in &s.call_uses {
                    let issue = match call.outcome {
                        CallSummaryOutcome::Applied | CallSummaryOutcome::Inductive => None,
                        CallSummaryOutcome::NotClosed => Some(SummaryIssue::DependencyNotClosed),
                        CallSummaryOutcome::Preconditions => Some(SummaryIssue::CallPrecondition),
                        CallSummaryOutcome::FreshInstanceFailure => {
                            Some(SummaryIssue::FreshInstance)
                        }
                        CallSummaryOutcome::UnsupportedMapping => {
                            Some(match call.observation.mapping_loss {
                                Some(MappingLoss::Guard) => SummaryIssue::Guard,
                                Some(MappingLoss::AliasFrame) => SummaryIssue::AliasFrame,
                                _ => SummaryIssue::AbiOrResourceMapping,
                            })
                        }
                    };
                    issues.extend(issue);
                }
                FunctionSummaryAudit {
                    function: id,
                    summary: s.clone(),
                    requirements,
                    returns: cfg.returns().iter().map(|r| r.finding()).collect(),
                    queries: cfg.relation_queries().to_vec(),
                    relations: cfg.relation_evidence().to_vec(),
                    provenance: cfg.provenance_evidence().to_vec(),
                    guarded_precision_losses: cfg.guarded_precision_losses().clone(),
                    metrics,
                    issues: issues.into_iter().collect(),
                }
            })
            .collect();
        Self {
            version: SUMMARY_SCHEMA_VERSION,
            functions,
            diagnostics: report.diagnostics().to_vec(),
            trust: report.trust_report().clone(),
            memory_checked: report.is_memory_checked_core0(),
        }
    }
    pub fn stable_dump(&self) -> String {
        format!("nera-summary-audit-v{}\n{self:#?}\n", self.version)
    }
}
