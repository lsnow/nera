//! Immutable-program observation replay cache.
use super::QueryEvidence;
/// Reuses a freshly verified observation set only within this immutable unit
/// and configuration. Cache keys are exact evidence including function/site,
/// case, guard, effective premises, limits and witness; equality, not a hash,
/// decides membership. No method installs a result into a ResourceState.
#[derive(Debug)]
pub struct RelationReplayCache<'a, 'unit> {
    _program: &'a crate::ResolvedVirUnit<'unit>,
    verified: crate::ProgramVerification,
}

impl<'a, 'unit> RelationReplayCache<'a, 'unit> {
    /// Whole-unit equality detects missing functions, changed effects, stale
    /// dependencies, altered call mappings and forged SCC closure. The cache
    /// was built by verify_program, not from the proposed summary or its hash.
    pub fn accepts_summary_audit(
        &self,
        proposal: &crate::verifier::summary::audit::SummaryAudit,
    ) -> bool {
        crate::verifier::summary::audit::SummaryAudit::from_report(&self.verified) == *proposal
    }
    pub fn new(
        program: &'a crate::ResolvedVirUnit<'unit>,
        config: crate::CfgAnalysisConfig,
    ) -> Result<Self, crate::VerificationError> {
        Ok(Self {
            _program: program,
            verified: crate::verify_program(program, config)?,
        })
    }

    #[must_use]
    pub fn accepts_query(&self, proposal: &QueryEvidence) -> bool {
        self.verified
            .functions()
            .get(&proposal.finding.site().function())
            .is_some_and(|f| {
                f.cfg().relation_queries().contains(proposal)
                    || f.proofs()
                        .iter()
                        .any(|proof| proof.relation_queries().contains(proposal))
            })
    }

    /// A Prove-local trace is separate from the CFG transfer journal. Exact
    /// equality detects omission/reordering as well as forged observations.
    #[must_use]
    pub fn accepts_spec_trace(
        &self,
        function: crate::VirFunctionId,
        prove: crate::VirSpecProveId,
        proposal: &[QueryEvidence],
    ) -> bool {
        self.verified
            .functions()
            .get(&function)
            .and_then(|f| f.proofs().iter().find(|p| p.prove() == prove))
            .is_some_and(|p| p.relation_queries() == proposal)
    }

    /// Batch replay also detects omitted observations, including Unknown.
    #[must_use]
    pub fn accepts_trace(
        &self,
        function: crate::VirFunctionId,
        proposal: &[QueryEvidence],
    ) -> bool {
        self.verified
            .functions()
            .get(&function)
            .is_some_and(|f| f.cfg().relation_queries() == proposal)
    }

    #[must_use]
    pub fn accepts_relation(&self, proposal: &crate::verifier::relation::RelationEvidence) -> bool {
        self.verified
            .functions()
            .get(&proposal.finding.site().function())
            .is_some_and(|f| f.cfg().relation_evidence().contains(proposal))
    }

    #[must_use]
    pub fn accepts_provenance(
        &self,
        proposal: &crate::verifier::provenance::ProvenanceEvidence,
    ) -> bool {
        self.verified
            .functions()
            .get(&proposal.finding.site().function())
            .is_some_and(|f| f.cfg().provenance_evidence().contains(proposal))
    }

    /// Complete resource + arithmetic observation replay. Missing successful,
    /// Unknown, lifecycle, or auxiliary numeric records all fail equality.
    #[must_use]
    pub fn accepts_memory_trace(
        &self,
        function: crate::VirFunctionId,
        provenance: &[crate::verifier::provenance::ProvenanceEvidence],
        queries: &[QueryEvidence],
        relations: &[crate::verifier::relation::RelationEvidence],
    ) -> bool {
        self.verified.functions().get(&function).is_some_and(|f| {
            f.cfg().provenance_evidence() == provenance
                && f.cfg().relation_queries() == queries
                && f.cfg().relation_evidence() == relations
        })
    }
}

pub fn replay_query_evidence(
    program: &crate::ResolvedVirUnit<'_>,
    config: crate::CfgAnalysisConfig,
    proposal: &QueryEvidence,
) -> Result<bool, crate::VerificationError> {
    Ok(RelationReplayCache::new(program, config)?.accepts_query(proposal))
}
