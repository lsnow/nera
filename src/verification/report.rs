//! Borrowed report views; counting never re-verifies, clones CFGs, or serializes
//! SummaryAudit. Historical/summary evidence is not counted as extra obligations.
use super::*;
use crate::{
    CapabilityFailureKind, CfgObligation, FunctionPostconditionCheck, ObligationStatus, SpecProof,
    VerifierFinding, VirFunctionId,
};

pub const PREVIEW_REPORT_VERSION: u32 = 2;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreviewStage {
    Frontend,
    Validation,
    Resolution,
    Verification,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreviewOutcome {
    Checked,
    /// Analysis completed, but necessary facts or proofs remain unresolved.
    /// Refuted abstract conditions are not asserted to be executable witnesses.
    Unproved,
    Unsupported {
        stage: PreviewStage,
        kind: CapabilityFailureKind,
    },
    Rejected(PreviewStage),
    BudgetAborted,
    AnalysisFailed,
}

/// Existing component versions, not a new semantic/capability manifest. Runtime
/// identity is unavailable until validation; configuration is always the requested
/// effective configuration (there is no hidden solver/profile switch).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreviewVersions {
    pub report: u32,
    pub compiler: &'static str,
    pub unit: Option<crate::VirUnitVersion>,
    pub runtime: Option<crate::VirRuntimeSemanticProfile>,
    pub summary_schema: u32,
    pub summary_profile: &'static str,
    pub relation_kernel: u32,
    pub relation_theory: &'static str,
    pub external_solver: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustedComponent {
    Frontend,
    HirLowering,
    VirValidationResolution,
    RustVerifier,
    LocalNumericKernel,
    AbiRuntimeModel,
    Backend,
    SystemToolchain,
    RuntimeHardware,
}
pub const ANALYSIS_TCB: &[TrustedComponent] = &[
    TrustedComponent::VirValidationResolution,
    TrustedComponent::RustVerifier,
    TrustedComponent::LocalNumericKernel,
    TrustedComponent::AbiRuntimeModel,
];
pub const SOURCE_TCB: &[TrustedComponent] = &[
    TrustedComponent::Frontend,
    TrustedComponent::HirLowering,
    TrustedComponent::VirValidationResolution,
    TrustedComponent::RustVerifier,
    TrustedComponent::LocalNumericKernel,
    TrustedComponent::AbiRuntimeModel,
];
/// Additional, unproved boundary IF the user later executes a native artifact.
/// These consumers are not invoked or checked by verification preview.
pub const NATIVE_EXECUTION_BOUNDARY: &[TrustedComponent] = &[
    TrustedComponent::Backend,
    TrustedComponent::SystemToolchain,
    TrustedComponent::RuntimeHardware,
];

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ObligationCounts {
    pub proven: usize,
    pub refuted: usize,
    pub unknown: usize,
}
impl ObligationCounts {
    pub fn total(self) -> usize {
        self.proven + self.refuted + self.unknown
    }
    fn observe(&mut self, status: ObligationStatus) {
        match status {
            ObligationStatus::Proven => self.proven += 1,
            ObligationStatus::Refuted => self.refuted += 1,
            ObligationStatus::Unknown => self.unknown += 1,
        }
    }
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PreviewCounts {
    pub cfg: ObligationCounts,
    pub postconditions: ObligationCounts,
    pub proofs: ObligationCounts,
    /// Historical journal only; can overlap current CFG obligations. Not part
    /// of total(), and never an alternative to the canonical verdict predicate.
    pub historical: ObligationCounts,
    pub functions: usize,
    pub summaries_closed: usize,
    pub summaries_candidate: usize,
    pub summaries_unknown: usize,
    /// Functions exporting an inferred borrow-result relation.
    pub borrow_interfaces: usize,
    /// Complete unconditional/guarded result worlds published by those interfaces.
    pub borrow_worlds: usize,
    pub diagnostics: usize,
}
impl PreviewCounts {
    pub fn total(self) -> usize {
        self.cfg.total() + self.postconditions.total() + self.proofs.total()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ObligationEvidence<'a> {
    Cfg(&'a CfgObligation),
    Postcondition(&'a FunctionPostconditionCheck),
    Proof(&'a SpecProof),
}
#[derive(Clone, Copy, Debug)]
pub struct PreviewObligation<'a> {
    pub function: VirFunctionId,
    pub evidence: ObligationEvidence<'a>,
}
impl PreviewObligation<'_> {
    pub fn finding(self) -> VerifierFinding {
        match self.evidence {
            ObligationEvidence::Cfg(c) => c.finding(),
            ObligationEvidence::Postcondition(c) => c.finding(),
            ObligationEvidence::Proof(p) => p.finding(),
        }
    }
    pub fn status(self) -> ObligationStatus {
        match self.evidence {
            ObligationEvidence::Cfg(c) => c.obligation().status(),
            ObligationEvidence::Postcondition(c) => c.check().status,
            ObligationEvidence::Proof(p) => p.status(),
        }
    }
}

impl VerificationPreview {
    pub fn versions(&self) -> PreviewVersions {
        use crate::verifier::{relation, summary};
        PreviewVersions {
            report: PREVIEW_REPORT_VERSION,
            compiler: env!("CARGO_PKG_VERSION"),
            unit: self.unit.as_ref().map(|u| u.as_unit().version),
            runtime: self.unit.as_ref().map(|u| u.runtime().semantic_profile),
            summary_schema: summary::SUMMARY_SCHEMA_VERSION,
            summary_profile: summary::SUMMARY_VERIFIER_PROFILE,
            relation_kernel: relation::RELATION_KERNEL_VERSION,
            relation_theory: relation::audit::RELATION_THEORY,
            external_solver: false,
        }
    }
    pub fn implementation_trust_boundary(&self) -> &'static [TrustedComponent] {
        if self.source().is_some() {
            SOURCE_TCB
        } else {
            ANALYSIS_TCB
        }
    }
    /// None means verification did not finish; it does not mean no trust was used.
    pub fn trust_report(&self) -> Option<&crate::VerifierTrustReport> {
        self.verification().map(ProgramVerification::trust_report)
    }
    pub fn diagnostics(&self) -> Option<&[crate::VerifierDiagnostic]> {
        self.verification().map(ProgramVerification::diagnostics)
    }
    pub fn obligations(&self) -> Option<impl Iterator<Item = PreviewObligation<'_>>> {
        Some(
            self.verification()?
                .functions()
                .iter()
                .flat_map(|(&function, f)| {
                    f.cfg()
                        .obligations()
                        .iter()
                        .map(ObligationEvidence::Cfg)
                        .chain(
                            f.postconditions()
                                .iter()
                                .map(ObligationEvidence::Postcondition),
                        )
                        .chain(f.proofs().iter().map(ObligationEvidence::Proof))
                        .map(move |evidence| PreviewObligation { function, evidence })
                }),
        )
    }
    /// Historical findings are explanations/closure evidence, not extra runtime
    /// obligations. Their original source and status remain inspectable.
    pub fn historical(&self) -> Option<impl Iterator<Item = &CfgObligation>> {
        Some(
            self.verification()?
                .functions()
                .values()
                .flat_map(|f| f.cfg().summary_pending()),
        )
    }
    pub fn summaries(
        &self,
    ) -> Option<impl Iterator<Item = (VirFunctionId, &crate::verifier::summary::FunctionSummary)>>
    {
        Some(
            self.verification()?
                .functions()
                .iter()
                .map(|(&id, f)| (id, f.summary())),
        )
    }
    pub fn counts(&self) -> Option<PreviewCounts> {
        let report = self.verification()?;
        let mut counts = PreviewCounts {
            functions: report.functions().len(),
            diagnostics: report.diagnostics().len(),
            ..Default::default()
        };
        for obligation in self.obligations()? {
            let target = match obligation.evidence {
                ObligationEvidence::Cfg(_) => &mut counts.cfg,
                ObligationEvidence::Postcondition(_) => &mut counts.postconditions,
                ObligationEvidence::Proof(_) => &mut counts.proofs,
            };
            target.observe(obligation.status());
        }
        for old in self.historical()? {
            counts.historical.observe(old.obligation().status());
        }
        for (_, summary) in self.summaries()? {
            use crate::verifier::summary::SummaryState;
            match summary.state {
                SummaryState::Closed => counts.summaries_closed += 1,
                SummaryState::Candidate => counts.summaries_candidate += 1,
                SummaryState::Unknown(_) => counts.summaries_unknown += 1,
                SummaryState::Hypothesis | SummaryState::Uncomputed => {}
            }
        }
        let runtime = self.validated_unit()?.runtime();
        for function in runtime.functions {
            let Some(abi) = runtime.abis.function(function.id) else {
                continue;
            };
            let signature = &abi.signature;
            if signature.borrow_result().is_some()
                || !signature.borrow_result_alternatives().is_empty()
            {
                counts.borrow_interfaces += 1;
                counts.borrow_worlds += usize::from(signature.borrow_result().is_some())
                    + signature.borrow_result_alternatives().len();
            }
        }
        Some(counts)
    }
}
