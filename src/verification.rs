//! Experimental, read-only verification preview. One frontend/resolution path
//! and one canonical verifier invocation; no execution, replay or proof import.
//! A successful analysis is relative to its runtime profile and trust boundary,
//! not a checked native artifact or a compiler soundness theorem.
mod command;
mod report;
pub use command::write_report;
mod text;
pub use report::*;
pub use text::{TextReportMode, render_text};

#[cfg(test)]
pub(crate) mod scale_tests;

use crate::session::{CompilationInput, CompilerSession, SessionError};
use crate::{
    CfgAnalysisConfig, FrontendIssue, FrontendStatus, ProgramVerification, SourceFile,
    ValidatedVirUnit, VerificationError, VirResolutionError, VirUnit, VirValidationError,
};
use std::sync::Arc;

/// Source identity binds the complete snapshot, selected source and effective
/// configuration. Raw-unit callers bypass the frontend and have no source binding.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Input {
    Source(Arc<CompilationInput>),
    Unit(Arc<VirUnit>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PreviewFailure {
    Validation(VirValidationError),
    Resolution(VirResolutionError),
    Verification(VerificationError),
    /// A producer claimed acceptance without a validated unit. Never success.
    MissingValidatedUnit,
}

/// Immutable observations of the actual pipeline. There is no public constructor
/// from reports/summaries, deserializer, mutator, or call-authorizing seal.
///
/// ```compile_fail
/// fn forge(preview: &mut nera::verification::VerificationPreview) {
///     preview.verification = None;
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerificationPreview {
    instantiations: Option<crate::frontend::InstantiationReport>,
    input: Input,
    config: CfgAnalysisConfig,
    frontend_status: Option<FrontendStatus>,
    frontend_issues: Vec<FrontendIssue>,
    unit: Option<Arc<ValidatedVirUnit>>,
    resolved: bool,
    verification: Option<ProgramVerification>,
    failure: Option<PreviewFailure>,
}

/// The production source entry. I/O belongs to the caller (`SourceFile::load`);
/// invalid UTF-8 and language errors still go through the actual frontend.
pub fn verify_source(source: &SourceFile, config: CfgAnalysisConfig) -> VerificationPreview {
    finish_source(prepare_source(source, config))
}

pub(crate) fn verify_session_source(
    session: &CompilerSession,
    logical_name: &str,
) -> Result<VerificationPreview, SessionError> {
    Ok(finish_source(prepare_session_source(
        session,
        logical_name,
    )?))
}

fn finish_source(mut preview: VerificationPreview) -> VerificationPreview {
    if preview.frontend_status == Some(FrontendStatus::AcceptedProposal) {
        preview.analyze_unit();
    }
    preview
}

// Private phase boundary shared with measurements; never exposes an unfinished preview.
fn prepare_source(source: &SourceFile, config: CfgAnalysisConfig) -> VerificationPreview {
    let session = CompilerSession::single(source.clone(), config);
    prepare_session_source(&session, "input.nera").expect("single-source production configuration")
}

fn prepare_session_source(
    session: &CompilerSession,
    logical_name: &str,
) -> Result<VerificationPreview, SessionError> {
    let (input, frontend) = session.analyze(logical_name)?.into_parts();
    let config = input.effective().analysis();
    let (status, issues, unit, instantiations) = frontend.into_verification_parts();
    Ok(VerificationPreview {
        instantiations: Some(instantiations),
        input: Input::Source(Arc::new(input)),
        config,
        frontend_status: Some(status),
        frontend_issues: issues,
        unit: unit.map(Arc::new),
        resolved: false,
        verification: None,
        failure: None,
    })
}

/// Raw VIR entry for existing typed fixtures and future producers. Validation is
/// mandatory, and source/frontend success is explicitly unavailable on this path.
pub fn verify_unit(unit: VirUnit, config: CfgAnalysisConfig) -> VerificationPreview {
    let input = Arc::new(unit);
    let validated = input.as_ref().clone().into_validated();
    let mut preview = VerificationPreview {
        instantiations: None,
        input: Input::Unit(input),
        config,
        frontend_status: None,
        frontend_issues: Vec::new(),
        unit: None,
        resolved: false,
        verification: None,
        failure: None,
    };
    match validated {
        Ok(unit) => {
            preview.unit = Some(Arc::new(unit));
            preview.analyze_unit();
        }
        Err(error) => preview.failure = Some(PreviewFailure::Validation(error)),
    }
    preview
}

impl VerificationPreview {
    fn analyze_unit(&mut self) {
        let Some(unit) = self.unit.as_ref() else {
            self.failure = Some(PreviewFailure::MissingValidatedUnit);
            return;
        };
        match unit.resolve() {
            Err(error) => self.failure = Some(PreviewFailure::Resolution(error)),
            Ok(resolved) => {
                self.resolved = true;
                match crate::verify_program(&resolved, self.config) {
                    Ok(report) => self.verification = Some(report),
                    Err(error) => self.failure = Some(PreviewFailure::Verification(error)),
                }
            }
        }
    }
    pub fn source(&self) -> Option<&SourceFile> {
        match &self.input {
            Input::Source(s) => Some(s.source()),
            Input::Unit(_) => None,
        }
    }
    /// Owned snapshot/config binding; unavailable for the raw-unit entry.
    pub fn source_input(&self) -> Option<&CompilationInput> {
        match &self.input {
            Input::Source(input) => Some(input),
            Input::Unit(_) => None,
        }
    }

    pub fn instantiations(&self) -> Option<&crate::frontend::InstantiationReport> {
        self.instantiations.as_ref()
    }
    pub fn matches_session(&self, session: &CompilerSession, logical_name: &str) -> bool {
        self.source_input().is_some_and(|old| {
            session
                .input(logical_name)
                .is_ok_and(|new| old.same_analysis_input(&new))
        })
    }
    /// Resolve a unit-local origin to this result's snapshot, not a live path.
    pub fn locate_vir_span(&self, span: crate::VirSourceSpan) -> Option<crate::VirSourceSpan> {
        self.validated_unit()?
            .as_unit()
            .source_map
            .source(span.source)?;
        self.source_input()?.locate_unit_span(span)
    }
    pub fn frontend_status(&self) -> Option<FrontendStatus> {
        self.frontend_status
    }
    pub fn frontend_issues(&self) -> &[FrontendIssue] {
        &self.frontend_issues
    }
    pub fn validated_unit(&self) -> Option<&ValidatedVirUnit> {
        self.unit.as_deref()
    }
    pub fn is_resolved(&self) -> bool {
        self.resolved
    }
    /// None means unavailable/incomplete, NOT a successful zero-obligation body.
    pub fn verification(&self) -> Option<&ProgramVerification> {
        self.verification.as_ref()
    }
    pub fn failure(&self) -> Option<&PreviewFailure> {
        self.failure.as_ref()
    }
    pub fn config(&self) -> CfgAnalysisConfig {
        self.config
    }
    /// Exact single-source convenience input comparison, not a hash or cache
    /// permission. A larger snapshot cannot match just one of its input files.
    pub fn matches_source(&self, source: &SourceFile, config: CfgAnalysisConfig) -> bool {
        self.matches_session(
            &CompilerSession::single(source.clone(), config),
            "input.nera",
        )
    }
    /// Exact unit/config equality includes bodies, ABI, specs, origins and profiles.
    /// A failed raw input also retains its exact identity, without claiming validity.
    pub fn matches_unit(&self, unit: &VirUnit, config: CfgAnalysisConfig) -> bool {
        self.config == config
            && match &self.input {
                Input::Unit(input) => input.as_ref() == unit,
                Input::Source(_) => self.unit.as_ref().is_some_and(|u| u.as_unit() == unit),
            }
    }
    pub fn outcome(&self) -> PreviewOutcome {
        if let Some(failure) = &self.failure {
            return failure_outcome(failure);
        }
        if let Some(report) = &self.verification {
            return if report.is_memory_checked_core0() {
                PreviewOutcome::Checked
            } else {
                PreviewOutcome::Unproved
            };
        }
        match self.frontend_status {
            Some(FrontendStatus::Invalid) => PreviewOutcome::Rejected(PreviewStage::Frontend),
            Some(FrontendStatus::Unsupported) => PreviewOutcome::Unsupported {
                stage: PreviewStage::Frontend,
                kind: crate::CapabilityFailureKind::RuntimeSemanticsUnsupported,
            },
            _ => PreviewOutcome::AnalysisFailed,
        }
    }
    /// Exactly the canonical whole-program conclusion, relative to explicit
    /// trust entries and the declared implementation TCB. Does not execute code.
    pub fn is_checked(&self) -> bool {
        self.outcome() == PreviewOutcome::Checked
    }
}

fn failure_outcome(failure: &PreviewFailure) -> PreviewOutcome {
    use crate::{CfgAnalysisError as C, VerificationError as V, VirResolutionErrorKind as R};
    match failure {
        PreviewFailure::Validation(_) => PreviewOutcome::Rejected(PreviewStage::Validation),
        PreviewFailure::Resolution(error) => match error.kind() {
            R::UnsupportedExternalCall(_) => PreviewOutcome::Unsupported {
                stage: PreviewStage::Resolution,
                kind: crate::CapabilityFailureKind::RuntimeSemanticsUnsupported,
            },
            _ => PreviewOutcome::Rejected(PreviewStage::Resolution),
        },
        PreviewFailure::Verification(V::UnsupportedCapability(_)) => PreviewOutcome::Unsupported {
            stage: PreviewStage::Verification,
            kind: crate::CapabilityFailureKind::VerificationUnsupported,
        },
        PreviewFailure::Verification(V::Cfg {
            error:
                C::BlockVisitLimitExceeded { .. }
                | C::RelationEvidenceBudgetExceeded { .. }
                | C::InstructionSiteLimitExceeded,
            ..
        }) => PreviewOutcome::BudgetAborted,
        PreviewFailure::Verification(_) | PreviewFailure::MissingValidatedUnit => {
            PreviewOutcome::AnalysisFailed
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn unproduced_error_variants_keep_their_classification_without_minting_a_report() {
        // There is currently no production emitter for UnsupportedCapability.
        // Test only classification, never claim this mock went through a body.
        assert_eq!(
            failure_outcome(&PreviewFailure::Verification(
                VerificationError::UnsupportedCapability("future-rule")
            )),
            PreviewOutcome::Unsupported {
                stage: PreviewStage::Verification,
                kind: crate::CapabilityFailureKind::VerificationUnsupported
            }
        );
        assert_eq!(
            failure_outcome(&PreviewFailure::Verification(
                VerificationError::InvalidFinding
            )),
            PreviewOutcome::AnalysisFailed
        );
        assert_eq!(
            failure_outcome(&PreviewFailure::MissingValidatedUnit),
            PreviewOutcome::AnalysisFailed
        );
    }
}
