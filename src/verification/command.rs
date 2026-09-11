//! Shared presentation/exit boundary, not a verifier or proof-import API.
use super::{PreviewOutcome, PreviewStage, TextReportMode, VerificationPreview, render_text};
use std::io::{self, Write};

/// Write and flush an immutable preview before returning the CLI exit status.
/// Configuration is supplied to verify_source/verify_unit, never parsed from output.
/// An I/O failure cannot return a successful exit status, even after a partial write.
pub fn write_report(
    preview: &VerificationPreview,
    mode: TextReportMode,
    output: &mut impl Write,
) -> io::Result<u8> {
    output.write_all(render_text(preview, mode).as_bytes())?;
    output.flush()?;
    Ok(exit_status(preview.outcome()))
}

/// Process policy only, not another verifier verdict. Some variants currently
/// have no source producer; they must still fail closed if exposed in the future.
fn exit_status(outcome: PreviewOutcome) -> u8 {
    match outcome {
        PreviewOutcome::Checked => 0,
        PreviewOutcome::Unproved
        | PreviewOutcome::Unsupported {
            stage: PreviewStage::Verification,
            ..
        } => 1,
        PreviewOutcome::Unsupported { .. }
        | PreviewOutcome::Rejected(_)
        | PreviewOutcome::BudgetAborted
        | PreviewOutcome::AnalysisFailed => 2,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exit_policy_is_total_without_claiming_unproduced_variants_are_source_tests() {
        use crate::CapabilityFailureKind as K;
        assert_eq!(exit_status(PreviewOutcome::Checked), 0);
        assert_eq!(exit_status(PreviewOutcome::Unproved), 1);
        assert_eq!(exit_status(PreviewOutcome::BudgetAborted), 2);
        assert_eq!(exit_status(PreviewOutcome::AnalysisFailed), 2);
        for stage in [
            PreviewStage::Frontend,
            PreviewStage::Validation,
            PreviewStage::Resolution,
            PreviewStage::Verification,
        ] {
            assert_eq!(exit_status(PreviewOutcome::Rejected(stage)), 2);
            assert_eq!(
                exit_status(PreviewOutcome::Unsupported {
                    stage,
                    kind: K::VerificationUnsupported
                }),
                if stage == PreviewStage::Verification {
                    1
                } else {
                    2
                }
            );
        }
    }
}
