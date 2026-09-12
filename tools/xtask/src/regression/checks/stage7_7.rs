use std::{error::Error, fs, path::Path};

use super::missing_marker;

pub(in crate::regression) fn check_phase7_verify_acceptance(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-verify-acceptance-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-7-6",
            "NERA_VERIFY_SCALE",
            "VmHWM",
            "SummaryAudit",
            "7.8.1",
        ],
    ) {
        return Err(format!("verify acceptance document misses '{marker}'").into());
    }
    let guide = fs::read_to_string(root.join("docs/verify.md"))?;
    if let Some(marker) = missing_marker(
        &guide,
        &[
            "nera verify",
            "--explain",
            "Unknown",
            "unverified",
            "终止",
            "栈空间",
        ],
    ) {
        return Err(format!("verify guide misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_verify_fail_closed(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-verify-fail-closed-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-7-5",
            "write_report",
            "BudgetAborted",
            "SummaryAudit",
            "7.7.6",
        ],
    ) {
        return Err(format!("verify fail-closed document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_auto_memory_corpus(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-auto-memory-corpus-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-7-4",
            "auto_memory_cases",
            "NotClosed",
            "OwnershipConserved",
            "7.7.5",
        ],
    ) {
        return Err(format!("ordinary memory corpus document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_verify_preview(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-verify-preview-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &["stage7-7-3", "nera verify", "stdout", "Unknown", "7.7.4"],
    ) {
        return Err(format!("verify preview document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_source_diagnostics(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-source-diagnostics-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-7-2",
            "render_text",
            "TextReportMode",
            "Unknown",
            "7.7.3",
        ],
    ) {
        return Err(format!("source diagnostic document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_verify_report(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-verification-report-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-7-1",
            "VerificationPreview",
            "BudgetAborted",
            "Unknown",
            "7.7.2",
        ],
    ) {
        return Err(format!("verification report document misses '{marker}'").into());
    }
    Ok(())
}
