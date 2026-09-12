use std::{error::Error, fs, path::Path};

use super::missing_marker;

use super::stage7_1::{
    check_phase7_aggregate_transfer_regression, check_phase7_builtin_drop_regression,
    check_phase7_identity_regression,
};

pub(in crate::regression) fn check_phase7_summary_projection(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-summary-projection-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-6-3",
            "Unknown",
            "ReturnWorld",
            "SummaryBinding",
            "7.6.4",
        ],
    ) {
        return Err(format!("summary projection is missing '{marker}'").into());
    }
    let transfer = fs::read_to_string(root.join("src/verifier/transfer/call.rs"))?;
    if transfer.contains("validate_structure") || transfer.contains("stable_dump") {
        return Err("call transfer must not treat a structurally valid dump as authority".into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_summary_calls(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-summary-calls-v2.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &["stage7-6-4", "SummaryRegistry", "Unknown", "Frame", "7.6.5"],
    ) {
        return Err(format!("summary calls document misses '{marker}'").into());
    }
    let registry = fs::read_to_string(root.join("src/verifier/summary/registry.rs"))?;
    if !registry.contains("pub(crate) struct SummaryRegistry")
        || !registry.contains("SummaryState::Candidate")
    {
        return Err("summary publication must remain private and require proved candidates".into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_recursive_summary(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-recursive-summary-v5.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &["stage7-6-7", "Inductive", "SccLimits", "Unknown", "7.6.8"],
    ) {
        return Err(format!("recursive summary document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_summary_acceptance(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-summary-acceptance-v6.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-6-8",
            "SummaryAudit",
            "max_summary_evidence",
            "Unknown",
            "7.7",
            "峰值",
        ],
    ) {
        return Err(format!("summary acceptance document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_borrow_summary(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-borrow-summary-v4.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-6-6",
            "BorrowRestoration",
            "InputLoan",
            "Unknown",
            "7.6.7",
        ],
    ) {
        return Err(format!("borrow summary document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_conditional_summary(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-conditional-summary-v3.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-6-5",
            "ConditionalResourceState",
            "ReturnWorld",
            "Unknown",
            "7.6.6",
        ],
    ) {
        return Err(format!("conditional summary document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_summary_architecture(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-summary-architecture-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-6-2",
            "Lowerer",
            "TransferBuilder",
            "Draft",
            "NERA_REFACTOR_COMPARE_DIR",
            "7.6.3",
        ],
    ) {
        return Err(format!("summary architecture is missing '{marker}'").into());
    }
    // Follow the actual implementation owner, never keep dead marker copies in
    // a parent file merely to satisfy an old textual regression check.
    for (parent, owner, markers) in [
        (
            "src/frontend/lower.rs",
            "src/frontend/lower/contract.rs",
            &["fn infer_contracts(", "fn lower_hir_specs("][..],
        ),
        (
            "src/frontend/lower.rs",
            "src/frontend/lower/abi.rs",
            &[
                "fn classify_hir_signature(",
                "fn bind_abi_entry_parameters(",
                "fn lower_return(",
            ][..],
        ),
        (
            "src/verifier/transfer.rs",
            "src/verifier/transfer/call.rs",
            &["fn call(", "fn install_aggregate_abi_payloads("][..],
        ),
        (
            "src/verifier/transfer.rs",
            "src/verifier/transfer/access.rs",
            &[
                "fn require_slice_argument(",
                "fn object_access_facts(",
                "fn permission_access_obligations(",
            ][..],
        ),
        (
            "src/verifier/transfer.rs",
            "src/verifier/transfer/obligation.rs",
            &[
                "struct ResourceObligation {",
                "struct InstructionTransfer {",
            ][..],
        ),
        (
            "src/verifier/transfer.rs",
            "src/verifier/transfer/error.rs",
            &["enum TransferError {"][..],
        ),
    ] {
        let parent_source = fs::read_to_string(root.join(parent))?;
        let owner_source = fs::read_to_string(root.join(owner))?;
        for marker in markers {
            if parent_source.contains(marker) || owner_source.matches(marker).count() != 1 {
                return Err(format!("{marker} must be owned once by {owner}, not {parent}").into());
            }
        }
    }
    for path in [
        "src/frontend/lower/tests.rs",
        "src/verifier/transfer/tests.rs",
    ] {
        fs::read(root.join(path))?;
    }
    check_phase7_identity_regression(root)?;
    check_phase7_builtin_drop_regression(root)?;
    check_phase7_aggregate_transfer_regression(root)?;
    Ok(())
}

pub(in crate::regression) fn check_phase7_summary_baseline(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-summary-baseline-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-6-1",
            "may-footprint",
            "must-fact",
            "normal return",
            "divergence",
            "Unknown",
            "Invalid",
            "conditional interface summary",
            "SCC",
            "unverified",
        ],
    ) {
        return Err(format!("summary baseline is missing '{marker}'").into());
    }
    fs::read(root.join("spec/cases/verify/summary-baseline.nera"))?;
    Ok(())
}
