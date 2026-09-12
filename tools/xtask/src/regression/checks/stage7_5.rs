use std::{error::Error, fs, path::Path};

use super::missing_marker;

pub(in crate::regression) fn check_phase7_provenance_baseline(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-provenance-baseline-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-5-1",
            "ptr_byte_distance",
            "one-past",
            "allocation instance",
            "Unknown",
            "10.1/10.3",
            "consumer",
            "unverified",
        ],
    ) {
        return Err(format!("provenance baseline is missing '{rule}'").into());
    }
    fs::read(root.join("spec/cases/verify/provenance-baseline.nera"))?;
    Ok(())
}

pub(in crate::regression) fn check_phase7_provenance_schema(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-provenance-schema-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-5-2",
            "VirProvenanceCatalog",
            "VirSubobject",
            "authority",
            "7.5.3",
            "7.5.5",
        ],
    ) {
        return Err(format!("provenance schema is missing '{rule}'").into());
    }
    fs::read(root.join("spec/cases/verify/provenance-schema.nera"))?;
    Ok(())
}

pub(in crate::regression) fn check_phase7_address_model(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-address-model-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-5-8",
            "SystemV2",
            "one-past",
            "PointerDomainViolation",
            "PermissionMismatch",
            "unverified",
            "ABI",
        ],
    ) {
        return Err(format!("address model audit is missing '{rule}'").into());
    }
    fs::read(root.join("spec/cases/verify/native-address-model.nera"))?;
    Ok(())
}

pub(in crate::regression) fn check_phase7_provenance_audit(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-provenance-audit-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-5-9",
            "ProvenanceEvidence",
            "accepts_memory_trace",
            "max_relation_evidence",
            "Unknown",
        ],
    ) {
        return Err(format!("provenance audit is missing '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_provenance_acceptance(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-provenance-acceptance-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-5-10",
            "Unknown",
            "gated",
            "7.6",
            "provenance_checked",
            "max_slots",
            "unverified",
        ],
    ) {
        return Err(format!("provenance acceptance is missing '{marker}'").into());
    }
    fs::read(root.join("src/bin/fuzz_support/provenance_cases.rs"))?;
    Ok(())
}

pub(in crate::regression) fn check_phase7_provenance_flow(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-provenance-flow-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-5-7",
            "MaybeLive",
            "IncomingDomain",
            "SelectedDomain",
            "Unknown",
            "7.6",
            "ABI",
        ],
    ) {
        return Err(format!("provenance flow design is missing '{rule}'").into());
    }
    fs::read(root.join("spec/cases/verify/provenance-flow.nera"))?;
    Ok(())
}

pub(in crate::regression) fn check_phase7_pointer_comparison(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-pointer-comparison-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-5-6",
            "PointerSameInstance",
            "PointerCompatibleDomain",
            "ptr_byte_distance",
            "Unknown",
            "V15",
            "7.5.7",
        ],
    ) {
        return Err(format!("pointer relation design is missing '{rule}'").into());
    }
    fs::read(root.join("spec/cases/verify/pointer-comparison.nera"))?;
    Ok(())
}

pub(in crate::regression) fn check_phase7_pointer_domain(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-pointer-domain-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-5-5",
            "PointerDomainContains",
            "one-past",
            "Unknown",
            "V14",
            "SystemV2",
            "7.5.7",
            "10.1/10.3",
        ],
    ) {
        return Err(format!("pointer domain design is missing '{rule}'").into());
    }
    fs::read(root.join("spec/cases/verify/pointer-domain.nera"))?;
    Ok(())
}

pub(in crate::regression) fn check_phase7_raw_address(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-raw-address-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-5-4",
            "RawAddress",
            "permission",
            "V13",
            "7.5.5",
            "10.1/10.3",
        ],
    ) {
        return Err(format!("raw address design is missing '{rule}'").into());
    }
    fs::read(root.join("spec/cases/verify/raw-address.nera"))?;
    Ok(())
}

pub(in crate::regression) fn check_phase7_allocation_instance(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-allocation-instance-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-5-3",
            "AllocationInstanceFresh",
            "Unknown",
            "4_096",
            "unverified",
            "7.5.5",
        ],
    ) {
        return Err(format!("allocation instance design is missing '{rule}'").into());
    }
    fs::read(root.join("spec/cases/verify/provenance-instance.nera"))?;
    Ok(())
}
