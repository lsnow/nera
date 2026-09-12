use std::{error::Error, fs, path::Path};

use super::missing_marker;

pub(in crate::regression) fn check_phase7_initialization_baseline(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let baseline = fs::read_to_string(root.join("docs/stage7-initialization-baseline-v1.md"))?;
    if let Some(rule) = missing_marker(
        &baseline,
        &[
            "7.3.1",
            "let mut value: T;",
            "ObjectDeinitialize",
            "Unknown",
            "LoanBegin",
            "7.3.2",
            "stage7-3-1",
        ],
    ) {
        return Err(format!("initialization baseline is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_initialization_planning(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-initialization-planning-v1.md"))?;
    if let Some(rule) = missing_marker(
        &plan,
        &[
            "InitializationEffects",
            "LoanBegin",
            "Unknown",
            "stage7-3-2",
        ],
    ) {
        return Err(format!("initialization planning acceptance is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_deferred_local(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-deferred-local-v1.md"))?;
    if let Some(rule) = missing_marker(
        &plan,
        &[
            "StorageReset",
            "HirVersion::V6",
            "VirUnitVersion::V10",
            "stage7-3-3",
        ],
    ) {
        return Err(format!("deferred local acceptance is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_partial_refill(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-partial-refill-v1.md"))?;
    if let Some(rule) = missing_marker(
        &plan,
        &[
            "ResourceInitialize",
            "ObjectDrop",
            "exactly-once",
            "stage7-3-4",
        ],
    ) {
        return Err(format!("partial refill acceptance is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_partial_construction(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-partial-construction-v1.md"))?;
    if let Some(rule) = missing_marker(
        &plan,
        &[
            "ResourceStorageReset",
            "ObjectDrop",
            "HirVersion::V7",
            "VirUnitVersion::V11",
            "stage7-3-5",
        ],
    ) {
        return Err(format!("partial construction acceptance is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_enum_construction(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-enum-construction-v1.md"))?;
    if let Some(rule) = missing_marker(
        &plan,
        &[
            "EnumSetDiscriminant",
            "ObjectResourcePayloadEmpty",
            "ObjectDrop",
            "stage7-3-6",
        ],
    ) {
        return Err(format!("enum construction acceptance is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_heap_construction(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-heap-construction-v1.md"))?;
    if let Some(rule) = missing_marker(
        &plan,
        &[
            "alloc<T>(1)",
            "ObjectDrop",
            "AllocationResourcePayloadEmpty",
            "stage7-3-7",
        ],
    ) {
        return Err(format!("heap construction acceptance is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_loop_initialization(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-loop-initialization-v1.md"))?;
    if let Some(rule) = missing_marker(
        &plan,
        &["initialized-prefix", "back-edge", "Unknown", "stage7-3-8"],
    ) {
        return Err(format!("loop initialization acceptance is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_initialization_interfaces(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-initialization-interfaces-v1.md"))?;
    if let Some(rule) = missing_marker(
        &plan,
        &["value bytes", "padding", "unconditional", "stage7-3-9"],
    ) {
        return Err(format!("initialization interface acceptance is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_initialization_acceptance(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let plan = fs::read_to_string(root.join("docs/stage7-initialization-acceptance-v1.md"))?;
    if let Some(rule) = missing_marker(
        &plan,
        &["concretization", "padding", "Unknown", "stage7-3-10", "7.4"],
    ) {
        return Err(format!("initialization acceptance is missing '{rule}'").into());
    }
    Ok(())
}
