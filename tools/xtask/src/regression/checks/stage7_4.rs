use std::{error::Error, fs, path::Path};

use super::missing_marker;

pub(in crate::regression) fn check_phase7_relation_baseline(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-baseline-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &["Unknown", "len", "7.4.5", "stage7-4-1", "derivation", "SMT"],
    ) {
        return Err(format!("relation baseline is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_difference_relations(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-difference-relations-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "Unknown",
            "wrapping",
            "7.4.3",
            "stage7-4-2",
            "derivation",
            "SMT",
        ],
    ) {
        return Err(format!("difference relations is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_relation_cfg(root: &Path) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-cfg-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "Unknown",
            "widening",
            "7.4.4",
            "stage7-4-3",
            "derivation",
            "SSA",
        ],
    ) {
        return Err(format!("relation CFG is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_symbolic_footprint(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-symbolic-footprint-v1.md"))?;
    if let Some(rule) = missing_marker(&doc, &["Unknown", "envelope", "SSA", "7.4.5", "stage7-4-4"])
    {
        return Err(format!("symbolic footprint is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_relation_bounds(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-bounds-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &["len(value)", "Unknown", "HIR V8", "stage7-4-5", "7.4.6"],
    ) {
        return Err(format!("relation bounds is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_disjoint_elements(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-disjoint-elements-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &["i != j", "Unknown", "stride", "stage7-4-6", "7.4.7"],
    ) {
        return Err(format!("disjoint elements is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_sibling_slices(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-sibling-slices-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "Suspended",
            "Unknown",
            "LoanReborrowAuthority",
            "stage7-4-7",
            "7.4.8",
        ],
    ) {
        return Err(format!("sibling slices is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_strided_regions(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-strided-regions-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-4-8",
            "Unknown",
            "stride",
            "max_region_pairs_per_instruction",
            "7.4.9",
        ],
    ) {
        return Err(format!("strided regions is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_relation_composition(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-composition-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-4-9",
            "Unknown",
            "initialized-prefix",
            "7.4.10",
            "7.6",
        ],
    ) {
        return Err(format!("relation composition is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_relation_audit(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-audit-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-4-10",
            "Unknown",
            "RelationReplayCache",
            "Rust",
            "7.4.11",
            "query",
        ],
    ) {
        return Err(format!("relation audit is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_relation_acceptance(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-relation-acceptance-v1.md"))?;
    if let Some(rule) = missing_marker(
        &doc,
        &[
            "stage7-4-11",
            "source accepted",
            "Unknown",
            "native",
            "7.5",
            "7.6",
            "relation-acceptance-limited",
        ],
    ) {
        return Err(format!("relation acceptance is missing '{rule}'").into());
    }
    for path in [
        "spec/cases/verify/relation-acceptance.nera",
        "spec/cases/verify/relation-acceptance-limited.nera",
        "src/bin/fuzz_support/relation_cases.rs",
    ] {
        fs::read(root.join(path))?;
    }
    Ok(())
}
