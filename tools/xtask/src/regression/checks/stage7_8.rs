use std::{error::Error, fs, path::Path};

use super::missing_marker;

pub(in crate::regression) fn check_phase7_compilation_session(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-compilation-session-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-8-1",
            "CompilerSession",
            "SourceDatabase",
            "VirSourceId",
            "7.8.2",
            "raw VIR",
        ],
    ) {
        return Err(format!("session document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_module_program(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-module-program-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-8-2",
            "CompilerSession::modules",
            "DAG",
            "private",
            "VirSourceMap",
            "7.8.3",
        ],
    ) {
        return Err(format!("module program document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_borrow_interface_mapping(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-borrow-interface-mapping-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "BorrowResultRelation",
            "SignatureDraft",
            "V16",
            "V10",
            "check-phase7-borrow-interface-mapping",
            "7.8.3.3",
        ],
    ) {
        return Err(format!("borrow interface mapping document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_implicit_borrow_inference(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-implicit-borrow-inference-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "infer_borrow_sources",
            "check-phase7-implicit-borrow-inference",
            "BorrowResultRelation",
            "7.8.3.4",
            "非递归",
        ],
    ) {
        return Err(format!("implicit borrow inference document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_conditional_borrow_inference(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-conditional-borrow-inference-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "BorrowResultAlternative",
            "BorrowGuardAtom",
            "check-phase7-conditional-borrow-inference",
            "V17",
            "V11",
            "7.8.3.5",
        ],
    ) {
        return Err(format!("conditional borrow inference document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_borrow_projection(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-borrow-projection-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "BorrowProjection",
            "BorrowSliceBound",
            "caller",
            "HirVersion::V12",
            "VirUnitVersion::V18",
            "runtime-vir-v17",
            "check-phase7-borrow-projection",
            "7.8.3.6",
        ],
    ) {
        return Err(format!("borrow projection document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_borrow_source_scc(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-borrow-source-scc-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "NoNormalReturn",
            "source_components",
            "MAX_BORROW_SOURCE_SCC_FUNCTIONS",
            "MAX_BORROW_SOURCE_FIXPOINT_ITERATIONS",
            "check-phase7-borrow-source-scc",
            "7.8.3.7",
        ],
    ) {
        return Err(format!("borrow source SCC document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_implicit_borrow_baseline(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-implicit-borrow-baseline-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "check-phase7-implicit-borrow-baseline",
            "CandidateSources",
            "NoNormalReturn",
            "Unknown",
            "InputLoan",
            "Initialized",
            "7.8.3.2",
        ],
    ) {
        return Err(format!("implicit borrow baseline document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_generic_instances(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-generic-instances-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-8-3",
            "InstanceKey",
            "InstantiationReport",
            "128",
            "7.8.4",
            "未实例化",
        ],
    ) {
        return Err(format!("generic instance document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_implicit_lifetime_syntax(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-implicit-lifetime-syntax-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "check-phase7-implicit-lifetime-syntax",
            "check-phase7-named-lifetimes",
            "&T",
            "stage 8",
            "TokenKind::Lifetime",
        ],
    ) {
        return Err(format!("implicit lifetime syntax document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_implicit_borrow_acceptance(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-implicit-borrow-acceptance-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "check-phase7-implicit-borrow-acceptance",
            "borrow_interfaces",
            "complete result worlds",
            "Unknown",
            "stage 8",
            "7.8.4",
        ],
    ) {
        return Err(format!("implicit borrow acceptance document misses '{marker}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_capability_profile(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let manifest = fs::read_to_string(root.join("spec/capability-profile-v1.txt"))?;
    let profile = nera::CapabilityProfile::parse(&manifest)?;
    profile.check_implementation()?;

    let doc = fs::read_to_string(root.join("docs/stage7-capability-profile-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-8-4",
            "check-phase7-capability-profile",
            profile.profile(),
            profile.language(),
            profile.runtime(),
            profile.verifier(),
            profile.interpreter(),
            profile.target(),
            profile.backend(),
            profile.formal_checker(),
            "schema-only",
            "rejected-with-diagnostic",
            "erased-after-validation",
            "7.8.5",
        ],
    ) {
        return Err(format!("capability profile document misses '{marker}'").into());
    }
    for feature in profile.features() {
        if !doc.contains(feature.id())
            || !doc.contains(feature.limit())
            || !doc.contains(feature.check())
        {
            return Err(format!(
                "capability profile document does not account for '{}'",
                feature.id()
            )
            .into());
        }
    }
    let config = fs::read_to_string(root.join("src/session/config.rs"))?;
    if !config.contains("current_capability_profile")
        || config.contains("pub const RUNTIME_PROFILE")
        || config.contains("pub const VERIFIER_PROFILE")
    {
        return Err(
            "compilation session does not use the capability profile as its defaults".into(),
        );
    }
    let cli = fs::read_to_string(root.join("src/main.rs"))?;
    let verification_text = fs::read_to_string(root.join("src/verification/text.rs"))?;
    if !cli.contains("current_capability_profile")
        || !cli.contains("capability-profile:")
        || !verification_text.contains("effective capability profile:")
    {
        return Err("frontend/run/build/verify do not report the registered profile".into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_interface_artifact(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-interface-artifact-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-8-5",
            "check-phase7-interface-artifact",
            "InterfaceArtifactVersion::V1",
            "InterfaceInputIdentity",
            "InterfaceDeclarationIdentity",
            "InterfaceInstanceIdentity",
            "BorrowResultRelation",
            "matches_analysis",
            "schema-only",
            "7.8.6",
        ],
    ) {
        return Err(format!("interface artifact document misses '{marker}'").into());
    }
    let implementation = fs::read_to_string(root.join("src/module_interface.rs"))?;
    if let Some(marker) = missing_marker(
        &implementation,
        &[
            "InterfaceArtifactVersion::V1",
            "InterfaceInputIdentity::from_input",
            "ConcreteInstance",
            "borrow_result_alternatives",
            "matches_analysis",
            "FrontendNotAccepted",
        ],
    ) {
        return Err(format!("interface artifact implementation misses '{marker}'").into());
    }
    if implementation.contains("ProgramVerification")
        || implementation.contains("is_checked: bool")
        || implementation.contains("DefaultHasher")
    {
        return Err("interface artifact contains verdict or hash authorization state".into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_stage_acceptance(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let doc = fs::read_to_string(root.join("docs/stage7-8-acceptance-v1.md"))?;
    if let Some(marker) = missing_marker(
        &doc,
        &[
            "stage7-8-6",
            "check-phase7-stage-acceptance",
            "check-rust",
            "stage7_8_acceptance",
            "InterfaceArtifact",
            "20,000",
            "阶段 8.1",
        ],
    ) {
        return Err(format!("stage 7 acceptance document misses '{marker}'").into());
    }
    for fixture in [
        "spec/cases/modules/stage7-acceptance-app.nera",
        "spec/cases/modules/stage7-acceptance-ownership.nera",
    ] {
        if !root.join(fixture).is_file() {
            return Err(format!("stage 7 acceptance fixture is missing: {fixture}").into());
        }
    }
    Ok(())
}
