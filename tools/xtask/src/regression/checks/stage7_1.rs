use std::{error::Error, fs, path::Path};

pub(in crate::regression) fn check_phase7_identity_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    for path in [
        "src/frontend/lower.rs",
        "src/frontend/lower/abi.rs",
        "src/frontend/lower/contract.rs",
    ] {
        if fs::read_to_string(root.join(path))?.contains("std::ptr::eq") {
            return Err("HIR lowering still depends on Rust object address identity".into());
        }
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_capability_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    for (path, forbidden) in [
        ("src/frontend/hir.rs", "type_contains_resource"),
        ("src/verifier/transfer.rs", "trivial_object_status"),
    ] {
        if fs::read_to_string(root.join(path))?.contains(forbidden) {
            return Err(format!("{path} restored duplicate classifier {forbidden}").into());
        }
    }
    for path in [
        "src/frontend/hir/body_validation.rs",
        "src/frontend/lower/concrete.rs",
        "src/verifier/transfer.rs",
        "src/vir/interpreter.rs",
        "src/backend/x86_64_plan.rs",
    ] {
        if !fs::read_to_string(root.join(path))?.contains("type_capabilities(") {
            return Err(format!("{path} does not consume canonical type capabilities").into());
        }
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_resource_payload_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let resource = super::read_rust_module(root, "src/verifier/resource")?;
    if !resource.contains("resource_payloads: BTreeMap<ResourcePayloadKey, MovePathState>")
        || !resource.contains("pub type ResourceCase = ResourceState")
    {
        return Err(
            "typed payload is no longer owned by the canonical ResourceCase/ObjectState".into(),
        );
    }
    let interpreter = fs::read_to_string(root.join("src/vir/interpreter.rs"))?;
    if !interpreter.contains("resource_payloads: BTreeMap<RuntimeResourcePayloadKey")
        || interpreter.contains("decode_runtime_pointer")
    {
        return Err(
            "interpreter typed shadow payload is absent or pointer identity is decoded from bytes"
                .into(),
        );
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_guarded_resource_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let guarded = fs::read_to_string(root.join("src/verifier/guarded.rs"))?;
    if !guarded.contains("cases: Vec<ResourceCase>")
        || !guarded.contains("GuardedStatePrecisionLoss")
        || guarded.contains("transfer_instruction")
    {
        return Err(
            "guarded analysis must own bounded ResourceCase sets without a second transfer engine"
                .into(),
        );
    }
    let cfg = fs::read_to_string(root.join("src/verifier/cfg.rs"))?;
    if !cfg.contains("GuardedReduction::PreserveGuards")
        || !cfg.contains("evaluate_conditional_block")
        || !cfg.contains("let evaluated = evaluate_block_step(")
        || !cfg.contains("transfer_instruction_with_contracts_and_memory(")
    {
        return Err(
            "CFG analysis no longer replays guarded cases through canonical instruction transfer"
                .into(),
        );
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_copy_move_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let hir = super::read_rust_module(root, "src/frontend/hir")?;
    let validation = fs::read_to_string(root.join("src/frontend/hir/body_validation.rs"))?;
    let assignment = fs::read_to_string(root.join("src/frontend/lower/assignment.rs"))?;
    if !hir.contains("pub enum HirUseMode")
        || !validation.contains("canonical_use_mode")
        || !assignment.contains("source_mode,")
    {
        return Err(
            "Copy/Move must be selected in typed HIR, independently validated, and preserved by assignment refinement"
                .into(),
        );
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_builtin_drop_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let vir = fs::read_to_string(root.join("src/vir.rs"))?;
    let lowering = super::read_rust_module(root, "src/frontend/lower")?;
    let transfer = super::read_rust_module(root, "src/verifier/transfer")?;
    let cfg = fs::read_to_string(root.join("src/verifier/cfg.rs"))?;
    if !vir.contains("DropOwn {") || !vir.contains("ObjectDrop {") {
        return Err("VIR no longer exposes scalar and object builtin-drop effects".into());
    }
    if !lowering.contains("emit_drops_not_in_environment")
        || !lowering.contains("VirGeneratedReason::ImplicitDrop")
    {
        return Err("lowering no longer uses the unified generated scope-cleanup path".into());
    }
    if !transfer.contains("DropFlagKnown") || !cfg.contains("OwnershipConserved") {
        return Err("verifier no longer checks drop flags and normal-exit conservation".into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_aggregate_transfer_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let abi = fs::read_to_string(root.join("src/vir/aggregate_abi.rs"))?;
    let lowering = super::read_rust_module(root, "src/frontend/lower")?;
    let contract = fs::read_to_string(root.join("src/frontend/lower/contract.rs"))?;
    let transfer = fs::read_to_string(root.join("src/verifier/transfer/call.rs"))?;
    if !abi.contains("return Ok(VirAbiValue::IndirectAggregate { access });")
        || !abi.contains("VirInterfaceTransfer::Move")
    {
        return Err("canonical ABI no longer classifies owning aggregates as indirect Move".into());
    }
    if !contract.contains("result_initialization")
        || !lowering.contains("initial_access_drop_flag(storage.access, false")
    {
        return Err(
            "lowering no longer closes owning aggregate call storage and drop state".into(),
        );
    }
    if !transfer.contains("AggregateAbiPayloadValid")
        || !transfer.contains("install_aggregate_abi_payloads")
    {
        return Err("verifier no longer checks aggregate ABI payload transfer".into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_resource_acceptance(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let guarded = fs::read_to_string(root.join("src/verifier/guarded.rs"))?;
    let cfg = fs::read_to_string(root.join("src/verifier/cfg.rs"))?;
    let interpreter = fs::read_to_string(root.join("src/vir/interpreter.rs"))?;
    let fuzz = fs::read_to_string(root.join("src/bin/nera_verifier_fuzz.rs"))?;
    if !guarded.contains("guards_have_exact_conjunctive_union")
        || !guarded.contains("same_resource_facts")
    {
        return Err(
            "guarded normalization no longer preserves resource-distinct alternatives".into(),
        );
    }
    if !cfg.contains("a consumed token may cross") || !interpreter.contains("RuntimeBlockArgument")
    {
        return Err("CFG consumers no longer transport permission tombstone state".into());
    }
    if !fuzz.contains("RESOURCE_CFG_VERIFIER_CASES") || !fuzz.contains("resource_cfg_checked") {
        return Err("verifier fuzz no longer covers resource CFG joins and back edges".into());
    }
    Ok(())
}
