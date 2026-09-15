use std::{error::Error, fs, path::Path};

use super::missing_marker;

pub(in crate::regression) fn check_phase7_borrow_baseline_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let baseline = fs::read_to_string(root.join("docs/stage7-borrow-baseline-v1.md"))?;
    if let Some(required) = missing_marker(
        &baseline,
        &[
            "Created --activate--> ActiveShared | ActiveMutable",
            "max_active_loans_per_case` | 256",
            "max_aliases_per_loan` | 256",
            "max_region_constraints_per_function` | 4096",
            "max_reborrow_depth` | 64",
            "ActiveLoanBudget",
            "LoanLoopWidening",
        ],
    ) {
        return Err(format!("borrow baseline is missing frozen rule '{required}'").into());
    }

    let hir_types = fs::read_to_string(root.join("src/frontend/hir/types.rs"))?;
    let hir = super::read_rust_module(root, "src/frontend/hir")?;
    let lowering = super::read_rust_module(root, "src/frontend/lower")?;
    let memory = fs::read_to_string(root.join("src/vir/memory.rs"))?;
    let abi = fs::read_to_string(root.join("src/vir/aggregate_abi.rs"))?;
    if !hir_types.contains("Reference {") || !hir.contains("Borrow {") {
        return Err("typed HIR no longer exposes the structural Reference/Borrow baseline".into());
    }
    if !lowering.contains("HirExpressionKind::Borrow { .. }") {
        return Err(
            "HIR lowering no longer handles Borrow explicitly and may silently fall through".into(),
        );
    }
    if !memory.contains("Reference,")
        || !abi.contains("VirInterfaceTransfer::BorrowShared")
        || !abi.contains("VirInterfaceTransfer::BorrowMutable")
    {
        return Err("VIR memory/ABI no longer exposes the frozen reference skeleton".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_hir_borrow_regions_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-hir-borrow-regions-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "HirVersion::V4",
            "LexicalScope | Parameter | Result | Inferred",
            "subregion <= superregion",
            "production reference syntax remains gated",
        ],
    ) {
        return Err(format!("HIR borrow-region acceptance is missing rule '{required}'").into());
    }

    let regions = fs::read_to_string(root.join("src/frontend/hir/regions.rs"))?;
    let program = fs::read_to_string(root.join("src/frontend/hir/program.rs"))?;
    if !regions.contains("pub enum HirRegionOrigin")
        || !regions.contains("pub struct HirRegionConstraint")
        || !program.contains("version: HirVersion::CURRENT")
        || !program.contains("validate_region_constraints")
    {
        return Err("canonical HIR borrow-region schema or validation is missing".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_vir_loan_schema_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-vir-loan-schema-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "VirUnitVersion::V6",
            "vir-unit-v6",
            "runtime-vir-v5",
            "LoanBegin | LoanAliasShared | LoanReborrow | LoanEnd",
            "production reference syntax remains gated",
        ],
    ) {
        return Err(format!("VIR loan-schema acceptance is missing rule '{required}'").into());
    }

    let borrow = fs::read_to_string(root.join("src/vir/borrow.rs"))?;
    let validate = super::read_rust_module(root, "src/vir/validate")?;
    let transfer = super::read_rust_module(root, "src/verifier/transfer")?;
    let interpreter = fs::read_to_string(root.join("src/vir/interpreter.rs"))?;
    let native = fs::read_to_string(root.join("src/backend/x86_64_plan.rs"))?;
    if !borrow.contains("pub struct VirBorrowEnvironment")
        || !borrow.contains("pub struct VirLoanEffect")
        || !validate.contains("validate_loan_instruction")
        || !validate.contains("borrow_region_is_subregion")
    {
        return Err("canonical VIR loan schema or structural validation is missing".into());
    }
    let interpreter_handles_loans = interpreter.contains("RuntimeLoanShadow");
    let native_handles_loans = native.contains("X86_64InstructionPlan::LoanReference");
    if !transfer.contains("fn loan_begin")
        || !transfer.contains("fn loan_end")
        || !interpreter_handles_loans
        || !native_handles_loans
    {
        return Err("a loan consumer neither implements nor explicitly rejects V6 effects".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_verifier_loans_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-verifier-loans-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "PermissionAuthority",
            "LoanRangeContained",
            "LoanCompatible",
            "LoanParentActive",
            "LoanEndedExactlyOnce",
            "production reference syntax remains gated",
        ],
    ) {
        return Err(format!("verifier-loan acceptance is missing rule '{required}'").into());
    }

    let resource = super::read_rust_module(root, "src/verifier/resource")?;
    let transfer = super::read_rust_module(root, "src/verifier/transfer")?;
    let interpreter = fs::read_to_string(root.join("src/vir/interpreter.rs"))?;
    let native = fs::read_to_string(root.join("src/backend/x86_64_plan.rs"))?;
    if !resource.contains("pub enum PermissionAuthority")
        || !resource.contains("pub struct AbstractLoan")
        || !transfer.contains("fn loan_alias_shared")
        || !transfer.contains("fn loan_reborrow")
        || !transfer.contains("fn loan_end")
    {
        return Err("canonical verifier loan domain or transfer rules are missing".into());
    }
    if !interpreter.contains("RuntimeLoanShadow") {
        return Err("the interpreter loan consumer is missing".into());
    }
    if !native.contains("X86_64InstructionPlan::LoanReference") {
        return Err("the native loan consumer is missing".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_loan_consumers_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-loan-consumers-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "RuntimeLoanShadow",
            "RuntimeLoanAuthority",
            "LoanReference",
            "ErasedLoan",
            "production reference syntax remains gated",
        ],
    ) {
        return Err(format!("loan-consumer acceptance is missing rule '{required}'").into());
    }

    let interpreter = fs::read_to_string(root.join("src/vir/interpreter.rs"))?;
    let shadow = fs::read_to_string(root.join("src/vir/interpreter/loan_shadow.rs"))?;
    let native_plan = fs::read_to_string(root.join("src/backend/x86_64_plan.rs"))?;
    let native_codegen = fs::read_to_string(root.join("src/backend/x86_64_codegen.rs"))?;
    if !interpreter.contains("RuntimeLoanShadow")
        || !shadow.contains("pub(super) struct RuntimeLoanShadow")
        || !shadow.contains("pub(super) fn reborrow")
        || !shadow.contains("pub(super) fn check_access")
    {
        return Err("bounded interpreter loan shadow is missing".into());
    }
    if !native_plan.contains("LoanReference")
        || !native_plan.contains("ErasedLoan")
        || !native_codegen.contains("X86_64InstructionPlan::LoanReference")
        || !native_codegen.contains("X86_64InstructionPlan::ErasedLoan")
    {
        return Err("native loan ghost erasure does not preserve reference pointer values".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_local_shared_borrow_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-local-shared-borrow-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "&place",
            "LoanAliasShared",
            "lexical scope end",
            "dynamic index",
            "stage 7.2.8",
        ],
    ) {
        return Err(format!("local shared-borrow acceptance is missing rule '{required}'").into());
    }

    let parser = fs::read_to_string(root.join("src/frontend/parser.rs"))?;
    let hir = super::read_rust_module(root, "src/frontend/hir")?;
    let lower = super::read_rust_module(root, "src/frontend/lower")?;
    if !parser.contains("fn parse_borrow")
        || !hir.contains("fn elaborate_borrow")
        || !lower.contains("fn lower_borrow")
        || !lower.contains("VirInstruction::LoanAliasShared")
        || !lower.contains("VirInstruction::LoanEnd")
    {
        return Err("the production local shared-borrow pipeline is incomplete".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_local_mutable_borrow_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-local-mutable-borrow-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "&mut place",
            "MoveOnly",
            "PermissionMove",
            "LoanBegin",
            "stage 7.2.8",
        ],
    ) {
        return Err(format!("local mutable-borrow acceptance is missing rule '{required}'").into());
    }

    let ast = fs::read_to_string(root.join("src/frontend.rs"))?;
    let parser = fs::read_to_string(root.join("src/frontend/parser.rs"))?;
    let hir = super::read_rust_module(root, "src/frontend/hir")?;
    let lower = super::read_rust_module(root, "src/frontend/lower")?;
    let assignment = fs::read_to_string(root.join("src/frontend/lower/assignment.rs"))?;
    let concrete = fs::read_to_string(root.join("src/frontend/lower/concrete.rs"))?;
    if !ast.contains("Reference {\n        pointee: Box<AstType>,\n        mutable: bool,")
        || !parser.contains("fn parse_borrow")
        || !hir.contains("fn elaborate_borrow")
        || !lower.contains("VirLoanKind::Mutable")
        || !lower.contains("VirInstruction::PermissionMove")
        || !assignment.contains("effect.source_pointer")
        || !concrete.contains("HirTypeKind::Reference {")
    {
        return Err("the production local mutable-borrow pipeline is incomplete".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_reborrow_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-reborrow-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "LoanReborrow",
            "child <= parent",
            "parent suspension",
            "explicit dereference",
            "stage7-2-8",
        ],
    ) {
        return Err(format!("reborrow acceptance is missing rule '{required}'").into());
    }

    let hir = super::read_rust_module(root, "src/frontend/hir")?;
    let validation = fs::read_to_string(root.join("src/frontend/hir/body_validation.rs"))?;
    let lower = super::read_rust_module(root, "src/frontend/lower")?;
    if !hir.contains("too many inferred borrow-region constraints")
        || !validation.contains("reborrow region is not constrained")
        || !lower.contains("VirInstruction::LoanReborrow")
        || !lower.contains("parent.range.contains(range)")
    {
        return Err("the production reborrow pipeline is incomplete".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_lowering_architecture_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-lowering-architecture-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "Validated HIR → Draft VIR → post-CFG effect planning",
            "InitializationEffects → LoanEndEffects → Seal",
            "RuntimeSemanticsUnsupported",
            "VerificationUnsupported",
            "TargetUnsupported",
            "stage7-2-9",
        ],
    ) {
        return Err(
            format!("lowering-architecture acceptance is missing rule '{required}'").into(),
        );
    }

    let lower = super::read_rust_module(root, "src/frontend/lower")?;
    let draft = fs::read_to_string(root.join("src/frontend/lower/draft.rs"))?;
    let post_cfg = fs::read_to_string(root.join("src/frontend/lower/post_cfg.rs"))?;
    let semantics = fs::read_to_string(root.join("src/vir/semantics.rs"))?;
    let validation = super::read_rust_module(root, "src/vir/validate")?;
    if !lower.contains("let mut draft_functions = Vec::new()")
        || !lower.contains("post_cfg::canonicalize_function")
        || !draft.contains("pub(super) enum DraftInstruction")
        || !post_cfg.contains("pub(super) const POST_CFG_PASSES")
        || !post_cfg.contains("seal_blocks")
        || !semantics.contains("pub const VIR_SYSTEM_SEMANTICS_V1")
        || !validation.contains("SemanticProfileMismatch")
    {
        return Err(
            "the production lowering architecture or semantic profile is incomplete".into(),
        );
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_nll_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-nll-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "finite region-inclusion closure",
            "last SSA use",
            "lexical fallback",
            "LoanEndEffects",
            "stage7-2-10",
        ],
    ) {
        return Err(format!("NLL acceptance is missing rule '{required}'").into());
    }

    let loan_end = fs::read_to_string(root.join("src/frontend/lower/loan_end.rs"))?;
    let post_cfg = fs::read_to_string(root.join("src/frontend/lower/post_cfg.rs"))?;
    let vir = fs::read_to_string(root.join("src/vir.rs"))?;
    if !loan_end.contains("RegionSolution::solve")
        || !loan_end.contains("instruction_escapes_authority")
        || !loan_end.contains("remap_source_locations")
        || !post_cfg.contains("loan_end::plan")
        || !vir.contains("pub(crate) fn visit_operands")
    {
        return Err("the production NLL end-planning pipeline is incomplete".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_loan_cfg_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-guarded-loan-cfg-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "ConditionalResourceState",
            "per-block last-use",
            "early return",
            "dynamic instance",
            "stage7-2-11",
        ],
    ) {
        return Err(format!("loan-CFG acceptance is missing rule '{required}'").into());
    }

    let lower = super::read_rust_module(root, "src/frontend/lower")?;
    let loan_end = fs::read_to_string(root.join("src/frontend/lower/loan_end.rs"))?;
    let resource = super::read_rust_module(root, "src/verifier/resource")?;
    let transfer = super::read_rust_module(root, "src/verifier/transfer")?;
    let shadow = fs::read_to_string(root.join("src/vir/interpreter/loan_shadow.rs"))?;
    if lower.contains("borrows across branch or loop CFG require stage 7.2.11")
        || !loan_end.contains("Each block is planned independently")
        || !resource.contains("define_next_loan_instance")
        || !transfer.contains("require_previous_loan_instance_ended")
        || !shadow.contains("loan.activity != RuntimeLoanActivity::Ended")
    {
        return Err("the guarded loan-CFG or loop-instance pipeline is incomplete".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_reference_aggregate_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-reference-aggregate-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "AggregateErased",
            "Stored",
            "candidate envelope",
            "partial move",
            "HirVersion::V5",
            "VirUnitVersion::V7",
            "stage7-2-12",
        ],
    ) {
        return Err(format!("reference-aggregate acceptance is missing rule '{required}'").into());
    }

    let regions = fs::read_to_string(root.join("src/frontend/hir/regions.rs"))?;
    let hir_program = fs::read_to_string(root.join("src/frontend/hir/program.rs"))?;
    let vir = fs::read_to_string(root.join("src/vir.rs"))?;
    let dump = fs::read_to_string(root.join("src/vir/dump.rs"))?;
    let resource = super::read_rust_module(root, "src/verifier/resource")?;
    let transfer = super::read_rust_module(root, "src/verifier/transfer")?;
    if !regions.contains("AggregateErased")
        || !vir.contains("LoanAliasAuthority")
        || !vir.contains("LoanEndAuthority")
        || !hir_program.contains("version: HirVersion::CURRENT")
        || !vir.contains("version: VirUnitVersion::V28")
        || !dump.contains("runtime-vir-v17")
        || !resource.contains("Stored {")
        || !transfer.contains("move_authority_to_storage")
        || !transfer.contains("move_authority_from_storage")
    {
        return Err("the reference-bearing aggregate authority pipeline is incomplete".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_safe_slice_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-safe-slice-v1.md"))?;
    if let Some(required) = missing_marker(
        &acceptance,
        &[
            "SliceAddress",
            "pointer + length + permission + loan",
            "one-past",
            "conservative envelope",
            "shared subslice",
            "VirUnitVersion::V8",
            "stage7-2-13",
        ],
    ) {
        return Err(format!("safe-slice acceptance is missing rule '{required}'").into());
    }

    let parser = fs::read_to_string(root.join("src/frontend/parser.rs"))?;
    let hir = super::read_rust_module(root, "src/frontend/hir")?;
    let lower = super::read_rust_module(root, "src/frontend/lower")?;
    let vir = fs::read_to_string(root.join("src/vir.rs"))?;
    let dump = fs::read_to_string(root.join("src/vir/dump.rs"))?;
    let transfer = super::read_rust_module(root, "src/verifier/transfer")?;
    let shadow = fs::read_to_string(root.join("src/vir/interpreter/loan_shadow.rs"))?;
    if !parser.contains("AstType::Slice")
        || !hir.contains("intern_slice_type")
        || !lower.contains("lower_slice_borrow")
        || !vir.contains("SliceAddress")
        || !vir.contains("version: VirUnitVersion::V28")
        || !dump.contains("runtime-vir-v17")
        || !transfer.contains("pointer_within_slice_range_status")
        || !shadow.contains("range.start_bytes == range.end_bytes")
    {
        return Err("the safe-slice surface or loan pipeline is incomplete".into());
    }

    Ok(())
}

pub(in crate::regression) fn check_phase7_borrow_calls_regression(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-borrow-calls-v1.md"))?;
    if let Some(rule) = missing_marker(
        &acceptance,
        &[
            "unconditional skeleton",
            "parameter region",
            "escape",
            "VirUnitVersion::V9",
            "stage7-2-14",
        ],
    ) {
        return Err(format!("borrow-call acceptance is missing '{rule}'").into());
    }
    Ok(())
}

pub(in crate::regression) fn check_phase7_borrow_acceptance(
    root: &Path,
) -> Result<(), Box<dyn Error>> {
    let acceptance = fs::read_to_string(root.join("docs/stage7-borrow-acceptance-v1.md"))?;
    if let Some(rule) = missing_marker(
        &acceptance,
        &[
            "7.2.15",
            "Proven",
            "ghost non-interference",
            "7.6",
            "lexical fallback",
        ],
    ) {
        return Err(format!("borrow acceptance is missing '{rule}'").into());
    }
    Ok(())
}
