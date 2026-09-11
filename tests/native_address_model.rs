#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::backend::{
    X86_64_UNKNOWN_LINUX_GNU, X86_64AbiParameterLocation, X86_64CallerStackLocation,
};
use nera::{
    CfgAnalysisConfig, VirExecutionErrorKind, VirInstruction, VirType, interpret, verify_program,
};

#[test]
fn checked_address_model_fixture_has_a_fixed_observation() {
    for condition in ["true", "false"] {
        let source = include_str!("../spec/cases/verify/native-address-model.nera")
            .replace("return true;", &format!("return {condition};"));
        frontend_checks::checked("native-address-model.nera", &source, 42);
    }
}

#[test]
fn pointer_carriers_use_ordinary_slots_and_erase_permission_abi() {
    let output = frontend_checks::accepted(
        "native-address-model.nera",
        include_str!("../spec/cases/verify/native-address-model.nera"),
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let planning = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .unwrap();
    let mut seen = [false; 4];
    for function in resolved.runtime().functions {
        let plan = planning.function(function.id).unwrap();
        assert_eq!(
            plan.incoming_parameters().len(),
            function
                .signature
                .parameters
                .iter()
                .filter(|ty| **ty != VirType::Permission)
                .count()
        );
        for block in &function.blocks {
            for parameter in &block.parameters {
                assert_eq!(
                    plan.frame().value_slot(parameter.id).is_none(),
                    parameter.ty == VirType::Permission
                );
            }
            for spanned in &block.instructions {
                let result = match spanned.instruction {
                    VirInstruction::RawAddress {
                        result,
                        source_permission,
                        ..
                    } => {
                        seen[0] = true;
                        assert!(plan.frame().value_slot(source_permission).is_none());
                        result
                    }
                    VirInstruction::PointerOffset { result, .. } => {
                        seen[1] = true;
                        result
                    }
                    VirInstruction::PointerCompare { result, .. } => {
                        seen[2] = true;
                        result
                    }
                    VirInstruction::PointerDistance { result, .. } => {
                        seen[3] = true;
                        result
                    }
                    _ => continue,
                };
                assert!(plan.frame().value_slot(result.id).is_some());
            }
        }
        if function.name == "probe" {
            assert_eq!(plan.incoming_parameters().len(), 8);
            for parameter in &plan.incoming_parameters()[..6] {
                assert!(matches!(
                    parameter.source(),
                    X86_64AbiParameterLocation::Register(_)
                ));
            }
            for (slot, parameter) in plan.incoming_parameters()[6..].iter().enumerate() {
                assert_eq!(
                    parameter.source(),
                    X86_64AbiParameterLocation::CallerStack(X86_64CallerStackLocation::from_slot(
                        u32::try_from(slot).unwrap()
                    ))
                );
            }
        }
    }
    assert_eq!(seen, [true; 4]);
}

#[test]
fn wrong_raw_source_permission_faults_but_does_not_change_machine_code() {
    let output = frontend_checks::accepted(
        "permission-erasure.nera",
        "fn main() -> u64 { let a = alloc<u64>(1); let b = alloc<u64>(1);
         let x = &raw *a; let same = x == x; free(a); free(b);
         if same { return 42; } return 0; }",
    );
    let baseline = output.vir().unwrap().resolve().unwrap();
    assert!(
        verify_program(&baseline, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert!(interpret(baseline.runtime()).is_ok());
    let mut unit = output.vir().unwrap().as_unit().clone();
    let instructions = &mut unit.runtime.functions[0].blocks[0].instructions;
    let wrong_permission = instructions
        .iter()
        .filter_map(|i| match i.instruction {
            VirInstruction::Allocate {
                permission_result, ..
            } => Some(permission_result.id),
            _ => None,
        })
        .nth(1)
        .unwrap();
    let raw = instructions
        .iter_mut()
        .find_map(|i| match &mut i.instruction {
            VirInstruction::RawAddress {
                source_permission, ..
            } => Some(source_permission),
            _ => None,
        })
        .unwrap();
    assert_ne!(*raw, wrong_permission);
    *raw = wrong_permission;
    // A well-typed SSA permission is not proof that it covers this allocation.
    let validated = unit.into_validated().unwrap();
    let mutated = validated.resolve().unwrap();
    let rejected = verify_program(&mutated, CfgAnalysisConfig::default()).unwrap();
    assert!(rejected.diagnostics().iter().any(|d| {
        d.provenance_notes()
            .iter()
            .any(|n| n.issue == nera::verifier::provenance::ProvenanceIssue::MissingPermission)
    }));
    assert!(!rejected.is_memory_checked_core0());
    assert!(matches!(
        interpret(mutated.runtime()).unwrap_err().kind(),
        VirExecutionErrorKind::PermissionMismatch { .. }
    ));
    let assembly = |runtime| {
        let machine = X86_64_UNKNOWN_LINUX_GNU.codegen_program(runtime).unwrap();
        X86_64_UNKNOWN_LINUX_GNU.emit_assembly(&machine).unwrap()
    };
    assert_ne!(
        baseline.runtime().as_runtime().stable_dump(),
        mutated.runtime().as_runtime().stable_dump()
    );
    assert_eq!(assembly(baseline.runtime()), assembly(mutated.runtime()));
    // Deliberately do not execute the unchecked native mutation. Erasure does
    // not turn a structurally valid artifact into a memory-safety guarantee.
}
