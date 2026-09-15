#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, VirRuntimeValue, analyze, interpret,
    verify_program,
};

fn accepted(source: &str) -> nera::FrontendOutput {
    frontend_checks::accepted("deferred-local.nera", source)
}

fn checked(source: &str, expected: u64) {
    frontend_checks::checked("deferred-local.nera", source, expected)
}

#[test]
fn scalar_and_nested_fields_can_be_initialized_without_a_value_placeholder() {
    checked(
        "fn main() -> u64 { let mut index: usize; let mut flag: bool;
      index = 1usize; flag = true; let values = [0, 42]; let selected = index;
      if selected < 2usize { if flag { return values[selected]; } } return 0; }",
        42,
    );
    checked(
        "fn main() -> u64 { let mut value: u64; value = 40; value = value + 2; return value; }",
        42,
    );
    checked(
        "struct Pair { flag: bool, word: u64, }
      fn main() -> u64 { let mut value: Pair; value.flag = true; let flag = &value.flag;
      value.word = 42; let whole = &value; if *flag { return whole.word; } return 0; }",
        42,
    );
    checked(
        "struct Pair { items: [u64; 2], other: (bool, u64), }
      fn main() -> u64 { let mut value: Pair; value.items[0] = 40; value.items[1] = 2;
      value.other.0 = true; value.other.1 = value.items[0] + value.items[1];
      let copied = value; return copied.other.1; }",
        42,
    );
}

#[test]
fn both_branches_establish_initialization_and_whole_assignment_is_supported() {
    checked(
        "fn main() -> u64 { let mut v: [u64; 3]; v[0] = 9; v = make(); return v[0] + v[1]; }
      fn make() -> [u64; 3] { let mut v: [u64; 3]; v[0] = 40; v[1] = 2; v[2] = 0; return v; }",
        42,
    );
    checked("struct S { items: [u64; 2], flag: bool, } fn main() -> u64 {
      let mut v: S; v.items[0] = 9; v.items = [40, 2]; v.flag = true; return v.items[0] + v.items[1]; }", 42);
    checked(
        "fn main() -> u64 { let mut value: u64; if choose() { value = 42; } else { value = 42; }
      return value; } fn choose() -> bool { return true; }",
        42,
    );
    checked(
        "fn main() -> u64 { let mut value: [u64; 2]; value = [40, 2]; return value[0] + value[1]; }",
        42,
    );
    checked(
        "fn main() -> u64 { let mut value: u64; if choose() { value = 1; }
      value = 42; return value; } fn choose() -> bool { return false; }",
        42,
    );
    checked(
        "fn main() -> u64 { let mut value: [u64; 2]; value[0] = 9;
      value = [40, 2]; value = value; return value[0] + value[1]; }",
        42,
    );
    checked(
        "fn main() -> u64 { let mut value: [u64; 2]; if choose() { value[0] = 9; }
      value = [40, 2]; return value[0] + value[1]; } fn choose() -> bool { return false; }",
        42,
    );
}

#[test]
fn reads_and_borrows_require_only_the_right_initialized_value_bytes() {
    for source in [
        "fn main() -> u64 { let mut value: u64; return value; }",
        "fn main() -> u64 { let mut value: u64; let r = &value; return 0; }",
        "fn main() -> u64 { let mut value: u64; let r = &mut value; *r = 42; return 0; }",
        "fn main() -> u64 { let mut value: [u64; 2]; value[0] = 1; let whole = value; return 0; }",
        "fn main() -> u64 { let mut value: [u64; 2]; value[0] = 1; let whole = &value; return 0; }",
        "fn main() -> u64 { let mut value: u64; if choose() { value = 42; } return value; }
         fn choose() -> bool { return false; }",
        "fn main() -> u64 { let mut lhs: u64; let mut rhs: u64; lhs = rhs; return lhs; }",
        "fn main() -> u64 { let mut value: [u64; 2]; value[0] = 1; value = value; return 0; }",
        "fn main() -> u64 { let mut value: [u64; 2]; value[0] = 1;
         let mut target = [2, 3]; target = value; return target[0]; }",
    ] {
        let output = accepted(source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        assert!(
            !verify_program(&resolved, CfgAnalysisConfig::default())
                .unwrap()
                .is_memory_checked_core0(),
            "{source}"
        );
        assert!(interpret(resolved.runtime()).is_err(), "{source}");
    }
}

#[test]
fn each_loop_declaration_starts_uninitialized_again() {
    checked(
        "fn main() -> u64 { let mut count = 0; while count < 2 {
        let mut value: u64; value = count; count = value + 1; } return count; }",
        2,
    );
    let source = "fn main() -> u64 { let mut count = 0; while count < 2 {
        let mut value: u64; if count == 0 { value = 42; }
        let copied = value; count = count + 1; } return 0; }";
    let output = accepted(source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert!(
        !verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert!(interpret(resolved.runtime()).is_err());
}

#[test]
fn storage_declaration_has_no_expression_and_keeps_precise_scalar_effects() {
    let output =
        accepted("fn main() -> u64 { let mut value: u64; value = 1; value = 42; return value; }");
    let hir = output.hir().unwrap();
    assert_eq!(hir.version(), nera::HirVersion::V21);
    let body = hir.functions()[0].body().unwrap();
    assert!(matches!(
        body.root.statements[0].kind,
        nera::HirStatementKind::Declare { .. }
    ));
    let unit = output.vir().unwrap().as_unit();
    assert_eq!(unit.version, nera::VirUnitVersion::V27);
    let instructions: Vec<_> = unit.runtime.functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect();
    assert_eq!(
        instructions
            .iter()
            .filter(|item| matches!(item.instruction, nera::VirInstruction::LocalStorage { .. }))
            .count(),
        1
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|item| matches!(item.instruction, nera::VirInstruction::StorageReset { .. }))
            .count(),
        1
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|item| matches!(item.instruction, nera::VirInstruction::Initialize { .. }))
            .count(),
        1
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|item| matches!(item.instruction, nera::VirInstruction::Store { .. }))
            .count(),
        1
    );
}

#[test]
fn deferred_standalone_resources_enums_and_zero_size_storage_remain_gated() {
    for source in [
        "fn main() { let mut value: Own<u64>; return; }",
        "fn main() { let mut value: &u64; return; }",
        "enum E { A, B(u64), } fn main() { let mut value: E; return; }",
        "enum E { A, B(u64), } struct S { e: E, } fn main() { let mut value: S; return; }",
        "struct Empty {} fn main() { let mut value: Empty; return; }",
        "fn main() { let mut value: [u64; 0]; return; }",
        "fn main() { let mut value: (); return; }",
        "fn main() { let mut value: [u64; 513]; return; }",
    ] {
        let output = analyze(&SourceFile::from_text("deferred-gate.nera", source));
        assert_eq!(
            output.status(),
            FrontendStatus::Unsupported,
            "{source}\n{:#?}",
            output.issues()
        );
        assert!(output.vir().is_none());
    }
    for source in [
        "fn main() { let value: u64; return; }",
        "fn main() { let mut value; return; }",
        "fn main() -> u64 { let value: u64; return value; }",
        "fn main() -> u64 { let mut value; return 0; }",
    ] {
        let output = analyze(&SourceFile::from_text("deferred-syntax.nera", source));
        assert_eq!(output.status(), FrontendStatus::Invalid);
        assert!(output.vir().is_none());
        assert!(!output.issues().is_empty());
    }
}

#[test]
fn storage_reset_mutations_cannot_keep_old_values_or_bypass_loans() {
    for (source, during_loan) in [
        (
            "fn main() -> u64 { let mut v: u64; v = 42; return v; }",
            false,
        ),
        (
            "fn main() -> u64 { let mut v: u64; v = 42; let r = &v; return *r; }",
            true,
        ),
    ] {
        let output = accepted(source);
        let mut unit = output.vir().unwrap().as_unit().clone();
        let instructions = &mut unit.runtime.functions[0].blocks[0].instructions;
        let reset = instructions
            .iter()
            .find(|item| matches!(item.instruction, nera::VirInstruction::StorageReset { .. }))
            .unwrap()
            .clone();
        if during_loan {
            let index = instructions
                .iter()
                .position(|item| matches!(item.instruction, nera::VirInstruction::LoanBegin { .. }))
                .unwrap();
            instructions.insert(index + 1, reset);
        } else {
            let initialize = instructions
                .iter_mut()
                .find(|item| matches!(item.instruction, nera::VirInstruction::Initialize { .. }))
                .unwrap();
            *initialize = reset;
        }
        unit.rebuild_source_map_from_runtime("deferred-local.nera", source.len());
        let validated = unit.into_validated().unwrap();
        let resolved = validated.resolve().unwrap();
        assert!(
            !verify_program(&resolved, CfgAnalysisConfig::default())
                .unwrap()
                .is_memory_checked_core0()
        );
        assert!(interpret(resolved.runtime()).is_err());
    }
}

#[test]
fn storage_reset_schema_rejects_resource_and_variant_shapes_and_old_versions() {
    for source in [
        "struct S { p: Own<u64>, } fn main() { let v = S { p: alloc<u64>(1) }; return; }",
        "enum E { A, B(u64), } fn main() { let v = E::B(42); return; }",
    ] {
        let output = accepted(source);
        let mut unit = output.vir().unwrap().as_unit().clone();
        let instructions = &mut unit.runtime.functions[0].blocks[0].instructions;
        let (pointer, permission, access, source_span) = instructions
            .iter()
            .find_map(|item| {
                if let nera::VirInstruction::LocalStorage {
                    pointer_result,
                    permission_result,
                    access,
                } = item.instruction
                {
                    Some((
                        pointer_result.id,
                        permission_result.id,
                        access,
                        item.source_span,
                    ))
                } else {
                    None
                }
            })
            .unwrap();
        let prefix = instructions
            .iter()
            .take_while(|item| {
                matches!(item.instruction, nera::VirInstruction::LocalStorage { .. })
            })
            .count();
        instructions.insert(
            prefix,
            nera::SpannedVirInstruction {
                instruction: nera::VirInstruction::StorageReset {
                    pointer,
                    permission,
                    access,
                },
                source_span,
            },
        );
        unit.rebuild_source_map_from_runtime("deferred-local.nera", source.len());
        assert!(unit.into_validated().is_err());
    }
    let output = accepted("fn main() { let mut v: u64; return; }");
    let mut unit = output.vir().unwrap().as_unit().clone();
    unit.version = nera::VirUnitVersion::V9;
    assert!(unit.into_validated().is_err());
}

#[test]
fn resetting_a_partial_subobject_preserves_initialized_siblings() {
    let source = "fn main() -> u64 { let mut v: [u64; 2]; v[0] = 1; v[1] = 42; return v[1]; }";
    let output = accepted(source);
    let mut unit = output.vir().unwrap().as_unit().clone();
    let initialize = unit.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .find(|item| matches!(item.instruction, nera::VirInstruction::Initialize { .. }))
        .unwrap();
    let nera::VirInstruction::Initialize {
        pointer,
        permission,
        access,
        ..
    } = initialize.instruction
    else {
        unreachable!()
    };
    initialize.instruction = nera::VirInstruction::StorageReset {
        pointer,
        permission,
        access,
    };
    unit.rebuild_source_map_from_runtime("deferred-local.nera", source.len());
    let validated = unit.into_validated().unwrap();
    let resolved = validated.resolve().unwrap();
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
}
