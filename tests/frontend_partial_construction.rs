#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{CfgAnalysisConfig, FrontendStatus, SourceFile, analyze, interpret, verify_program};

fn accepted(source: &str) -> nera::FrontendOutput {
    frontend_checks::accepted("partial-construction.nera", source)
}

fn checked(source: &str, expected: u64) {
    frontend_checks::checked("partial-construction.nera", source, expected)
}

#[test]
fn partial_owners_are_cleaned_without_becoming_complete() {
    for condition in ["true", "false"] {
        checked(
            &include_str!("../spec/cases/verify/partial-construction.nera")
                .replace("return true;", &format!("return {condition};")),
            42,
        );
    }
    checked(
        "struct Pair { left: Own<u64>, right: Own<u64>, }
      fn main() -> u64 { let mut value: Pair; return 42; }",
        42,
    );
    checked("struct Pair { left: Own<u64>, right: Own<u64>, }
      fn main() -> u64 { { let mut value: Pair; let a = alloc<u64>(1); *a = 1; value.left = a; } return 42; }", 42);
}

#[test]
fn nested_and_array_construction_restore_whole_values() {
    checked(
        "struct Inner { owner: Own<u64>, word: u64, } struct Outer { nested: Inner, flag: bool, }
      fn main() -> u64 { let mut value: Outer; let a = alloc<u64>(1); *a = 40;
      value.nested.owner = a; value.nested.word = 2; value.flag = true;
      let r = &value; let word = r.nested.word; let whole = value;
      let answer = whole.nested.owner; return *answer + word; }",
        42,
    );
    checked(
        "fn main() -> u64 { let mut value: [Own<u64>; 2];
      let a = alloc<u64>(1); *a = 20; let b = alloc<u64>(1); *b = 22;
      value[0] = a; value[1] = b; let whole = value;
      let x = whole[0]; let y = whole[1]; return *x + *y; }",
        42,
    );
}

#[test]
fn partially_constructed_references_preserve_and_end_authority() {
    checked(
        "struct Pair { left: &u64, right: &u64, }
      fn main() -> u64 { let a = 20; let b = 22; let mut value: Pair;
      value.left = &a; value.right = &b; let copied = value;
      let left = copied.left; let right = value.right; return *left + *right; }",
        42,
    );
    checked(
        "struct Pair { left: &mut u64, right: &mut u64, }
      fn main() -> u64 { let mut word = 40; { let mut value: Pair;
      value.left = &mut word; let reference = value.left; *reference = 42;
      value.left = reference; } return word; }",
        42,
    );
    checked(
        "struct Pair { left: &u64, right: &u64, }
      fn main() -> u64 { let a = 20; let b = 22; let mut value: Pair;
      value.left = &a; let alias = value.left; value.left = &b;
      let updated = value.left; return *alias + *updated; }",
        42,
    );
}

#[test]
fn initialized_sibling_borrow_does_not_require_a_complete_resource_object() {
    checked(
        "struct Slot { owner: Own<u64>, word: u64, } fn main() -> u64 {
      let mut value: Slot; value.word = 42; let r = &value.word; return *r; }",
        42,
    );
}

#[test]
fn double_drop_and_omitted_loop_cleanup_fail_independent_consumers() {
    let source = "struct Slot { owner: Own<u64>, } fn main() -> u64 {
      let mut value: Slot; let a = alloc<u64>(1); *a = 42; value.owner = a;
      let taken = value.owner; let answer = *taken; return answer; }";
    let mut unit = accepted(source).vir().unwrap().as_unit().clone();
    let block = &mut unit.runtime.functions[0].blocks[0];
    let index = block
        .instructions
        .iter()
        .rposition(|inst| matches!(inst.instruction, nera::VirInstruction::DropOwn { .. }))
        .unwrap();
    block
        .instructions
        .insert(index + 1, block.instructions[index].clone());
    unit.rebuild_source_map_from_runtime("double-drop.nera", source.len());
    let unit = unit.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    assert!(
        !verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert!(interpret(resolved.runtime()).is_err());

    let source = include_str!("../spec/cases/verify/partial-construction-loop.nera");
    let mut unit = accepted(source).vir().unwrap().as_unit().clone();
    for block in &mut unit.runtime.functions[0].blocks {
        for inst in &mut block.instructions {
            if let nera::VirInstruction::ObjectDrop { condition, .. } = inst.instruction {
                inst.instruction = nera::VirInstruction::Check { condition };
            }
        }
    }
    unit.rebuild_source_map_from_runtime("missing-loop-cleanup.nera", source.len());
    let unit = unit.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    for max_guarded_cases_per_block in [1, 16] {
        assert!(
            !verify_program(
                &resolved,
                CfgAnalysisConfig {
                    max_guarded_cases_per_block,
                    ..CfgAnalysisConfig::default()
                }
            )
            .unwrap()
            .is_memory_checked_core0()
        );
    }
    assert!(interpret(resolved.runtime()).is_err());
}

#[test]
fn replacement_temporaries_and_refill_after_whole_move_keep_cleanup_armed() {
    checked(
        "struct Pair { left: Own<u64>, right: Own<u64>, }
      fn main() -> u64 { let mut value: Pair; let a = alloc<u64>(1); *a = 1; value.left = a;
      let b = alloc<u64>(1); *b = 20; let c = alloc<u64>(1); *c = 22;
      value = Pair { left: b, right: c }; let moved = value;
      let d = alloc<u64>(1); *d = 3; value.left = d;
      let x = moved.left; let y = moved.right; return *x + *y; }",
        42,
    );
}

#[test]
fn loop_reentry_break_and_continue_clean_partial_storage() {
    checked(
        "struct Pair { left: Own<u64>, right: Own<u64>, }
      fn main() -> u64 { let mut count = 0; while count < 3 {
      let mut value: Pair; let a = alloc<u64>(1); *a = count; value.left = a;
      count = count + 1; if count == 1 { continue; } if count == 2 { break; }
      } return count; }",
        2,
    );
}

#[test]
fn missing_fields_cannot_be_observed_or_borrowed() {
    for tail in [
        "let whole = value; return 0;",
        "let r = &value; return 0;",
        "let x = value.right; return *x;",
    ] {
        let source = format!("struct Pair {{ left: Own<u64>, right: Own<u64>, }}
          fn main() -> u64 {{ let mut value: Pair; let a = alloc<u64>(1); *a = 42; value.left = a; {tail} }}");
        let output = accepted(&source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        assert!(
            !verify_program(&resolved, CfgAnalysisConfig::default())
                .unwrap()
                .is_memory_checked_core0()
        );
        assert!(interpret(resolved.runtime()).is_err());
    }
}

#[test]
fn resource_storage_reset_requires_empty_payload_and_real_write_authority() {
    for source in [
        "struct Slot { owner: Own<u64>, } fn main() -> u64 {
          let mut value: Slot; let a = alloc<u64>(1); *a = 42; value.owner = a; return 42; }",
        "struct Slot { owner: &mut u64, } fn main() -> u64 {
          let mut word = 42; let mut value: Slot; value.owner = &mut word; return 42; }",
    ] {
        let original = accepted(source).vir().unwrap().as_unit().clone();
        for mutation in 0..3 {
            let mut unit = original.clone();
            let block = &mut unit.runtime.functions[0].blocks[0];
            let reset = block
                .instructions
                .iter()
                .find(|inst| {
                    matches!(
                        inst.instruction,
                        nera::VirInstruction::ResourceStorageReset { .. }
                    )
                })
                .unwrap()
                .instruction
                .clone();
            let last_cleanup = block
                .instructions
                .iter()
                .rposition(|inst| {
                    matches!(inst.instruction, nera::VirInstruction::ObjectDrop { .. })
                })
                .unwrap();
            match mutation {
                0 => {
                    block.instructions[last_cleanup].instruction = reset;
                }
                1 => {
                    let nera::VirInstruction::ObjectDrop { condition, .. } =
                        block.instructions[last_cleanup].instruction
                    else {
                        unreachable!()
                    };
                    let flag = block
                        .instructions
                        .iter_mut()
                        .find(|inst| {
                            matches!(inst.instruction,
                        nera::VirInstruction::Constant { result, .. } if result.id == condition)
                        })
                        .unwrap();
                    let nera::VirInstruction::Constant { value, .. } = &mut flag.instruction else {
                        unreachable!()
                    };
                    *value = nera::VirConstant::Bool(false);
                }
                _ => {
                    // Preserve all site/origin indices while deleting cleanup.
                    block.instructions[last_cleanup].instruction = nera::VirInstruction::Check {
                        condition: block
                            .instructions
                            .iter()
                            .find_map(|inst| match inst.instruction {
                                nera::VirInstruction::Constant {
                                    result,
                                    value: nera::VirConstant::Bool(true),
                                } => Some(result.id),
                                _ => None,
                            })
                            .unwrap(),
                    };
                }
            }
            if mutation != 1 {
                unit.rebuild_source_map_from_runtime("partial-construction.nera", source.len());
                // Rebuild diagnostic anchors only; retain the actual region
                // scopes, inclusions, loan ids and runtime effects.
                let origin = |owner| {
                    unit.source_map
                        .origin_at(nera::VirLocation::FunctionEntry { function: owner })
                        .unwrap()
                        .id
                };
                let regions = unit
                    .borrows
                    .regions()
                    .iter()
                    .cloned()
                    .map(|mut region| {
                        region.source_origin = origin(region.owner);
                        region
                    })
                    .collect();
                let constraints = unit
                    .borrows
                    .constraints()
                    .iter()
                    .copied()
                    .map(|mut constraint| {
                        constraint.source_origin = origin(constraint.owner);
                        constraint
                    })
                    .collect();
                unit.borrows = nera::VirBorrowEnvironment::from_tables(regions, constraints);
            }
            let unit = unit.into_validated().unwrap();
            let resolved = unit.resolve().unwrap();
            assert!(
                !verify_program(&resolved, CfgAnalysisConfig::default())
                    .unwrap()
                    .is_memory_checked_core0(),
                "mutation {mutation}: {source}"
            );
            assert!(
                interpret(resolved.runtime()).is_err(),
                "mutation {mutation}: {source}"
            );
        }
    }
}

#[test]
fn empty_resource_storage_does_not_create_a_value_and_old_schema_is_rejected() {
    let source = "struct Slot { owner: Own<u64>, } fn main() { let mut value: Slot; return; }";
    let output = accepted(source);
    assert_eq!(output.hir().unwrap().version(), nera::HirVersion::V20);
    let unit = output.vir().unwrap().as_unit();
    assert_eq!(unit.version, nera::VirUnitVersion::V25);
    assert!(unit.stable_dump().contains("resource.storage.reset"));
    let mut old = unit.clone();
    old.version = nera::VirUnitVersion::V10;
    assert!(old.into_validated().is_err());
    for source in [
        "fn main() { let mut value: Own<u64>; return; }",
        "enum E { A(Own<u64>), B, } fn main() { let mut value: E; return; }",
        "struct S { pointer: ptr<u64>, } fn main() { let mut value: S; return; }",
    ] {
        assert_eq!(
            analyze(&SourceFile::from_text("gated.nera", source)).status(),
            FrontendStatus::Unsupported
        );
    }
}

#[test]
fn reset_cannot_discard_live_loans_or_allow_stale_iteration_reads() {
    for source in [
        "struct Pair { left: Own<u64>, right: Own<u64>, }
          fn main() -> u64 { let mut count = 0; while count < 2 {
          let mut value: Pair; if count == 0 { let a = alloc<u64>(1); *a = 42; value.left = a; }
          let moved = value.left; count = count + 1; } return count; }",
        "struct Slot { reference: &mut u64, word: u64, }
          fn main() -> u64 { let mut a = 40; let mut b = 2; let mut value: Slot;
          value.reference = &mut a; value.word = 42; let alias = &value;
          value.reference = &mut b; return alias.word; }",
    ] {
        let output = accepted(source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        assert!(
            !verify_program(&resolved, CfgAnalysisConfig::default())
                .unwrap()
                .is_memory_checked_core0(),
            "{source}"
        );
        assert!(interpret(resolved.runtime()).is_err());
    }
}
