#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{CfgAnalysisConfig, VirRuntimeValue, interpret, verify_program};

fn accepted(source: &str) -> nera::FrontendOutput {
    frontend_checks::accepted("partial-refill.nera", source)
}

fn checked(source: &str, expected: u64) {
    frontend_checks::checked("partial-refill.nera", source, expected)
}

#[test]
fn owner_leaf_refill_preserves_siblings_and_reestablishes_whole_move() {
    checked(
        "struct Pair { left: Own<u64>, right: Own<u64>, }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 20; let b = alloc<u64>(1); *b = 22;
      let mut pair = Pair { left: a, right: b }; let first = pair.left;
      pair.left = first; let whole = pair; let left = whole.left; let right = whole.right;
      return *left + *right; }",
        42,
    );
    checked(
        "struct Pair { left: Own<u64>, right: Own<u64>, }
      struct Outer { nested: Pair, word: u64, }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 20; let b = alloc<u64>(1); *b = 22;
      let mut v = Outer { nested: Pair { left: a, right: b }, word: 0 };
      let old = v.nested.left; let sibling = v.word; v.nested.left = old;
      let whole = v; let left = whole.nested.left; let right = whole.nested.right;
      return *left + *right + sibling; }",
        42,
    );
}

#[test]
fn present_owner_replacement_and_self_assignment_are_resource_safe() {
    checked(
        "struct Slot { value: Own<u64>, } fn main() -> u64 {
      let old = alloc<u64>(1); *old = 1; let mut v = Slot { value: old };
      let replacement = alloc<u64>(1); *replacement = 42; v.value = replacement;
      v.value = v.value; let answer = v.value; return *answer; }",
        42,
    );
}

#[test]
fn mutable_reference_refill_and_shared_alias_replacement_preserve_authority() {
    checked(
        "struct Pair { left: &mut u64, right: &mut u64, }
      fn main() -> u64 { let mut left = 20; let mut right = 22;
      let mut pair = Pair { left: &mut left, right: &mut right }; let first = pair.left;
      pair.left = first; let whole = pair; let a = whole.left; let b = whole.right;
      return *a + *b; }",
        42,
    );
    checked(
        "struct Slot { value: &u64, } fn main() -> u64 {
      let left = 20; let right = 22; let mut v = Slot { value: &left };
      let alias = v.value; v.value = &right; let updated = v.value;
      return *alias + *updated; }",
        42,
    );
}

#[test]
fn branch_local_refill_restores_only_its_own_path() {
    checked(
        "struct Pair { left: Own<u64>, right: Own<u64>, }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 20; let b = alloc<u64>(1); *b = 22;
      let mut pair = Pair { left: a, right: b };
      if choose() { let moved = pair.left; pair.left = moved; }
      else { let moved = pair.right; pair.right = moved; }
      let whole = pair; let left = whole.left; let right = whole.right; return *left + *right;
      } fn choose() -> bool { return true; }",
        42,
    );
    checked(
        "struct Slot { value: Own<u64>, } fn main() -> u64 {
      let old = alloc<u64>(1); *old = 1; let mut v = Slot { value: old };
      if choose() { let moved = v.value; }
      let replacement = alloc<u64>(1); *replacement = 42; v.value = replacement;
      let answer = v.value; return *answer; } fn choose() -> bool { return false; }",
        42,
    );
}

#[test]
fn nested_resource_objects_can_be_moved_refilled_and_self_assigned() {
    checked("struct Inner { owner: Own<u64>, word: u64, } struct Outer { nested: Inner, sibling: Own<u64>, }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 40; let b = alloc<u64>(1); *b = 2;
      let v = Outer { nested: Inner { owner: a, word: 9 }, sibling: b };
      let moved = v.nested; let answer = moved.owner; return *answer; }", 40);
    checked(
        "struct Inner { owner: Own<u64>, word: u64, } struct Outer { nested: Inner, sibling: u64, }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 40;
      let mut v = Outer { nested: Inner { owner: a, word: 2 }, sibling: 9 };
      let moved = v.nested; v.nested = moved; v.nested = v.nested;
      let whole = v; let answer = whole.nested.owner; return *answer + whole.nested.word; }",
        42,
    );
    checked(
        "struct Inner { value: &mut u64, word: u64, } struct Outer { nested: Inner, sibling: u64, }
      fn main() -> u64 { let mut word = 40;
      let mut v = Outer { nested: Inner { value: &mut word, word: 2 }, sibling: 9 };
      let moved = v.nested; v.nested = moved; v = v;
      let reference = v.nested.value; return *reference + v.nested.word; }",
        42,
    );
    checked(
        "struct Slot { value: &u64, } fn main() -> u64 { let word = 42;
      let mut v = Slot { value: &word }; let copy = v; v = v; let r = v.value; return *r; }",
        42,
    );
}

#[test]
fn missing_wrong_path_and_repeated_refill_inputs_do_not_create_complete_objects() {
    for source in [
        "struct Pair { left: Own<u64>, right: Own<u64>, } fn main() -> u64 {
          let a = alloc<u64>(1); *a = 1; let b = alloc<u64>(1); *b = 2;
          let mut pair = Pair { left: a, right: b }; let first = pair.left;
          let again = pair.left; return *again; }",
        "struct Pair { left: Own<u64>, right: Own<u64>, } fn main() -> u64 {
          let a = alloc<u64>(1); *a = 1; let b = alloc<u64>(1); *b = 2;
          let mut pair = Pair { left: a, right: b }; let first = pair.left;
          pair.right = first; let whole = pair; return 0; }",
        "struct Pair { left: Own<u64>, right: Own<u64>, } fn main() -> u64 {
          let a = alloc<u64>(1); *a = 1; let b = alloc<u64>(1); *b = 2;
          let mut pair = Pair { left: a, right: b }; if choose() { let first = pair.left; }
          let whole = pair; return 0; } fn choose() -> bool { return true; }",
        "struct Slot { value: Own<u64>, } fn main() -> u64 {
          let a = alloc<u64>(1); *a = 42; let mut v = Slot { value: a }; let moved = v.value;
          v.value = moved; return *moved; }",
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
fn refill_reestablishes_whole_borrows_and_shared_copy() {
    checked(
        "struct Slot { owner: Own<u64>, word: u64, }
      fn main() -> u64 { let owner = alloc<u64>(1); *owner = 1;
      let mut v = Slot { owner: owner, word: 40 }; let moved = v.owner;
      v.owner = moved; let r = &mut v; r.word = 42; return r.word; }",
        42,
    );
    checked(
        "struct Slot { value: &u64, word: u64, } fn main() -> u64 {
      let left = 20; let right = 22; let mut v = Slot { value: &left, word: 0 };
      let alias = v.value; v.value = &right; let copy = v; let r = &copy;
      let word = r.word; let value = copy.value; return *alias + *value + word; }",
        42,
    );
}

#[test]
fn resource_refill_evaluates_dynamic_destination_once_before_rhs() {
    // The opaque function's returned index is not a safety proof. This test
    // independently checks runtime ordering/count; exact-index safety is
    // covered by indexed_and_tuple_resource_paths_refill_independently.
    let source = "fn main() -> u64 { let mut count = 0;
      let a = alloc<u64>(1); *a = 42; let mut v = [a]; let moved = v[0];
      v[next(&mut count)] = moved; let answer = v[0]; return count + *answer;
      } fn next(count: &mut u64) -> usize { *count = *count + 1; return 0usize; }";
    let output = accepted(source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        resolved.runtime().functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter(|inst| matches!(inst.instruction, nera::VirInstruction::Call { .. }))
            .count(),
        1
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(43)]
    );
}

#[test]
fn exhausted_guard_budget_cannot_invent_missing_refill() {
    let source = "struct Pair { left: Own<u64>, right: Own<u64>, }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 20; let b = alloc<u64>(1); *b = 22;
      let mut v = Pair { left: a, right: b };
      if choose() { let moved = v.left; v.right = moved; }
      let whole = v; return 0; } fn choose() -> bool { return true; }";
    let output = accepted(source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    for max_guarded_cases_per_block in [1, 16] {
        let config = CfgAnalysisConfig {
            max_guarded_cases_per_block,
            ..CfgAnalysisConfig::default()
        };
        assert!(
            !verify_program(&resolved, config)
                .unwrap()
                .is_memory_checked_core0()
        );
    }
    assert!(interpret(resolved.runtime()).is_err());
}

#[test]
fn indexed_and_tuple_resource_paths_refill_independently() {
    checked(
        "fn main() -> u64 { let a = alloc<u64>(1); *a = 20;
      let b = alloc<u64>(1); *b = 22; let mut v = [a, b]; let index = 0usize;
      let moved = v[index]; v[index] = moved; let whole = v;
      let left = whole[0]; let right = whole[1]; return *left + *right; }",
        42,
    );
    checked(
        "fn main() -> u64 { let a = alloc<u64>(1); *a = 20;
      let b = alloc<u64>(1); *b = 22; let mut v = (a, b);
      let moved = v.0; v.0 = moved; let whole = v;
      let left = whole.0; let right = whole.1; return *left + *right; }",
        42,
    );
}

#[test]
fn incomplete_whole_borrow_and_active_loan_replacement_are_rejected() {
    for source in [
        "struct Slot { owner: Own<u64>, word: u64, } fn main() -> u64 {
          let a = alloc<u64>(1); *a = 1; let mut v = Slot { owner: a, word: 42 };
          let moved = v.owner; let r = &v; return r.word; }",
        "struct Slot { owner: Own<u64>, word: u64, } fn main() -> u64 {
          let a = alloc<u64>(1); *a = 1; let mut v = Slot { owner: a, word: 42 };
          let r = &v; let b = alloc<u64>(1); *b = 2; v.owner = b; return r.word; }",
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
fn refill_mutations_cannot_skip_retirement_or_reuse_consumed_authority() {
    for source in [
        "struct Slot { owner: Own<u64>, } fn main() -> u64 {
      let a = alloc<u64>(1); *a = 1; let mut v = Slot { owner: a };
      let b = alloc<u64>(1); *b = 42; v.owner = b;
      let answer = v.owner; return *answer; }",
        "struct Slot { owner: &mut u64, } fn main() -> u64 {
      let mut a = 1; let mut b = 42; let mut v = Slot { owner: &mut a };
      v.owner = &mut b; let answer = v.owner; return *answer; }",
    ] {
        let original = accepted(source).vir().unwrap().as_unit().clone();
        for mutation in 0..3 {
            // Keep borrow-region instruction sites stable. False flag below is
            // the semantic no-cleanup mutation for the reference fixture.
            if mutation == 0 && source.contains("&mut") {
                continue;
            }
            let mut unit = original.clone();
            let block = &mut unit.runtime.functions[0].blocks[0];
            let refill = block
                .instructions
                .iter()
                .rposition(|inst| {
                    matches!(
                        inst.instruction,
                        nera::VirInstruction::ResourceInitialize { .. }
                    )
                })
                .unwrap();
            let cleanup = block.instructions[..refill]
                .iter()
                .rposition(|inst| {
                    matches!(inst.instruction, nera::VirInstruction::ObjectDrop { .. })
                })
                .unwrap();
            match mutation {
                0 => {
                    block.instructions.remove(cleanup);
                }
                1 => {
                    let nera::VirInstruction::ObjectDrop { condition, .. } =
                        block.instructions[cleanup].instruction
                    else {
                        unreachable!()
                    };
                    let definition = block
                        .instructions
                        .iter_mut()
                        .find(|inst| {
                            matches!(inst.instruction,
                    nera::VirInstruction::Constant { result, .. } if result.id == condition)
                        })
                        .unwrap();
                    let nera::VirInstruction::Constant { value, .. } = &mut definition.instruction
                    else {
                        unreachable!()
                    };
                    *value = nera::VirConstant::Bool(false);
                }
                _ => {
                    let first = block
                        .instructions
                        .iter()
                        .find_map(|inst| match inst.instruction {
                            nera::VirInstruction::ResourceInitialize {
                                value,
                                value_permission,
                                ..
                            } => Some((value, value_permission)),
                            _ => None,
                        })
                        .unwrap();
                    let nera::VirInstruction::ResourceInitialize {
                        value,
                        value_permission,
                        ..
                    } = &mut block.instructions[refill].instruction
                    else {
                        unreachable!()
                    };
                    *value = first.0;
                    *value_permission = first.1;
                }
            }
            if mutation == 0 {
                unit.rebuild_source_map_from_runtime("partial-refill.nera", source.len());
            }
            let unit = unit.into_validated().unwrap();
            let resolved = unit.resolve().unwrap();
            assert!(
                !verify_program(&resolved, CfgAnalysisConfig::default())
                    .unwrap()
                    .is_memory_checked_core0(),
                "mutation {mutation}"
            );
            assert!(
                interpret(resolved.runtime()).is_err(),
                "mutation {mutation}"
            );
        }
    }
}
