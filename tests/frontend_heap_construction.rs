#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, VirInstruction, VirUnit, analyze, interpret,
    verify_program,
};

fn accepted(source: &str) -> nera::FrontendOutput {
    frontend_checks::accepted("heap-construction.nera", source)
}

fn rejected(unit: VirUnit) -> Vec<nera::ResourceObligationKind> {
    let validated = unit.into_validated().unwrap();
    let resolved = validated.resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!verification.is_memory_checked_core0());
    assert!(interpret(resolved.runtime()).is_err());
    verification
        .functions()
        .values()
        .flat_map(|function| function.cfg().obligations())
        .filter(|record| !record.obligation().is_proven())
        .map(|record| record.obligation().kind())
        .collect()
}

fn checked(source: &str, expected: u64) {
    frontend_checks::checked("heap-construction.nera", source, expected)
}

#[test]
fn heap_tuple_struct_and_array_construction() {
    checked("struct Pair { left: u64, right: u64, } fn main() -> u64 {
      let p = alloc<Pair>(1); let q = p; q.left = 42; let r = &q.left; let answer = *r; free(q); return answer; }", 42);
    checked(
        "fn main() -> u64 { let p = alloc<(u64, u64)>(1); p.0 = 20; p.1 = 22; let r = &*p; return r.0 + r.1; }",
        42,
    );
    checked(
        "struct Pair { left: u64, right: u64, } fn main() -> u64 { let p = alloc<Pair>(1); p.left = 20; p.right = 22; let value = *p; free(p); return value.left + value.right; }",
        42,
    );
    checked(
        "fn main() -> u64 { let p = alloc<[u64; 2]>(1); p[0] = 20; p[1] = 22; let value = *p; return value[0] + value[1]; }",
        42,
    );
}

#[test]
fn heap_partial_owners_and_empty_storage_cleanup() {
    for exit in ["free(p);", ""] {
        checked(
            &format!(
                "struct Pair {{ left: Own<u64>, right: Own<u64>, }} fn main() -> u64 {{ let p = alloc<Pair>(1); {exit} return 42; }}"
            ),
            42,
        );
        checked(
            &format!(
                "struct Pair {{ left: Own<u64>, right: Own<u64>, }} fn main() -> u64 {{ let p = alloc<Pair>(1); let a = alloc<u64>(1); *a = 42; p.left = a; {exit} return 42; }}"
            ),
            42,
        );
    }
}

#[test]
fn heap_enum_empty_constructed_and_moved_cleanup() {
    for body in [
        "",
        "*p = Item::Empty;",
        "let a = alloc<u64>(1); *a = 42; *p = Item::Full(a);",
        "let a = alloc<u64>(1); *a = 42; *p = Item::Full(a); let moved = *p;",
    ] {
        checked(
            &format!(
                "enum Item {{ Empty, Full(Own<u64>), }} fn main() -> u64 {{ let p = alloc<Item>(1); {body} free(p); return 42; }}"
            ),
            42,
        );
    }
}

#[test]
fn heap_resource_move_refill_and_partial_reference_cleanup() {
    checked(
        "fn main() -> u64 { let p = alloc<[Own<u64>; 2]>(1); let a = alloc<u64>(1); *a = 42; p[1] = a; return 42; }",
        42,
    );
    checked("struct Inner { owner: Own<u64>, } struct Outer { inner: Inner, word: u64, }
      fn main() -> u64 { let p = alloc<Outer>(1); let a = alloc<u64>(1); *a = 42; p.inner.owner = a; return 42; }", 42);
    checked("struct Pair { left: u64, right: u64, } fn main() -> u64 { let value = make(); return value.left + value.right; }
      fn make() -> Pair { let p = alloc<Pair>(1); p.left = 20; p.right = 22; return *p; }", 42);
    checked(
        "struct Slot { owner: Own<u64>, word: u64, } fn main() -> u64 {
      let p = alloc<Slot>(1); let a = alloc<u64>(1); *a = 40; p.owner = a;
      p.word = 21; let r = &p.word; let answer = *r; let value = *p;
      let b = alloc<u64>(1); *b = 1; p.owner = b; free(p); return answer + value.word; }",
        42,
    );
    checked(
        "struct Pair { left: &mut u64, right: &mut u64, } fn main() -> u64 {
      let mut word = 40; { let p = alloc<Pair>(1); p.left = &mut word;
      let r = p.left; *r = 42; p.left = r; free(p); } return word; }",
        42,
    );
    checked(
        "enum Item { Empty, Full(Own<u64>), } fn main() -> u64 {
      let p = alloc<Item>(1); let a = alloc<u64>(1); *a = 1; *p = Item::Full(a);
      let b = alloc<u64>(1); *b = 42; *p = Item::Full(b); let whole = *p; free(p);
      match whole { Item::Empty => { return 0; }, Item::Full(owner) => { return *owner; }, } }",
        42,
    );
}

#[test]
fn heap_branch_and_loop_partial_exit_cleanup() {
    for condition in ["true", "false"] {
        checked(
            &format!(
                "struct Pair {{ left: Own<u64>, right: Own<u64>, }}
          fn main() -> u64 {{ let p = alloc<Pair>(1);
          if choose() {{ let a = alloc<u64>(1); *a = 1; p.left = a; return 42; }}
          free(p); return 42; }} fn choose() -> bool {{ return {condition}; }}"
            ),
            42,
        );
    }
    checked(
        "struct Slot { owner: Own<u64>, } fn main() -> u64 {
      let mut i = 0; while i < 3 { let p = alloc<Slot>(1); let a = alloc<u64>(1); *a = i;
      p.owner = a; i = i + 1; if i == 1 { continue; } if i == 2 { break; } } return i + 40; }",
        42,
    );
}

#[test]
fn storage_ownership_does_not_prove_pointee_completeness() {
    for tail in [
        "let r = &*p; return 0;",
        "let value = *p; return value.right;",
        "return p.right;",
        "return take(*p);",
    ] {
        let source = format!("struct Pair {{ left: u64, right: u64, }}
          fn main() -> u64 {{ let p = alloc<Pair>(1); p.left = 42; {tail} }} fn take(value: Pair) -> u64 {{ return value.right; }}");
        rejected(accepted(&source).vir().unwrap().as_unit().clone());
    }
    let source = "struct Pair { left: u64, right: u64, } fn main() -> u64 { let value = make(); return value.right; } fn make() -> Pair { let p = alloc<Pair>(1); p.left = 1; return *p; }";
    rejected(accepted(source).vir().unwrap().as_unit().clone());
    let source = "enum Item { Empty, Full(Own<u64>), } fn main() -> u64 { let p = alloc<Item>(1); let r = &*p; return 0; }";
    rejected(accepted(source).vir().unwrap().as_unit().clone());
    let source = source.replace("let r = &*p;", "let value = *p;");
    let output = analyze(&SourceFile::from_text("unformed-tag.nera", &source));
    assert_eq!(output.status(), FrontendStatus::Unsupported);
    assert!(output.issues().iter().any(|issue| {
        issue
            .diagnostic()
            .message()
            .contains("initialization planning")
    }));
}

#[test]
fn free_requires_ended_loans_and_exactly_once_outer_and_inner_cleanup() {
    for source in [
        "struct Slot { word: u64, } fn main() -> u64 { let p = alloc<Slot>(1); p.word = 42; let r = &*p; free(p); return r.word; }",
        "struct Slot { word: u64, } fn main() -> u64 { let p = alloc<Slot>(1); free(p); free(p); return 42; }",
        "struct Slot { owner: Own<u64>, word: u64, } fn main() -> u64 { let p = alloc<Slot>(1); let a = alloc<u64>(1); *a = 42; p.owner = a; p.word = 42; let r = &p.word; free(p); return *r; }",
    ] {
        rejected(accepted(source).vir().unwrap().as_unit().clone());
    }

    let source = "struct Slot { owner: Own<u64>, } fn main() -> u64 { let p = alloc<Slot>(1); let a = alloc<u64>(1); *a = 42; p.owner = a; free(p); return 42; }";
    let mut unit = accepted(source).vir().unwrap().as_unit().clone();
    let block = &mut unit.runtime.functions[0].blocks[0];
    let cleanup = block
        .instructions
        .iter()
        .rposition(|item| matches!(item.instruction, VirInstruction::ObjectDrop { .. }))
        .unwrap();
    block.instructions.remove(cleanup);
    unit.rebuild_source_map_from_runtime("heap-mutation.vir", 10_000);
    assert!(rejected(unit).iter().any(|kind| matches!(
        kind,
        nera::ResourceObligationKind::AllocationResourcePayloadEmpty { .. }
    )));
}

#[test]
fn aggregate_heap_profile_is_explicitly_bounded() {
    for source in [
        "struct Pair { word: u64, } fn main() -> u64 { let p = alloc<Pair>(2); return 42; }",
        "fn main() -> u64 { let p = alloc<[u64; 513]>(1); return 42; }",
        "fn main() -> u64 { let p = alloc<()>(1); return 42; }",
        "fn main() -> u64 { let p = alloc<Own<u64> >(1); return 42; }",
        "enum Item { Empty, Full(Own<u64>), } struct Box { item: Item, } fn main() -> u64 { let p = alloc<Box>(1); return 42; }",
        "struct Box { word: u64, } fn make() -> Own<Box> { let p = alloc<Box>(1); return p; } fn main() -> u64 { return 42; }",
    ] {
        let output = analyze(&SourceFile::from_text("heap-gated.nera", source));
        assert_eq!(
            output.status(),
            FrontendStatus::Unsupported,
            "{source}\n{:?}",
            output.issues()
        );
        assert!(output.vir().is_none());
    }
}

#[test]
fn empty_heap_tag_retirement_does_not_admit_unconstructed_local_enum() {
    let output = accepted(
        "enum Item { Empty, Full(Own<u64>), } fn main() -> u64 { let p = alloc<Item>(1); free(p); return 42; }",
    );
    let mut unit = output.vir().unwrap().as_unit().clone();
    let mut changed = false;
    for item in &mut unit.runtime.functions[0].blocks[0].instructions {
        if let VirInstruction::Allocate {
            pointer_result,
            permission_result,
            element,
            ..
        } = item.instruction
        {
            item.instruction = VirInstruction::LocalStorage {
                pointer_result,
                permission_result,
                access: element,
            };
            changed = true;
        }
    }
    assert!(changed);
    let block = &mut unit.runtime.functions[0].blocks[0];
    let local = block
        .instructions
        .iter()
        .position(|item| matches!(item.instruction, VirInstruction::LocalStorage { .. }))
        .unwrap();
    let local = block.instructions.remove(local);
    block.instructions.insert(0, local);
    unit.rebuild_source_map_from_runtime("local-tag-mutation.vir", 10_000);
    assert!(rejected(unit).iter().any(|kind| matches!(
        kind,
        nera::ResourceObligationKind::ObjectActiveVariantKnown { .. }
    )));
}
