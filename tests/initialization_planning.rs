#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, ObligationStatus, ResourceObligationKind, VirInstruction, VirRuntimeValue,
    VirUnit, interpret, verify_program,
};

fn unit(source: &str) -> VirUnit {
    frontend_checks::accepted("initialization-planning.nera", source)
        .vir()
        .unwrap()
        .as_unit()
        .clone()
}

fn checked(source: &str, expected: u64) {
    frontend_checks::checked("initialization-planning.nera", source, expected)
}

#[test]
fn complete_borrows_do_not_require_padding_or_inactive_payloads() {
    checked(
        "struct Padded { small: bool, word: u64, }
        fn main() -> u64 { let value = Padded { small: true, word: 42 };
        let reference = &value; return reference.word; }",
        42,
    );
    checked(
        "enum Item { None, Some(u64), }
        fn main() -> u64 { let value = Item::None; let reference = &value; return 42; }",
        42,
    );
    checked(
        "struct Pair { owner: Own<u64>, word: u64, }
        fn main() -> u64 { let owner = alloc<u64>(1); *owner = 1;
        let pair = Pair { owner: owner, word: 42 }; let moved = pair.owner;
        let sibling = &pair.word; return *sibling; }",
        42,
    );
}

#[test]
fn slice_envelopes_and_reborrows_preserve_initialized_values() {
    checked(
        "fn main() -> u64 { let mut values = [40, 42];
        let parent = &mut values[..]; let child = &parent[1..]; return child[0]; }",
        42,
    );
    checked(
        "fn main() -> u64 { let values = [1, 2]; let empty = &values[2..2]; return 42; }",
        42,
    );
    checked(
        "fn main() -> u64 { let values = [40, 42]; let index = 1usize;
        let value = &values[index]; return *value; }",
        42,
    );
}

#[test]
fn replacement_planning_keeps_place_then_rhs_single_evaluation() {
    // This checks lowering/evaluation order, not safety proof of the opaque
    // returned index. The existing function skeleton does not expose its value.
    let source = "fn main() -> u64 { let mut count = 0; let mut values = [1, 2];
        values[next(&mut count)] = rhs(&mut count); return count + values[0]; }
        fn next(count: &mut u64) -> usize { *count = *count + 1; return 0usize; }
        fn rhs(count: &mut u64) -> u64 { *count = *count + 1; return *count + 40; }";
    let unit = unit(source).into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    assert_eq!(
        unit.runtime().functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter(|instruction| matches!(instruction.instruction, VirInstruction::Call { .. }))
            .count(),
        2
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(44)]
    );
    checked(
        "fn main() -> u64 { let mut value = [1, 2]; value = value; return value[1]; }",
        2,
    );
    checked(
        "struct Box { value: Own<u64>, }
        fn main() -> u64 { let first = alloc<u64>(1); *first = 1;
        let mut value = Box { value: first }; let second = alloc<u64>(1); *second = 42;
        if choose() { value = Box { value: second }; } else { value = Box { value: second }; }
        let final_owner = value.value; return *final_owner; } fn choose() -> bool { return true; }",
        42,
    );
}

#[test]
fn deinitialized_referent_is_rejected_at_borrow_not_a_later_read() {
    for source in [
        "fn main() -> u64 { let value = 42; let reference = &value; return 0; }",
        "struct Padded { small: bool, word: u64, }
         fn main() -> u64 { let value = Padded { small: true, word: 42 }; let reference = &value; return 0; }",
        "enum Item { None, Some(u64), }
         fn main() -> u64 { let value = Item::Some(42); let reference = &value; return 0; }",
    ] {
        let mut unit = unit(source);
        let block = &mut unit.runtime.functions[0].blocks[0];
        let index = block.instructions.iter().position(|instruction| matches!(instruction.instruction, VirInstruction::LoanBegin { .. })).unwrap();
        let borrow = block.instructions[index].clone();
        let VirInstruction::LoanBegin { effect, reference_result, .. } = borrow.instruction else { unreachable!() };
        let nera::VirType::Pointer { access } = reference_result.ty else { unreachable!() };
        block.instructions.insert(index, nera::SpannedVirInstruction {
            instruction: VirInstruction::ObjectDeinitialize { pointer: effect.source_pointer, permission: effect.source_permission, access },
            source_span: borrow.source_span,
        });
        unit.rebuild_source_map_from_runtime("initialization-planning.nera", source.len());
        let unit = unit.into_validated().unwrap();
        let resolved = unit.resolve().unwrap();
        let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(!result.is_memory_checked_core0());
        assert!(result.functions().values().any(|function| function.cfg().obligations().iter().any(|record| {
            matches!(record.obligation().kind(), ResourceObligationKind::ObjectValueBytesInitialized { .. })
                && record.obligation().status() != ObligationStatus::Proven
                && record.obligation().source_span() == borrow.source_span
        })), "{:#?}", result.diagnostics());
        assert!(interpret(resolved.runtime()).is_err());
    }
}
