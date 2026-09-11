#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, VirInstruction, VirObjectDestinationMode, VirRuntimeValue, VirUnit,
    interpret, verify_program,
};

#[path = "support/enum_construction_program.rs"]
mod enum_construction_program;

fn accepted(source: &str) -> nera::FrontendOutput {
    frontend_checks::accepted("enum-construction.nera", source)
}

fn checked(source: &str, expected: u64) {
    frontend_checks::checked("enum-construction.nera", source, expected)
}

#[test]
fn aggregate_payload_move_allows_early_cleanup_and_reconstruction() {
    let source = include_str!("../spec/cases/verify/enum-partial-construction.nera");
    checked(source, 42);
    checked(&source.replace("packet = Packet::Empty;", ""), 42);
    checked(
        "struct Payload { owner: Own<u64>, word: u64, }
      enum Packet { Empty, Full(Payload, Own<u64>), }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 40; let b = alloc<u64>(1); *b = 1;
      let mut packet = Packet::Full(Payload { owner: a, word: 2 }, b);
      match packet { Packet::Empty => { return 0; }, Packet::Full(payload, other) => {
        packet = Packet::Full(payload, other);
        match packet { Packet::Empty => { return 0; }, Packet::Full(rebuilt, _) => {
          let owner = rebuilt.owner; return *owner + rebuilt.word;
        }, }
      }, } }",
        42,
    );
}

#[test]
fn resource_variant_replacement_and_refill_after_whole_move() {
    checked(
        "enum Item { Empty, Full(Own<u64>), }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 42;
      let mut value = Item::Empty; value = Item::Full(a);
      value = value;
      let moved = value; value = Item::Empty;
      match moved { Item::Empty => { return 0; }, Item::Full(owner) => { return *owner; }, } }",
        42,
    );
    checked(
        "enum Item { Empty, Full(Own<u64>), }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 1;
      let b = alloc<u64>(1); *b = 42;
      let mut value = Item::Full(a); let other = Item::Full(b); value = other;
      match value { Item::Empty => { return 0; }, Item::Full(owner) => { return *owner; }, } }",
        42,
    );
}

#[test]
fn shared_enum_self_assignment_preserves_payload_authority() {
    checked(
        "enum Ref { Empty, Full(&u64), }
      fn main() -> u64 { let word = 42; let mut value = Ref::Full(&word);
      value = value; match value { Ref::Empty => { return 0; },
      Ref::Full(reference) => { return *reference; }, } }",
        42,
    );
}

fn tag_only_unit() -> VirUnit {
    enum_construction_program::partial_unit(false)
}

#[test]
fn tag_only_construction_can_be_cleaned_but_not_observed() {
    let unit = tag_only_unit().into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        verification.is_memory_checked_core0(),
        "{:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
    let machine = nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .unwrap();
    let plan = machine
        .planning()
        .function(nera::VirFunctionId::new(0))
        .unwrap();
    assert!(plan.blocks()[0].instructions().iter().any(|inst| matches!(inst,
        nera::backend::X86_64InstructionPlan::EnumDiscriminant(tag) if tag.empty_resource_offsets() == [8])));

    let mut unit = tag_only_unit();
    let block = &mut unit.runtime.functions[0].blocks[0];
    let (destination, destination_permission) = block
        .instructions
        .iter()
        .find_map(|inst| {
            if let VirInstruction::LocalStorage {
                pointer_result,
                permission_result,
                access,
            } = inst.instruction
                && !unit
                    .memory
                    .object_shape(access)
                    .unwrap()
                    .variants()
                    .is_empty()
            {
                Some((pointer_result.id, permission_result.id))
            } else {
                None
            }
        })
        .unwrap();
    for inst in &mut block.instructions {
        if let VirInstruction::ObjectDrop {
            pointer,
            permission,
            access,
            ..
        } = inst.instruction
        {
            inst.instruction = VirInstruction::ObjectTransfer {
                destination,
                destination_permission,
                source: pointer,
                source_permission: permission,
                access,
                destination_mode: VirObjectDestinationMode::Initialize,
                source_mode: nera::VirObjectSourceMode::Move,
            };
        }
    }
    let failures = rejected_by_consumers(unit);
    assert!(failures.iter().any(|kind| matches!(
        kind,
        nera::ResourceObligationKind::ObjectValueBytesInitialized { .. }
    )));
}

fn rejected_by_consumers(mut unit: VirUnit) -> Vec<nera::ResourceObligationKind> {
    unit.rebuild_source_map_from_runtime("enum-mutation.vir", 1000);
    let unit = unit.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
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

#[test]
fn missing_old_cleanup_and_forged_tag_are_independently_rejected() {
    let source = "enum Item { Empty, Full(Own<u64>, u64), }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 1;
      let mut value = Item::Full(a, 9); value = Item::Empty; return 42; }";
    let original = accepted(source).vir().unwrap().as_unit().clone();
    let mut unit = original.clone();
    for block in &mut unit.runtime.functions[0].blocks {
        block
            .instructions
            .retain(|inst| !matches!(inst.instruction, VirInstruction::ObjectDrop { .. }));
    }
    rejected_by_consumers(unit);

    let mut unit = original;
    for block in &mut unit.runtime.functions[0].blocks {
        let tag = block
            .instructions
            .iter()
            .find_map(|inst| match inst.instruction {
                VirInstruction::EnumSetDiscriminant { variant, .. } => Some(variant),
                _ => None,
            })
            .unwrap();
        for inst in &mut block.instructions {
            if let VirInstruction::ObjectDrop {
                pointer,
                permission,
                access,
                ..
            } = inst.instruction
            {
                inst.instruction = VirInstruction::EnumSetDiscriminant {
                    pointer,
                    permission,
                    access,
                    variant: tag,
                    mode: VirObjectDestinationMode::Initialize,
                };
                break;
            }
        }
    }
    let failures = rejected_by_consumers(unit);
    assert!(failures.iter().any(|kind| matches!(
        kind,
        nera::ResourceObligationKind::ObjectResourcePayloadEmpty { .. }
    )));
}

#[test]
fn wrong_active_mask_cannot_initialize_an_inactive_payload() {
    let source = "enum Item { Empty, Full(Own<u64>, u64), }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 1;
      let value = Item::Full(a, 9); return 42; }";
    let mut unit = accepted(source).vir().unwrap().as_unit().clone();
    for block in &mut unit.runtime.functions[0].blocks {
        for inst in &mut block.instructions {
            if let VirInstruction::EnumSetDiscriminant {
                variant, access, ..
            } = &mut inst.instruction
            {
                *variant = unit
                    .memory
                    .variants
                    .iter()
                    .find(|case| case.owner == access.ty && case.fields.is_empty())
                    .unwrap()
                    .id;
            }
        }
    }
    rejected_by_consumers(unit);
}

#[test]
fn incomplete_enum_cannot_be_reused_as_a_whole_value() {
    let source = "struct Payload { owner: Own<u64>, word: u64, }
      enum Item { Empty, Full(Payload, Own<u64>), }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 1; let b = alloc<u64>(1); *b = 2;
      let mut value = Item::Full(Payload { owner: a, word: 9 }, b);
      match value { Item::Empty => { return 0; }, Item::Full(payload, _) => {
        value = value; return 42;
      }, } }";
    let unit = accepted(source).vir().unwrap().as_unit().clone();
    rejected_by_consumers(unit);
}

#[test]
fn nested_resource_tags_stay_outside_the_native_cleanup_profile() {
    let source = "enum Inner { Empty, Full(Own<u64>), }
      enum Outer { Empty, Full(Inner), }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 1;
      let value = Outer::Full(Inner::Full(a)); return 42; }";
    let output = accepted(source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    // No blanket claim that every nested representation has cleanup support.
    assert!(
        nera::backend::X86_64_UNKNOWN_LINUX_GNU
            .plan_program(resolved.runtime())
            .is_err()
    );
}

#[test]
fn live_borrow_of_enum_storage_blocks_variant_replacement() {
    let source = "enum Item { Empty, Full(&u64), }
      fn main() -> u64 { let word = 42; let mut value = Item::Full(&word);
      let view = &value; value = Item::Empty;
      let observed = *view;
      match observed { Item::Empty => { return 0; }, Item::Full(reference) => { return *reference; }, } }";
    let output = accepted(source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        !verification.is_memory_checked_core0(),
        "{:#?}",
        verification.diagnostics()
    );
    assert!(interpret(resolved.runtime()).is_err());
}
