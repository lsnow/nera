use nera::{
    SourceFile, VirConstant, VirInstruction, VirTerminator, VirType, VirUnit, VirValue, VirValueId,
    analyze,
};

/// Construct a valid low-level program whose enum representation has a tag but
/// either no payload or only an owner (the ordinary field is absent). No
/// frontend completeness assumption participates in this test.
pub fn partial_unit(present: bool) -> VirUnit {
    let source = "enum Item { Empty, Full(Own<u64>, u64), }
      fn main() -> u64 { let a = alloc<u64>(1); *a = 1;
      let value = Item::Full(a, 9); return 42; }";
    let mut unit = analyze(&SourceFile::from_text("partial-enum.nera", source))
        .vir()
        .unwrap()
        .as_unit()
        .clone();
    let block = &mut unit.runtime.functions[0].blocks[0];
    let tag = block
        .instructions
        .iter()
        .find(|inst| matches!(inst.instruction, VirInstruction::EnumSetDiscriminant { .. }))
        .unwrap()
        .clone();
    let VirInstruction::EnumSetDiscriminant {
        pointer,
        permission,
        access,
        ..
    } = tag.instruction
    else {
        unreachable!()
    };
    if present {
        let last = block
            .instructions
            .iter()
            .position(|inst| matches!(inst.instruction, VirInstruction::ResourceInitialize { .. }))
            .unwrap();
        block.instructions.truncate(last + 1);
    } else {
        block
            .instructions
            .retain(|inst| matches!(inst.instruction, VirInstruction::LocalStorage { .. }));
        block.instructions.push(tag.clone());
    }
    let condition = VirValueId::new(50000);
    let answer = VirValueId::new(50001);
    for instruction in [
        VirInstruction::Constant {
            result: VirValue {
                id: condition,
                ty: VirType::Bool,
            },
            value: VirConstant::Bool(true),
        },
        VirInstruction::ObjectDrop {
            pointer,
            permission,
            access,
            condition,
        },
        VirInstruction::Constant {
            result: VirValue {
                id: answer,
                ty: VirType::U64,
            },
            value: VirConstant::U64(42),
        },
    ] {
        block.instructions.push(nera::SpannedVirInstruction {
            instruction,
            source_span: tag.source_span,
        });
    }
    block.terminator.terminator = VirTerminator::Return {
        values: vec![answer],
    };
    unit.rebuild_source_map_from_runtime("tag-only.vir", source.len());
    unit
}
