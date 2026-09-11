#[path = "support/object_effect_program.rs"]
mod object_effect_program;

use nera::backend::{
    X86_64_UNKNOWN_LINUX_GNU, X86_64InstructionPlan, X86_64MachineByteRead, X86_64MachineByteWrite,
    X86_64MachineInstruction,
};
use nera::{
    ObligationStatus, ResourceObligationKind, SpannedVirInstruction, VirExecutionErrorKind,
    VirFieldId, VirFunctionId, VirInstruction, VirObjectDestinationMode, VirObjectSourceMode,
    VirRuntimeValue, VirType, VirValue, VirValueId, analyze_function_cfg, interpret,
};

#[test]
fn complete_record_copy_and_move_close_the_cfg_runtime_slice() {
    for (destination_mode, source_mode) in [
        (
            VirObjectDestinationMode::Initialize,
            VirObjectSourceMode::Copy,
        ),
        (
            VirObjectDestinationMode::Initialize,
            VirObjectSourceMode::Move,
        ),
        (VirObjectDestinationMode::Replace, VirObjectSourceMode::Copy),
        (VirObjectDestinationMode::Replace, VirObjectSourceMode::Move),
    ] {
        let validated =
            object_effect_program::validated_record_modes(destination_mode, source_mode);
        let resolved = validated.resolve().expect("record fixture resolves");
        let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
            .expect("record object-effect CFG converges");
        assert!(analysis.all_obligations_proven());

        let execution = interpret(resolved.runtime()).expect("record object effect executes");
        assert_eq!(execution.values(), &[VirRuntimeValue::U64(42)]);
        assert!(execution.trace().len() >= 13);

        let machine = X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(resolved.runtime())
            .expect("record object effect lowers natively");
        let plan = machine
            .planning()
            .function(VirFunctionId::new(0))
            .expect("record entry plan");
        assert!(plan.blocks()[0].instructions().iter().any(|instruction| {
            matches!(instruction, X86_64InstructionPlan::ObjectTransfer(transfer) if transfer.size_bytes() == 16)
        }));
        let assembly = X86_64_UNKNOWN_LINUX_GNU
            .emit_assembly(&machine)
            .expect("record object assembly emits");
        assert!(assembly.contains("mov r10, QWORD PTR [r11]"));
        assert!(assembly.contains("mov QWORD PTR [rax + 8], r10"));
    }
}

#[test]
fn partial_source_is_rejected_by_both_verifier_and_interpreter() {
    let validated = object_effect_program::record_unit(VirObjectSourceMode::Move, false)
        .into_validated()
        .expect("partial source is structurally valid VIR");
    let resolved = validated.resolve().expect("partial fixture resolves");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("partial object CFG still produces obligations");
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::ObjectValueBytesInitialized { .. }
        ) && record.obligation().status() != ObligationStatus::Proven
    }));
    assert!(matches!(
        interpret(resolved.runtime())
            .expect_err("partial source cannot execute a whole-object move")
            .kind(),
        VirExecutionErrorKind::UninitializedObjectLeaf {
            offset_bytes: 8,
            ..
        }
    ));
}

#[test]
fn reading_the_source_after_an_object_move_fails_closed() {
    let mut unit = object_effect_program::record_unit(VirObjectSourceMode::Move, true);
    let entry = &mut unit.runtime.functions[0].blocks[0].instructions;
    let before_condition = entry.len() - 1;
    let source_span = entry[0].source_span;
    entry.splice(
        before_condition..before_condition,
        [
            SpannedVirInstruction {
                instruction: VirInstruction::FieldAddress {
                    result: VirValue {
                        id: VirValueId::new(16),
                        ty: VirType::Pointer {
                            access: object_effect_program::U64_ACCESS,
                        },
                    },
                    base: VirValueId::new(0),
                    field: VirFieldId::new(1),
                    owner: object_effect_program::RECORD_ACCESS,
                    field_access: object_effect_program::U64_ACCESS,
                    offset_bytes: 8,
                },
                source_span,
            },
            SpannedVirInstruction {
                instruction: VirInstruction::Load {
                    result: VirValue {
                        id: VirValueId::new(17),
                        ty: VirType::U64,
                    },
                    pointer: VirValueId::new(16),
                    permission: VirValueId::new(1),
                    access: object_effect_program::U64_ACCESS,
                },
                source_span,
            },
        ],
    );
    unit.rebuild_source_map_from_runtime("move-after-read.vir", 1);
    let validated = unit
        .into_validated()
        .expect("post-move source read is structurally valid VIR");
    let resolved = validated.resolve().expect("post-move fixture resolves");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("post-move read produces obligations");
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::MemoryInitialized { .. }
        ) && record.obligation().status() == ObligationStatus::Refuted
    }));
    assert!(matches!(
        interpret(resolved.runtime())
            .expect_err("moved source cannot be read")
            .kind(),
        VirExecutionErrorKind::UninitializedRead { .. }
    ));
}

#[test]
fn overlapping_runtime_ranges_have_a_distinct_fault() {
    let validated = object_effect_program::overlapping_record_unit()
        .into_validated()
        .expect("overlap is a verifier/runtime condition, not malformed VIR");
    let resolved = validated.resolve().expect("overlap fixture resolves");
    let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
        .expect("overlap CFG produces an explicit obligation");
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::ObjectNonOverlapping { .. }
        ) && record.obligation().status() == ObligationStatus::Refuted
    }));
    assert_eq!(
        interpret(resolved.runtime())
            .expect_err("overlapping object copy cannot execute")
            .kind(),
        &VirExecutionErrorKind::OverlappingObjectTransfer {
            allocation: 0,
            destination_offset_bytes: 8,
            source_offset_bytes: 0,
            size_bytes: 16,
        }
    );
}

#[test]
fn one_byte_enum_tag_and_object_copy_have_explicit_native_lowering() {
    for source_mode in [VirObjectSourceMode::Copy, VirObjectSourceMode::Move] {
        let validated = object_effect_program::validated_enum(source_mode);
        let resolved = validated.resolve().expect("enum fixture resolves");
        let analysis = analyze_function_cfg(&resolved, VirFunctionId::new(0))
            .expect("enum object-effect CFG converges");
        assert!(analysis.all_obligations_proven());
        assert_eq!(
            interpret(resolved.runtime())
                .expect("enum object effect executes")
                .values(),
            &[VirRuntimeValue::U64(1)]
        );

        let machine = X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(resolved.runtime())
            .expect("one-byte enum lowers natively");
        let function = machine
            .function(VirFunctionId::new(0))
            .expect("enum entry machine function");
        assert!(
            function
                .blocks()
                .iter()
                .flat_map(|block| block.instructions())
                .any(|instruction| matches!(
                    instruction,
                    X86_64MachineInstruction::Move8 {
                        destination: X86_64MachineByteWrite::Memory(_),
                        source: X86_64MachineByteRead::Immediate(1),
                    }
                ))
        );
        assert!(
            function
                .blocks()
                .iter()
                .flat_map(|block| block.instructions())
                .any(|instruction| matches!(
                    instruction,
                    X86_64MachineInstruction::Move8 {
                        destination: X86_64MachineByteWrite::Register(_),
                        source: X86_64MachineByteRead::Memory(_),
                    }
                ))
        );
        let assembly = X86_64_UNKNOWN_LINUX_GNU
            .emit_assembly(&machine)
            .expect("byte object assembly emits");
        assert!(assembly.contains("mov BYTE PTR [r11], 0x01"));
        assert!(assembly.contains("mov r10b, BYTE PTR [r11]"));
        assert!(assembly.contains("mov BYTE PTR [rax], r10b"));
    }
}
