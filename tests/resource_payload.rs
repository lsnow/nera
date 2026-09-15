#[path = "support/resource_payload_program.rs"]
mod resource_payload_program;

use nera::backend::{X86_64_UNKNOWN_LINUX_GNU, X86_64InstructionPlan};
use nera::{
    ObligationStatus, ResourceObligationKind, SpannedVirInstruction, VirExecutionErrorKind,
    VirInstruction, VirMemoryTypeKind, VirObjectSourceMode, VirPointerKind, VirRuntimeValue,
    VirType, VirValidationErrorKind, VirValue, VirValueId, analyze_function_cfg, interpret,
};

#[test]
fn canonical_shape_exposes_the_owning_move_path() {
    let schema = resource_payload_program::schema();
    let shape = schema
        .object_shape(resource_payload_program::OWNER_BOX_ACCESS)
        .expect("owner box has a canonical shape");
    let [leaf] = shape.resource_leaves() else {
        panic!("owner box must have exactly one resource leaf");
    };
    assert_eq!(leaf.access(), resource_payload_program::OWN_U64_ACCESS);
    assert_eq!(leaf.pointee_access(), resource_payload_program::U64_ACCESS);
    assert_eq!(leaf.kind(), VirPointerKind::Own);
    assert_eq!(
        (leaf.bytes().start_bytes(), leaf.bytes().end_bytes()),
        (0, 8)
    );
    assert_eq!(leaf.path().segments().len(), 1);
}

#[test]
fn own_payload_round_trip_moves_permission_exactly_once() {
    let validated = resource_payload_program::validated();
    assert!(validated.stable_dump().starts_with("vir-unit-v27\n"));
    assert!(validated.stable_dump().contains("resource.init"));
    assert!(validated.stable_dump().contains("resource.take"));
    let resolved = validated.resolve().expect("resource VIR resolves");
    let analysis = analyze_function_cfg(&resolved, nera::VirFunctionId::new(0))
        .expect("resource payload CFG converges");
    assert!(
        analysis.all_obligations_proven(),
        "{:#?}",
        analysis.obligations()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("typed shadow payload executes")
            .values(),
        &[VirRuntimeValue::U64(0)]
    );

    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("verified resource move has native lowering");
    let plan = machine
        .planning()
        .function(nera::VirFunctionId::new(0))
        .expect("resource function plan");
    assert!(plan.blocks()[0].instructions().iter().any(|instruction| {
        matches!(instruction, X86_64InstructionPlan::ObjectTransfer(transfer) if transfer.size_bytes() == 8)
    }));
    let assembly = X86_64_UNKNOWN_LINUX_GNU
        .emit_assembly(&machine)
        .expect("resource assembly emits");
    assert!(assembly.contains("mov QWORD PTR [r11], r10"));
    assert!(assembly.contains("mov r10, QWORD PTR [r11]"));
}

#[test]
fn own_object_copy_is_rejected_by_capability() {
    let mut unit = resource_payload_program::unit();
    let VirInstruction::ObjectTransfer { source_mode, .. } =
        &mut unit.runtime.functions[0].blocks[0].instructions[6].instruction
    else {
        panic!("fixture object transfer");
    };
    *source_mode = VirObjectSourceMode::Copy;
    unit.rebuild_source_map_from_runtime("copy-owner.vir", 1);
    let validated = unit
        .into_validated()
        .expect("copy/move is a verifier condition");
    let resolved = validated.resolve().expect("copy-owner VIR resolves");
    let analysis = analyze_function_cfg(&resolved, nera::VirFunctionId::new(0))
        .expect("copy-owner CFG produces obligations");
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::ObjectTriviallyCopyable { .. }
        ) && record.obligation().status() == ObligationStatus::Refuted
    }));
}

#[test]
fn second_take_is_rejected_without_reconstructing_owner_from_bits() {
    let mut unit = resource_payload_program::unit();
    let instructions = &mut unit.runtime.functions[0].blocks[0].instructions;
    let span = instructions[0].source_span;
    instructions.insert(
        9,
        SpannedVirInstruction {
            instruction: VirInstruction::ResourceTake {
                pointer_result: VirValue {
                    id: VirValueId::new(12),
                    ty: VirType::Pointer {
                        access: resource_payload_program::U64_ACCESS,
                    },
                },
                permission_result: VirValue {
                    id: VirValueId::new(13),
                    ty: VirType::Permission,
                },
                source: VirValueId::new(8),
                source_permission: VirValueId::new(3),
                access: resource_payload_program::OWN_U64_ACCESS,
            },
            source_span: span,
        },
    );
    unit.rebuild_source_map_from_runtime("double-take.vir", 1);
    let validated = unit
        .into_validated()
        .expect("double take is structurally valid");
    let resolved = validated.resolve().expect("double-take VIR resolves");
    let analysis = analyze_function_cfg(&resolved, nera::VirFunctionId::new(0))
        .expect("double take produces obligations");
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::ResourcePayloadAvailable { .. }
                | ResourceObligationKind::MemoryInitialized { .. }
        ) && record.obligation().status() == ObligationStatus::Refuted
    }));
    assert!(matches!(
        interpret(resolved.runtime())
            .expect_err("runtime shadow rejects a second take")
            .kind(),
        VirExecutionErrorKind::UninitializedRead { .. }
            | VirExecutionErrorKind::MissingResourcePayload { .. }
    ));
}

#[test]
fn raw_pointer_cannot_impersonate_an_own_resource_effect() {
    let mut unit = resource_payload_program::unit();
    let raw_type = &mut unit.memory.types[1];
    let VirMemoryTypeKind::Pointer { kind, .. } = &mut raw_type.kind else {
        panic!("fixture resource pointer type");
    };
    *kind = VirPointerKind::Raw;
    unit.memory
        .assign_canonical_type_capabilities()
        .expect("mutated raw capabilities");
    assert!(unit.validate().is_err());
}

#[test]
fn resource_effect_schema_rejects_permission_alias_and_wrong_result_type() {
    let mut aliased = resource_payload_program::unit();
    let VirInstruction::ResourceInitialize {
        destination_permission,
        value_permission,
        ..
    } = &mut aliased.runtime.functions[0].blocks[0].instructions[5].instruction
    else {
        panic!("fixture resource init");
    };
    *value_permission = *destination_permission;
    assert_eq!(
        aliased
            .validate()
            .expect_err("permission roles must differ")
            .kind(),
        &VirValidationErrorKind::ResourcePermissionAliases
    );

    let mut wrong_result = resource_payload_program::unit();
    let VirInstruction::ResourceTake { pointer_result, .. } =
        &mut wrong_result.runtime.functions[0].blocks[0].instructions[8].instruction
    else {
        panic!("fixture resource take");
    };
    pointer_result.ty = VirType::Pointer {
        access: resource_payload_program::OWN_U64_ACCESS,
    };
    assert!(matches!(
        wrong_result
            .validate()
            .expect_err("take result must name the canonical pointee")
            .kind(),
        VirValidationErrorKind::TypeMismatch { .. }
    ));
}

#[test]
fn partial_move_preserves_sibling_but_invalidates_whole_object_move() {
    let sibling = resource_payload_program::partial_pair_unit(true)
        .into_validated()
        .expect("sibling fixture validates");
    let sibling_resolved = sibling.resolve().expect("sibling fixture resolves");
    let sibling_analysis = analyze_function_cfg(&sibling_resolved, nera::VirFunctionId::new(0))
        .expect("sibling CFG converges");
    assert!(sibling_analysis.all_obligations_proven());
    assert_eq!(
        interpret(sibling_resolved.runtime())
            .expect("unmoved sibling remains available")
            .values(),
        &[VirRuntimeValue::U64(0)]
    );

    let whole = resource_payload_program::partial_pair_unit(false)
        .into_validated()
        .expect("partial whole-move fixture validates");
    let whole_resolved = whole
        .resolve()
        .expect("partial whole-move fixture resolves");
    let whole_analysis = analyze_function_cfg(&whole_resolved, nera::VirFunctionId::new(0))
        .expect("partial whole-move CFG converges");
    assert!(whole_analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::ObjectValueBytesInitialized { .. }
                | ResourceObligationKind::ResourcePayloadAvailable { .. }
        ) && record.obligation().status() != ObligationStatus::Proven
    }));
    assert!(matches!(
        interpret(whole_resolved.runtime())
            .expect_err("whole move after partial move must fail")
            .kind(),
        VirExecutionErrorKind::UninitializedObjectLeaf { .. }
            | VirExecutionErrorKind::MissingResourcePayload { .. }
    ));
}
