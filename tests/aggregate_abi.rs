use nera::{
    FrontendStatus, SourceFile, VirAbiSignature, VirAbiValue, VirInstruction, VirInterfaceStorage,
    VirInterfaceTransfer, VirResolutionErrorKind, VirType, analyze,
};

#[path = "support/slice_program.rs"]
mod slice_program;

fn accepted(name: &str, source: &str) -> nera::FrontendOutput {
    let output = analyze(&SourceFile::from_text(name, source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{name}: {:?}",
        output.issues()
    );
    output
}

#[test]
fn classifier_selects_direct_and_indirect_aggregate_boundaries() {
    let direct = accepted(
        "abi-direct.nera",
        include_str!("../spec/cases/aggregate/abi-direct.nera"),
    );
    let direct = direct.vir().expect("direct ABI VIR");
    let make_pair = direct
        .runtime()
        .functions
        .iter()
        .find(|function| function.name == "make_pair")
        .expect("make_pair function");
    let make_pair_abi = direct
        .runtime()
        .abis
        .function(make_pair.id)
        .expect("make_pair ABI");
    assert!(matches!(
        make_pair_abi.signature.results()[0].value(),
        VirAbiValue::DirectAggregate { leaves, .. } if leaves.len() == 2
    ));
    assert_eq!(
        make_pair_abi.signature.results()[0].interface().transfer,
        VirInterfaceTransfer::Copy
    );
    assert_eq!(
        make_pair_abi.signature.results()[0].interface().storage,
        VirInterfaceStorage::Direct
    );
    assert_eq!(make_pair.signature.results, [VirType::U64, VirType::U64]);

    let indirect = accepted(
        "abi-indirect.nera",
        include_str!("../spec/cases/aggregate/abi-indirect.nera"),
    );
    let indirect = indirect.vir().expect("indirect ABI VIR");
    let make_values = indirect
        .runtime()
        .functions
        .iter()
        .find(|function| function.name == "make_values")
        .expect("make_values function");
    let make_values_abi = indirect
        .runtime()
        .abis
        .function(make_values.id)
        .expect("make_values ABI");
    let result = &make_values_abi.signature.results()[0];
    assert!(matches!(
        result.value(),
        VirAbiValue::IndirectAggregate { .. }
    ));
    assert_eq!(result.interface().transfer, VirInterfaceTransfer::Copy);
    assert_eq!(result.interface().storage, VirInterfaceStorage::Indirect);
    assert_eq!(result.parameter_slots(), [1, 2]);
    assert_eq!(result.result_slots(), [0]);
    assert_eq!(
        make_values.signature.parameters,
        [
            VirType::U64,
            VirType::Pointer {
                access: result.value().access().expect("aggregate access")
            },
            VirType::Permission,
        ]
    );
    assert_eq!(make_values.signature.results, [VirType::Permission]);
}

#[test]
fn slice_abi_preserves_length_and_restores_parameter_permission() {
    let schema = slice_program::schema();
    let abi = VirAbiSignature::classify(
        &schema,
        &[slice_program::SLICE_ACCESS],
        &[slice_program::SLICE_ACCESS],
    )
    .expect("slice ABI classifies");
    assert!(matches!(
        abi.parameters()[0].value(),
        VirAbiValue::Slice { .. }
    ));
    assert_eq!(
        abi.parameters()[0].interface().transfer,
        VirInterfaceTransfer::BorrowShared
    );
    assert_eq!(
        abi.parameters()[0].interface().storage,
        VirInterfaceStorage::Direct
    );
    assert_eq!(abi.parameters()[0].parameter_slots(), [0, 1, 2]);
    assert_eq!(abi.parameters()[0].result_slots(), [3]);
    assert_eq!(abi.results()[0].result_slots(), [0, 1, 2]);
    assert_eq!(
        abi.physical().parameters,
        [
            VirType::Pointer {
                access: slice_program::U64_ACCESS
            },
            VirType::U64,
            VirType::Permission,
        ]
    );
    assert_eq!(
        abi.physical().results,
        [
            VirType::Pointer {
                access: slice_program::U64_ACCESS
            },
            VirType::U64,
            VirType::Permission,
            VirType::Permission,
        ]
    );
}

#[test]
fn owned_parameter_and_result_require_move_effects() {
    let output = accepted(
        "owned-interface.nera",
        include_str!("../spec/cases/control-flow/owned-call.nera"),
    );
    let unit = output.vir().expect("owned-call VIR");
    let identity = unit
        .runtime()
        .functions
        .iter()
        .find(|function| function.name == "identity")
        .expect("identity function");
    let abi = unit
        .runtime()
        .abis
        .function(identity.id)
        .expect("identity ABI");

    assert_eq!(
        abi.signature.parameters()[0].interface().transfer,
        VirInterfaceTransfer::Move
    );
    assert_eq!(
        abi.signature.results()[0].interface().transfer,
        VirInterfaceTransfer::Move
    );
}

#[test]
fn resolver_rejects_a_call_with_a_noncanonical_logical_slot_map() {
    let output = accepted(
        "abi-direct.nera",
        include_str!("../spec/cases/aggregate/abi-direct.nera"),
    );
    let mut raw = output.vir().expect("direct ABI VIR").as_unit().clone();
    let target = raw.runtime.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .find_map(|instruction| match &mut instruction.instruction {
            VirInstruction::Call { target, .. } if target.symbol == "make_pair" => Some(target),
            _ => None,
        })
        .expect("make_pair call");
    target.abi = Some(VirAbiSignature::identity(&target.signature));

    let validated = raw
        .into_validated()
        .expect("identity call ABI is structurally self-consistent");
    let error = validated
        .resolve()
        .expect_err("callee canonical ABI must still be enforced");
    assert_eq!(
        error.kind(),
        &VirResolutionErrorKind::CallAbiMismatch("make_pair".to_owned())
    );
}

#[test]
fn raw_dump_does_not_assume_that_the_abi_table_was_validated() {
    let output = accepted(
        "abi-direct.nera",
        include_str!("../spec/cases/aggregate/abi-direct.nera"),
    );
    let mut raw = output.vir().expect("direct ABI VIR").as_unit().clone();
    raw.runtime.abis.functions.clear();

    let dump = raw.stable_dump();

    assert!(dump.contains("fn fn0"));
    assert!(raw.validate().is_err());
}
