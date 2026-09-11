use nera::{
    CfgAnalysisConfig, FrontendStatus, ObligationStatus, ResourceObligationKind, SourceFile,
    VirAbiValue, VirInterfaceStorage, VirInterfaceTransfer, VirRuntimeValue, analyze, interpret,
    verify_program,
};

#[test]
fn owning_aggregate_crosses_direct_calls_with_exactly_once_transfer() {
    let source = include_str!("../spec/cases/aggregate/owning-abi.nera");
    let output = analyze(&SourceFile::from_text("owning-abi.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "issues: {:?}",
        output.issues()
    );
    let unit = output.vir().expect("owning aggregate source has VIR");
    assert!(unit.runtime().abis.functions.iter().any(|function| {
        function
            .signature
            .parameters()
            .iter()
            .chain(function.signature.results())
            .any(|binding| {
                matches!(binding.value(), VirAbiValue::IndirectAggregate { .. })
                    && binding.interface().transfer == VirInterfaceTransfer::Move
                    && binding.interface().storage == VirInterfaceStorage::Indirect
            })
    }));

    let resolved = unit.resolve().expect("owning aggregate VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("owning aggregate verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
    assert!(verification.functions().values().any(|function| {
        function.cfg().obligations().iter().any(|record| {
            matches!(
                record.obligation().kind(),
                ResourceObligationKind::AggregateAbiPayloadValid { .. }
            ) && record.obligation().status() == ObligationStatus::Proven
        })
    }));
    assert_eq!(
        interpret(resolved.runtime())
            .expect("owning aggregate source executes")
            .values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn missing_aggregate_return_transfer_is_rejected_by_payload_and_conservation_checks() {
    let source = include_str!("../spec/cases/aggregate/owning-abi.nera");
    let output = analyze(&SourceFile::from_text("owning-abi.nera", source));
    let mut unit = output
        .vir()
        .expect("owning aggregate source has VIR")
        .as_unit()
        .clone();
    let choose = unit
        .runtime
        .functions
        .iter_mut()
        .find(|function| function.name == "choose")
        .expect("choose function");
    let mut removed = false;
    for block in &mut choose.blocks {
        block.instructions.retain(|instruction| {
            if !removed
                && matches!(
                    instruction.instruction,
                    nera::VirInstruction::ObjectTransfer { .. }
                )
            {
                removed = true;
                false
            } else {
                true
            }
        });
    }
    assert!(removed, "return-buffer transfer mutation must apply");
    unit.rebuild_source_map_from_runtime("owning-abi-mutation.nera", source.len());
    let validated = unit
        .into_validated()
        .expect("missing semantic transfer remains structurally valid");
    let verification = verify_program(
        &validated.resolve().expect("mutated VIR resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("mutated aggregate verification converges");
    assert!(!verification.is_memory_checked_core0());
    assert!(verification.functions().values().any(|function| {
        function.cfg().obligations().iter().any(|record| {
            matches!(
                record.obligation().kind(),
                ResourceObligationKind::AggregateAbiPayloadValid { .. }
                    | ResourceObligationKind::OwnershipConserved { .. }
            ) && record.obligation().status() != ObligationStatus::Proven
        })
    }));
}

#[test]
fn variant_dependent_owner_abi_stays_explicitly_gated() {
    let output = analyze(&SourceFile::from_text(
        "variant-owner-abi.nera",
        "enum Package { Empty, Full(Own<u64>), }\n\
         fn pass(package: Package) -> Package { return package; }\n\
         fn main() -> u64 { return 0; }",
    ));
    assert_eq!(output.status(), FrontendStatus::Unsupported);
    assert!(output.issues().iter().any(|issue| {
        issue
            .diagnostic()
            .message()
            .contains("conditional interface summary")
    }));
}

#[test]
fn aggregate_abi_does_not_upgrade_an_uninitialized_owner_payload() {
    let source = "struct Package { owner: Own<u64>, }\n\
                  fn make() -> Package {\n\
                      let owner = alloc<u64>(1);\n\
                      return Package { owner: owner };\n\
                  }\n\
                  fn main() -> u64 {\n\
                      let package = make();\n\
                      let owner = package.owner;\n\
                      free(owner);\n\
                      return 0;\n\
                  }";
    let output = analyze(&SourceFile::from_text("uninitialized-result.nera", source));
    assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
    let verification = verify_program(
        &output
            .vir()
            .expect("uninitialized result has VIR")
            .resolve()
            .expect("uninitialized result resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("uninitialized result verification converges");
    assert!(!verification.is_memory_checked_core0());
    assert!(verification.functions().values().any(|function| {
        function.cfg().obligations().iter().any(|record| {
            matches!(
                record.obligation().kind(),
                ResourceObligationKind::AggregateAbiPayloadValid { .. }
            ) && record.obligation().status() == ObligationStatus::Refuted
        })
    }));
}
