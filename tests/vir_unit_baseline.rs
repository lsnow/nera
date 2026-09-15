use nera::{
    ByteSpan, CfgAnalysisConfig, ObligationStatus, SourceFile, SpannedVirInstruction,
    SpannedVirTerminator, ValidatedVirUnit, VerifierDiagnosticKind, VirBasicBlock, VirBlockId,
    VirConstant, VirContractId, VirContractPosition, VirExecutionErrorKind, VirFunction,
    VirFunctionId, VirInstruction, VirMemorySchema, VirSignature, VirTerminator, VirType, VirUnit,
    VirUnitVersion, VirValue, VirValueId, analyze, interpret, verify_program,
};

#[path = "support/contract_builder.rs"]
mod contract_builder;

use contract_builder::{add_u64_range, function_origin};

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(start, end).expect("valid test span")
}

fn runtime_check_program(condition: bool) -> ValidatedVirUnit {
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "runtime_check".to_owned(),
            signature: VirSignature {
                parameters: Vec::new(),
                results: Vec::new(),
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: Vec::new(),
                instructions: vec![
                    SpannedVirInstruction {
                        instruction: VirInstruction::Constant {
                            result: VirValue {
                                id: VirValueId::new(0),
                                ty: VirType::Bool,
                            },
                            value: VirConstant::Bool(condition),
                        },
                        source_span: span(1, 2),
                    },
                    SpannedVirInstruction {
                        instruction: VirInstruction::Check {
                            condition: VirValueId::new(0),
                        },
                        source_span: span(3, 4),
                    },
                ],
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return { values: Vec::new() },
                    source_span: span(5, 6),
                },
                source_span: span(0, 7),
            }],
            source_span: span(0, 7),
        }],
    )
    .into_validated()
    .expect("baseline runtime check VIR must validate")
}

fn with_scalar_result(program: &ValidatedVirUnit, expected: u64) -> ValidatedVirUnit {
    let mut unit = program.as_unit().clone();
    let origin = function_origin(&unit, VirFunctionId::new(0));
    add_u64_range(
        &mut unit.specs,
        VirContractId::new(0),
        VirContractPosition::Ensures,
        origin,
        0,
        expected,
        expected,
    );
    unit.into_validated().expect("scalar result contract")
}

#[test]
fn runtime_check_executes_and_is_verified_from_the_same_unit() {
    let program = runtime_check_program(false);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("a closed contract set reaches check verification");
    assert!(!verification.is_memory_checked_core0());
    assert!(
        verification
            .diagnostics()
            .iter()
            .any(|diagnostic| { diagnostic.kind() == VerifierDiagnosticKind::RefutedObligation })
    );

    let resolved = program.resolve().expect("runtime check program resolves");
    let error = interpret(resolved.runtime()).expect_err("false runtime check must fault");
    assert_eq!(error.kind(), &VirExecutionErrorKind::CheckFailed);
    assert_eq!(error.source_span(), span(3, 4));
}

#[test]
fn true_runtime_check_is_both_executed_and_proven() {
    let program = runtime_check_program(true);
    let verification = verify_program(
        &program.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("a closed contract set reaches check verification");
    assert!(verification.is_memory_checked_core0());
    assert!(
        verification
            .functions()
            .values()
            .flat_map(|function| function.cfg().obligations())
            .all(|obligation| obligation.obligation().status() == ObligationStatus::Proven)
    );

    let resolved = program.resolve().expect("runtime check program resolves");
    assert!(interpret(resolved.runtime()).is_ok());
}

#[test]
fn embedded_contracts_change_verification_but_not_runtime_behavior() {
    let source = SourceFile::new("contract-boundary.nera", b"fn main() -> u64 { return 1; }");
    let output = analyze(&source);
    let program = output
        .vir()
        .expect("baseline source lowers to validated VIR");
    let resolved = program.resolve().expect("baseline source resolves");
    let runtime_before = interpret(resolved.runtime()).expect("baseline source executes");

    let accepted_program = with_scalar_result(program, 1);
    let rejected_program = with_scalar_result(program, 2);
    let accepted = verify_program(
        &accepted_program
            .resolve()
            .expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("matching postcondition is checked");
    let rejected = verify_program(
        &rejected_program
            .resolve()
            .expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("mismatching postcondition is reported, not a structural error");
    let rejected_again = verify_program(
        &rejected_program
            .resolve()
            .expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("the same mismatching postcondition is deterministic");

    assert!(accepted.is_memory_checked_core0());
    assert!(!rejected.is_memory_checked_core0());
    assert_eq!(rejected, rejected_again);
    assert!(
        rejected.diagnostics().iter().any(|diagnostic| {
            diagnostic.kind() == VerifierDiagnosticKind::RefutedPostcondition
        })
    );
    assert_eq!(
        interpret(resolved.runtime()).expect("contract checking cannot mutate runtime VIR"),
        runtime_before
    );
    let stable_dump = program.stable_dump();
    assert_eq!(program.stable_dump(), stable_dump);
}

#[test]
fn unit_owns_all_tables_and_exposes_a_read_only_runtime_view() {
    let program = runtime_check_program(true);
    let unit = program.as_unit();
    let runtime = program.runtime();

    assert_eq!(unit.version, VirUnitVersion::V28);
    assert_eq!(unit.specs.len(), 1);
    assert_eq!(unit.specs.contracts()[0].function, VirFunctionId::new(0));
    assert!(!unit.source_map.sources().is_empty());
    assert!(std::ptr::eq(runtime.memory, &unit.memory));
    assert_eq!(runtime.entry, unit.runtime.entry);
    assert_eq!(runtime.functions, unit.runtime.functions.as_slice());

    let dump = unit.stable_dump();
    let sections = [
        "vir-unit-v28",
        "memory {",
        "borrow-regions {",
        "runtime {",
        "specs {",
        "source-map {",
    ];
    let positions = sections.map(|section| {
        dump.find(section)
            .unwrap_or_else(|| panic!("full-unit dump must contain {section}"))
    });
    assert!(positions.windows(2).all(|pair| pair[0] < pair[1]));

    let runtime_dump = runtime.stable_dump();
    assert!(runtime_dump.starts_with("runtime-vir-v17\n"));
    assert!(!runtime_dump.contains("specs {"));
    assert!(!runtime_dump.contains("source-map {"));
}

#[test]
fn historical_unit_versions_fail_closed_at_the_current_schema_boundary() {
    let program = runtime_check_program(true);
    let mut legacy = program.as_unit().clone();
    legacy.version = VirUnitVersion::V1;
    assert_eq!(
        legacy
            .validate()
            .expect_err("V1 has no capability/effect schema")
            .kind(),
        &nera::VirValidationErrorKind::UnsupportedUnitVersion(VirUnitVersion::V1)
    );
    assert!(legacy.stable_dump().starts_with("vir-unit-v1\n"));

    legacy.version = VirUnitVersion::V2;
    assert_eq!(
        legacy
            .validate()
            .expect_err("V2 has no capability/effect schema")
            .kind(),
        &nera::VirValidationErrorKind::UnsupportedUnitVersion(VirUnitVersion::V2)
    );

    legacy.version = VirUnitVersion::V3;
    assert_eq!(
        legacy
            .validate()
            .expect_err("pre-resource-payload V3 must fail closed")
            .kind(),
        &nera::VirValidationErrorKind::UnsupportedUnitVersion(VirUnitVersion::V3)
    );
    legacy.version = VirUnitVersion::V4;
    assert_eq!(
        legacy
            .validate()
            .expect_err("V4 has no builtin-drop effect schema")
            .kind(),
        &nera::VirValidationErrorKind::UnsupportedUnitVersion(VirUnitVersion::V4)
    );
    legacy.version = VirUnitVersion::V5;
    assert_eq!(
        legacy
            .validate()
            .expect_err("V5 has no explicit loan effect schema")
            .kind(),
        &nera::VirValidationErrorKind::UnsupportedUnitVersion(VirUnitVersion::V5)
    );
    legacy.version = VirUnitVersion::V6;
    assert_eq!(
        legacy
            .validate()
            .expect_err("V6 has no stored loan-authority effect schema")
            .kind(),
        &nera::VirValidationErrorKind::UnsupportedUnitVersion(VirUnitVersion::V6)
    );
    legacy.version = VirUnitVersion::V7;
    assert_eq!(
        legacy
            .validate()
            .expect_err("V7 has no address-only safe-slice instruction schema")
            .kind(),
        &nera::VirValidationErrorKind::UnsupportedUnitVersion(VirUnitVersion::V7)
    );
    legacy.version = VirUnitVersion::V8;
    assert_eq!(
        legacy
            .validate()
            .expect_err("pre-borrow-call schema must not use the current ABI")
            .kind(),
        &nera::VirValidationErrorKind::UnsupportedUnitVersion(VirUnitVersion::V8)
    );
    for version in [
        VirUnitVersion::V9,
        VirUnitVersion::V10,
        VirUnitVersion::V11,
        VirUnitVersion::V12,
        VirUnitVersion::V13,
        VirUnitVersion::V14,
        VirUnitVersion::V15,
        VirUnitVersion::V16,
        VirUnitVersion::V17,
        VirUnitVersion::V18,
        VirUnitVersion::V19,
        VirUnitVersion::V20,
        VirUnitVersion::V21,
        VirUnitVersion::V22,
        VirUnitVersion::V23,
        VirUnitVersion::V24,
        VirUnitVersion::V25,
        VirUnitVersion::V26,
        VirUnitVersion::V27,
    ] {
        legacy.version = version;
        assert_eq!(
            legacy.validate().unwrap_err().kind(),
            &nera::VirValidationErrorKind::UnsupportedUnitVersion(version)
        );
    }
}
