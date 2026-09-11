use nera::{
    FrontendStatus, SourceFile, ValidatedVirUnit, VirExecution, VirExecutionError,
    VirExecutionErrorKind, VirInstruction, VirInterpreterConfig, VirRuntimeValue,
    VirValidationErrorKind, analyze, interpret, interpret_with_config,
};

#[path = "support/address_program.rs"]
mod address_program;

#[test]
fn typed_field_and_index_addresses_execute_with_nominal_runtime_identity() {
    let validated = address_program::validated();
    let execution = execute(&validated).expect("typed address program executes");
    assert_eq!(execution.values(), &[VirRuntimeValue::U64(99)]);

    let mut out_of_bounds = validated.as_unit().clone();
    let VirInstruction::Constant { value, .. } =
        &mut out_of_bounds.runtime.functions[0].blocks[0].instructions[3].instruction
    else {
        panic!("index constant fixture")
    };
    *value = nera::VirConstant::U64(4);
    let out_of_bounds = out_of_bounds
        .into_validated()
        .expect("runtime index remains structurally valid");
    assert!(matches!(
        execute(&out_of_bounds)
            .expect_err("index equal to length must fault")
            .kind(),
        VirExecutionErrorKind::IndexOutOfBounds {
            index: 4,
            length: 4
        }
    ));

    let mut wrong_root = validated.as_unit().clone();
    let VirInstruction::Allocate { element, .. } =
        &mut wrong_root.runtime.functions[0].blocks[0].instructions[1].instruction
    else {
        panic!("allocation fixture")
    };
    *element = address_program::ARRAY_ACCESS;
    assert!(matches!(
        wrong_root
            .validate()
            .expect_err("allocation result carries its nominal access")
            .kind(),
        VirValidationErrorKind::TypeMismatch {
            context: "allocation pointer result",
            ..
        }
    ));

    let mut skipped_index = validated.as_unit().clone();
    let VirInstruction::Write { pointer, .. } =
        &mut skipped_index.runtime.functions[0].blocks[0].instructions[6].instruction
    else {
        panic!("typed write fixture")
    };
    *pointer = nera::VirValueId::new(3);
    assert!(matches!(
        skipped_index
            .validate()
            .expect_err("leaf access requires a leaf pointer type")
            .kind(),
        VirValidationErrorKind::TypeMismatch {
            context: "write pointer",
            ..
        }
    ));

    let mut undersized = validated.as_unit().clone();
    let VirInstruction::Constant { value, .. } =
        &mut undersized.runtime.functions[0].blocks[0].instructions[0].instruction
    else {
        panic!("allocation size fixture")
    };
    *value = nera::VirConstant::U64(32);
    let undersized = undersized
        .into_validated()
        .expect("dynamic allocation size remains structural VIR");
    assert!(matches!(
        execute(&undersized)
            .expect_err("root object outside allocation must fault")
            .kind(),
        VirExecutionErrorKind::AddressOutOfBounds { .. }
    ));

    let mut underaligned = validated.as_unit().clone();
    let VirInstruction::Allocate { alignment, .. } =
        &mut underaligned.runtime.functions[0].blocks[0].instructions[1].instruction
    else {
        panic!("allocation fixture")
    };
    *alignment = 4;
    let underaligned = underaligned
        .into_validated()
        .expect("unsafe alignment is a runtime/verifier condition");
    assert!(matches!(
        execute(&underaligned)
            .expect_err("misaligned root object must fault")
            .kind(),
        VirExecutionErrorKind::MisalignedAccess {
            required_alignment: 8,
            ..
        }
    ));
}

#[test]
fn source_to_vir_execution_returns_the_expected_word() {
    let source = SourceFile::new(
        "accepted-core0.nera",
        include_bytes!("../spec/cases/frontend/accepted-core0.nera"),
    );
    let output = analyze(&source);
    assert_eq!(output.status(), FrontendStatus::AcceptedProposal);

    let execution =
        execute(output.vir().expect("accepted source has VIR")).expect("accepted corpus executes");

    assert_eq!(execution.values(), &[VirRuntimeValue::U64(42)]);
    assert!(execution.steps() > 0);
}

#[test]
fn unit_source_executes_with_no_return_values() {
    let validated = lower("fn unit() { return; }");

    let execution = execute(&validated).expect("unit program executes");

    assert!(execution.values().is_empty());
    assert_eq!(execution.steps(), 1);
}

#[test]
fn uninitialized_source_read_is_an_explicit_fault() {
    let validated = lower(
        "fn bad() -> u64 {
            let memory = alloc<u64>(1);
            let value = *memory;
            free(memory);
            return value;
        }",
    );

    let error = execute(&validated).expect_err("uninitialized read must fault");

    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::UninitializedRead { .. }
    ));
    assert!(error.source_span().end() > error.source_span().start());
}

#[test]
fn ordinary_write_can_initialize_and_then_update_a_cell() {
    let validated = lower(
        "fn write_twice() -> u64 {
            let memory = alloc<u64>(1);
            *memory = 1;
            *memory = 2;
            let value = *memory;
            free(memory);
            return value;
        }",
    );

    let execution = execute(&validated).expect("ordinary writes accept either prior state");

    assert_eq!(execution.values(), &[VirRuntimeValue::U64(2)]);
}

#[test]
fn use_after_free_is_not_masked_by_consumed_permission() {
    let output = analyze(&SourceFile::new(
        "uaf.nera",
        include_bytes!("../spec/cases/verify/uaf.nera"),
    ));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "frontend issues: {:?}",
        output.issues()
    );

    let error = execute(output.vir().expect("accepted source has VIR"))
        .expect_err("use after free must fault");

    assert_eq!(
        error.kind(),
        &VirExecutionErrorKind::UseAfterFree { allocation: 0 }
    );
    assert_eq!(error.source_span().start(), 76);
    assert_eq!(error.source_span().end(), 78);
}

#[test]
fn repeated_free_is_reported_as_double_free() {
    let validated = lower(
        "fn bad() {
            let memory = alloc<u64>(1);
            free(memory);
            free(memory);
            return;
        }",
    );

    let error = execute(&validated).expect_err("repeated free must fault");

    assert_eq!(
        error.kind(),
        &VirExecutionErrorKind::DoubleFree { allocation: 0 }
    );
}

#[test]
fn one_past_pointer_access_is_an_explicit_fault() {
    let validated = lower(
        "fn bad() -> u64 {
            let memory = alloc<u64>(1);
            let one_past = memory + 8;
            *one_past = 1;
            free(memory);
            return 0;
        }",
    );

    let error = execute(&validated).expect_err("one-past pointer cannot be dereferenced");

    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::OutOfBoundsAccess {
            offset_bytes: 8,
            size_bytes: 8,
            ..
        }
    ));
}

#[test]
fn zero_sized_allocation_is_an_explicit_fault() {
    let validated = lower(
        "fn bad() {
            let memory = alloc<u64>(0);
            free(memory);
            return;
        }",
    );

    let error = execute(&validated).expect_err("zero-sized allocation must fault");

    assert_eq!(
        error.kind(),
        &VirExecutionErrorKind::AllocationFailure {
            size_bytes: 0,
            limit_bytes: 4096,
        }
    );
}

#[test]
fn execution_budget_stops_before_the_first_instruction() {
    let validated = lower("fn limited() -> u64 { return 1; }");
    let config = VirInterpreterConfig {
        max_steps: 0,
        ..VirInterpreterConfig::default()
    };

    let resolved = validated.resolve().expect("source VIR resolves");
    let error =
        interpret_with_config(resolved.runtime(), config).expect_err("zero budget must stop");

    assert_eq!(error.kind(), &VirExecutionErrorKind::StepLimitExceeded);
}

fn lower(text: &str) -> nera::ValidatedVirUnit {
    let output = analyze(&SourceFile::from_text("interpreter-test.nera", text));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "frontend issues: {:?}",
        output.issues()
    );
    output.vir().expect("accepted source has VIR").clone()
}

fn execute(program: &ValidatedVirUnit) -> Result<VirExecution, VirExecutionError> {
    let resolved = program.resolve().expect("source VIR resolves");
    interpret(resolved.runtime())
}
