use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, ValidatedVirUnit, VirAbiEnvironment,
    VirBasicBlock, VirBlockId, VirBlockTarget, VirCallTarget, VirConstant, VirContractId,
    VirExecution, VirExecutionError, VirExecutionErrorKind, VirFunction, VirFunctionId,
    VirInstruction, VirIntegerPredicate, VirInterpreterConfig, VirRegionId, VirResolutionErrorKind,
    VirRuntimeValue, VirSignature, VirTerminator, VirType, VirUnit, VirValidationErrorKind,
    VirValue, VirValueId, interpret, interpret_with_config, project_core0_compat,
};

#[test]
fn representative_raw_vir_v0_has_stable_dump_and_requires_a_call_contract() {
    let program = representative_program();

    assert_eq!(
        program
            .validate()
            .expect_err("a call cannot name a contract absent from the unit")
            .kind(),
        &VirValidationErrorKind::MissingCallContract(VirContractId::new(1))
    );
    assert_eq!(program.stable_dump(), EXPECTED_DUMP);
    assert_eq!(program.to_string(), EXPECTED_DUMP);

    let complete = executable_representative_program();
    let validated = complete
        .into_validated()
        .expect("the local callee supplies the checked call contract");
    assert_eq!(validated.stable_dump(), validated.to_string());
}

#[test]
fn validation_rejects_non_boolean_branch_condition() {
    let mut program = representative_program();
    let VirTerminator::Branch { condition, .. } =
        &mut program.runtime.functions[0].blocks[0].terminator.terminator
    else {
        panic!("entry block must branch");
    };
    *condition = VirValueId::new(4);

    assert!(matches!(
        program
            .validate()
            .expect_err("u64 is not a condition")
            .kind(),
        VirValidationErrorKind::TypeMismatch {
            context: "branch condition",
            expected: VirType::Bool,
            found: VirType::U64,
        }
    ));
}

#[test]
fn validation_requires_cross_block_values_to_use_block_parameters() {
    let mut program = representative_program();
    let VirTerminator::Return { values } =
        &mut program.runtime.functions[0].blocks[3].terminator.terminator
    else {
        panic!("exit block must return");
    };
    values[0] = VirValueId::new(23);

    assert_eq!(
        program
            .validate()
            .expect_err("a value from another block is unavailable")
            .kind(),
        &VirValidationErrorKind::ValueNotAvailableInBlock(VirValueId::new(23))
    );
}

#[test]
fn validation_checks_block_argument_arity() {
    let mut program = representative_program();
    let VirTerminator::Branch { then_target, .. } =
        &mut program.runtime.functions[0].blocks[0].terminator.terminator
    else {
        panic!("entry block must branch");
    };
    then_target.arguments.pop();

    assert_eq!(
        program
            .validate()
            .expect_err("target arity must match block parameters")
            .kind(),
        &VirValidationErrorKind::ArityMismatch {
            context: "block target arguments",
            expected: 3,
            found: 2,
        }
    );
}

#[test]
fn validation_rejects_duplicate_ssa_definitions() {
    let mut program = representative_program();
    let VirInstruction::Constant { result, .. } =
        &mut program.runtime.functions[0].blocks[0].instructions[1].instruction
    else {
        panic!("second instruction must be a constant");
    };
    result.id = VirValueId::new(0);

    assert_eq!(
        program
            .validate()
            .expect_err("SSA ids are unique within a function")
            .kind(),
        &VirValidationErrorKind::DuplicateValue(VirValueId::new(0))
    );
}

#[test]
fn validation_rejects_invalid_allocation_alignment() {
    let mut program = representative_program();
    let VirInstruction::Allocate { alignment, .. } =
        &mut program.runtime.functions[0].blocks[0].instructions[2].instruction
    else {
        panic!("third instruction must allocate");
    };
    *alignment = 3;

    assert_eq!(
        program
            .validate()
            .expect_err("alignment must be a nonzero power of two")
            .kind(),
        &VirValidationErrorKind::InvalidAlignment(3)
    );
}

#[test]
fn validation_rejects_forged_allocation_element_access() {
    let mut program = representative_program();
    let VirInstruction::Allocate { element, .. } =
        &mut program.runtime.functions[0].blocks[0].instructions[2].instruction
    else {
        panic!("third instruction must allocate");
    };
    let forged = nera::VirMemoryAccess::new(nera::VirTypeId::new(0), nera::VirLayoutId::new(9));
    *element = forged;

    assert_eq!(
        program
            .validate()
            .expect_err("allocation element must resolve in the program schema")
            .kind(),
        &VirValidationErrorKind::InvalidMemoryAccess(forged)
    );
}

#[test]
fn interpreter_executes_all_representative_vir_categories() {
    let mut program = representative_program();
    program.runtime.functions.push(identity_function());
    rebuild_source_map(&mut program);
    let validated = program
        .into_validated()
        .expect("representative VIR with a local call is well formed");

    let execution = execute(&validated).expect("representative VIR executes");

    assert_eq!(execution.values(), &[VirRuntimeValue::U64(41)]);
    assert_eq!(execution.steps(), 21);
}

#[test]
fn precise_initialize_rejects_an_initialized_cell() {
    let mut program = representative_program();
    program.runtime.functions[0].blocks[0].instructions[7].instruction =
        VirInstruction::Initialize {
            pointer: VirValueId::new(6),
            value: VirValueId::new(4),
            permission: VirValueId::new(2),
            access: nera::VirMemoryAccess::core_u64(),
        };
    program.runtime.functions.push(identity_function());
    rebuild_source_map(&mut program);
    let validated = program.into_validated().expect("replacement is well typed");

    let error = execute(&validated).expect_err("precise initialize requires an empty cell");

    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::InitializeAlreadyInitialized { .. }
    ));
}

#[test]
fn precise_store_rejects_an_uninitialized_cell() {
    let mut program = representative_program();
    program.runtime.functions[0].blocks[0].instructions[3].instruction = VirInstruction::Store {
        pointer: VirValueId::new(1),
        value: VirValueId::new(3),
        permission: VirValueId::new(2),
        access: nera::VirMemoryAccess::core_u64(),
    };
    program.runtime.functions.push(identity_function());
    rebuild_source_map(&mut program);
    let validated = program.into_validated().expect("replacement is well typed");

    let error = execute(&validated).expect_err("precise store requires an existing value");

    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::StoreToUninitialized { .. }
    ));
}

#[test]
fn core0_projection_erases_scalar_write_modes_but_rejects_wider_alignment() {
    for program in [
        single_block_memory_program(MemoryWrite::Initialize, 8),
        single_block_memory_program(MemoryWrite::Store, 8),
        single_block_memory_program(MemoryWrite::Write, 8),
    ] {
        let validated = program.into_validated().expect("test VIR is well formed");
        assert!(
            project_core0_compat(validated.resolve().expect("VIR resolves").runtime()).is_ok(),
            "the historical Core0 projection erases scalar write modes"
        );
    }

    let incompatible = single_block_memory_program(MemoryWrite::Write, 16)
        .into_validated()
        .expect("test VIR is well formed");
    assert!(project_core0_compat(incompatible.resolve().expect("VIR resolves").runtime()).is_err());
}

#[test]
fn resolution_rejects_external_duplicate_and_mismatched_calls() {
    let external = representative_program();
    assert_eq!(
        external
            .into_validated()
            .expect_err("unregistered external contracts fail closed")
            .kind(),
        &VirValidationErrorKind::MissingCallContract(VirContractId::new(1))
    );

    let mut duplicate = representative_program();
    duplicate.runtime.functions.push(identity_function());
    let mut duplicate_identity = identity_function();
    duplicate_identity.id = VirFunctionId::new(2);
    duplicate_identity.contract = VirContractId::new(2);
    duplicate.runtime.functions.push(duplicate_identity);
    rebuild_source_map(&mut duplicate);
    let duplicate = duplicate
        .into_validated()
        .expect("duplicate symbols are structural");
    assert!(matches!(
        duplicate.resolve().expect_err("symbols must resolve uniquely").kind(),
        VirResolutionErrorKind::DuplicateFunctionSymbol(symbol) if symbol == "identity"
    ));

    let mut signature = representative_program();
    let mut call_contract_owner = identity_function();
    call_contract_owner.name = "call_contract_owner".to_owned();
    signature.runtime.functions.push(call_contract_owner);
    let mut mismatched = identity_function();
    mismatched.id = VirFunctionId::new(2);
    mismatched.contract = VirContractId::new(2);
    mismatched.signature.parameters = vec![VirType::Bool];
    mismatched.signature.results = vec![VirType::Bool];
    mismatched.blocks[0].parameters[0].ty = VirType::Bool;
    signature.runtime.functions.push(mismatched);
    rebuild_source_map(&mut signature);
    let signature = signature
        .into_validated()
        .expect("both functions are structural");
    assert!(matches!(
        signature.resolve().expect_err("signature must match binding").kind(),
        VirResolutionErrorKind::CallSignatureMismatch(symbol) if symbol == "identity"
    ));

    let mut contract = representative_program();
    let mut call_contract_owner = identity_function();
    call_contract_owner.name = "call_contract_owner".to_owned();
    contract.runtime.functions.push(call_contract_owner);
    let mut mismatched = identity_function();
    mismatched.id = VirFunctionId::new(2);
    mismatched.contract = VirContractId::new(2);
    contract.runtime.functions.push(mismatched);
    rebuild_source_map(&mut contract);
    let contract = contract
        .into_validated()
        .expect("opaque contract ids are structural");
    assert!(matches!(
        contract.resolve().expect_err("contract must match binding").kind(),
        VirResolutionErrorKind::CallContractMismatch(symbol) if symbol == "identity"
    ));
}

#[test]
fn interpreter_checks_permission_transfer_failures() {
    let mut invalid_split = executable_representative_program();
    set_constant(&mut invalid_split, 12, 9);
    let error =
        execute_valid_program(invalid_split).expect_err("split outside permission must fail");
    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::InvalidPermissionSplit {
            split_at_bytes: 9,
            ..
        }
    ));

    let mut out_of_range = executable_representative_program();
    let split = instruction_position(&out_of_range, |instruction| {
        matches!(instruction, VirInstruction::PermissionSplit { .. })
    });
    out_of_range.runtime.functions[0].blocks[0]
        .instructions
        .insert(
            split + 1,
            instruction(VirInstruction::Write {
                pointer: VirValueId::new(1),
                value: VirValueId::new(3),
                permission: VirValueId::new(8),
                access: nera::VirMemoryAccess::core_u64(),
            }),
        );
    let error =
        execute_valid_program(out_of_range).expect_err("half permission cannot cover a full word");
    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::PermissionOutOfRange { .. }
    ));

    let mut invalid_join = executable_representative_program();
    invalid_join.runtime.functions[0].blocks[0]
        .instructions
        .insert(
            3,
            instruction(VirInstruction::Allocate {
                pointer_result: value(
                    50,
                    VirType::Pointer {
                        access: nera::VirMemoryAccess::core_u64(),
                    },
                ),
                permission_result: value(51, VirType::Permission),
                size_bytes: VirValueId::new(0),
                alignment: 8,
                region: VirRegionId::new(0),
                element: nera::VirMemoryAccess::core_u64(),
            }),
        );
    let join = invalid_join.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .find(|spanned| matches!(spanned.instruction, VirInstruction::PermissionJoin { .. }))
        .expect("permission join exists");
    let VirInstruction::PermissionJoin { right, .. } = &mut join.instruction else {
        unreachable!();
    };
    *right = VirValueId::new(51);
    let error = execute_valid_program(invalid_join)
        .expect_err("permissions from different allocations cannot be joined");
    assert_eq!(error.kind(), &VirExecutionErrorKind::InvalidPermissionJoin);

    let mut consumed = executable_representative_program();
    let VirTerminator::Branch { then_target, .. } = &mut consumed.runtime.functions[0].blocks[0]
        .terminator
        .terminator
    else {
        panic!("entry block must branch");
    };
    then_target.arguments[2] = VirValueId::new(10);
    let error = execute_valid_program(consumed)
        .expect_err("a consumed permission tombstone cannot authorize a later free");
    assert_eq!(
        error.kind(),
        &VirExecutionErrorKind::PermissionAlreadyConsumed(VirValueId::new(42))
    );

    let mut duplicated = executable_representative_program();
    duplicated.runtime.functions[0].blocks[1]
        .parameters
        .push(value(24, VirType::Permission));
    let VirTerminator::Branch { then_target, .. } = &mut duplicated.runtime.functions[0].blocks[0]
        .terminator
        .terminator
    else {
        panic!("entry block must branch");
    };
    then_target.arguments.push(VirValueId::new(11));
    let error =
        execute_valid_program(duplicated).expect_err("one permission cannot be transferred twice");
    assert_eq!(
        error.kind(),
        &VirExecutionErrorKind::PermissionDuplicated(VirValueId::new(11))
    );
}

#[test]
fn interpreter_checks_permission_allocation_and_false_control_flow() {
    let mut mismatch = executable_representative_program();
    mismatch.runtime.functions[0].blocks[0].instructions.insert(
        3,
        instruction(VirInstruction::Allocate {
            pointer_result: value(
                50,
                VirType::Pointer {
                    access: nera::VirMemoryAccess::core_u64(),
                },
            ),
            permission_result: value(51, VirType::Permission),
            size_bytes: VirValueId::new(0),
            alignment: 8,
            region: VirRegionId::new(0),
            element: nera::VirMemoryAccess::core_u64(),
        }),
    );
    let VirInstruction::Initialize { permission, .. } =
        &mut mismatch.runtime.functions[0].blocks[0].instructions[4].instruction
    else {
        panic!("initial write must initialize");
    };
    *permission = VirValueId::new(51);
    let error =
        execute_valid_program(mismatch).expect_err("permission from another allocation must fail");
    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::PermissionMismatch { .. }
    ));

    let mut checked = executable_representative_program();
    set_comparison(&mut checked, VirIntegerPredicate::NotEqual);
    let error = execute_valid_program(checked).expect_err("false check must fail");
    assert_eq!(error.kind(), &VirExecutionErrorKind::CheckFailed);

    let mut false_branch = executable_representative_program();
    set_comparison(&mut false_branch, VirIntegerPredicate::NotEqual);
    let check = instruction_position(&false_branch, |instruction| {
        matches!(instruction, VirInstruction::Check { .. })
    });
    false_branch.runtime.functions[0].blocks[0]
        .instructions
        .remove(check);
    let execution = execute_valid_program(false_branch).expect("false branch executes");
    assert_eq!(execution.values(), &[VirRuntimeValue::U64(82)]);
}

#[test]
fn explicit_stacks_enforce_loop_and_call_limits() {
    let loop_program = loop_program()
        .into_validated()
        .expect("loop VIR is structural");
    let loop_resolved = loop_program.resolve().expect("loop VIR resolves");
    let error = interpret_with_config(
        loop_resolved.runtime(),
        VirInterpreterConfig {
            max_steps: 2,
            ..VirInterpreterConfig::default()
        },
    )
    .expect_err("loop must stop at the step limit");
    assert_eq!(error.kind(), &VirExecutionErrorKind::StepLimitExceeded);

    let recursive = recursive_program()
        .into_validated()
        .expect("recursive VIR is structural");
    let recursive = recursive.resolve().expect("self call resolves");
    let error = interpret_with_config(
        recursive.runtime(),
        VirInterpreterConfig {
            max_call_depth: 2,
            ..VirInterpreterConfig::default()
        },
    )
    .expect_err("recursive calls must stop at the depth limit");
    assert_eq!(error.kind(), &VirExecutionErrorKind::CallDepthExceeded);
}

#[test]
fn permission_can_round_trip_through_a_resolved_call() {
    let validated = permission_call_program()
        .into_validated()
        .expect("permission call VIR is structural");
    let execution = execute(&validated).expect("returned permission can free its allocation");
    assert!(execution.values().is_empty());
    assert_eq!(execution.steps(), 6);
}

fn representative_program() -> VirUnit {
    let pointer_type = VirType::Pointer {
        access: nera::VirMemoryAccess::core_u64(),
    };
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "main\nquoted\"".to_owned(),
            signature: VirSignature {
                parameters: Vec::new(),
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![
                VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: Vec::new(),
                    instructions: vec![
                        instruction(VirInstruction::Constant {
                            result: value(0, VirType::U64),
                            value: VirConstant::U64(8),
                        }),
                        instruction(VirInstruction::Constant {
                            result: value(3, VirType::U64),
                            value: VirConstant::U64(41),
                        }),
                        instruction(VirInstruction::Allocate {
                            pointer_result: value(1, pointer_type),
                            permission_result: value(2, VirType::Permission),
                            size_bytes: VirValueId::new(0),
                            alignment: 8,
                            region: VirRegionId::new(0),
                            element: nera::VirMemoryAccess::core_u64(),
                        }),
                        instruction(VirInstruction::Initialize {
                            pointer: VirValueId::new(1),
                            value: VirValueId::new(3),
                            permission: VirValueId::new(2),
                            access: nera::VirMemoryAccess::core_u64(),
                        }),
                        instruction(VirInstruction::Load {
                            result: value(4, VirType::U64),
                            pointer: VirValueId::new(1),
                            permission: VirValueId::new(2),
                            access: nera::VirMemoryAccess::core_u64(),
                        }),
                        instruction(VirInstruction::Constant {
                            result: value(5, VirType::U64),
                            value: VirConstant::U64(0),
                        }),
                        instruction(VirInstruction::PointerOffset {
                            result: value(6, pointer_type),
                            base: VirValueId::new(1),
                            delta_bytes: VirValueId::new(5),
                        }),
                        instruction(VirInstruction::Store {
                            pointer: VirValueId::new(6),
                            value: VirValueId::new(4),
                            permission: VirValueId::new(2),
                            access: nera::VirMemoryAccess::core_u64(),
                        }),
                        instruction(VirInstruction::Write {
                            pointer: VirValueId::new(6),
                            value: VirValueId::new(4),
                            permission: VirValueId::new(2),
                            access: nera::VirMemoryAccess::core_u64(),
                        }),
                        instruction(VirInstruction::Compare {
                            result: value(7, VirType::Bool),
                            predicate: VirIntegerPredicate::Equal,
                            left: VirValueId::new(4),
                            right: VirValueId::new(3),
                        }),
                        instruction(VirInstruction::Constant {
                            result: value(12, VirType::U64),
                            value: VirConstant::U64(4),
                        }),
                        instruction(VirInstruction::PermissionSplit {
                            left_result: value(8, VirType::Permission),
                            right_result: value(9, VirType::Permission),
                            source: VirValueId::new(2),
                            split_at_bytes: VirValueId::new(12),
                        }),
                        instruction(VirInstruction::PermissionJoin {
                            result: value(10, VirType::Permission),
                            left: VirValueId::new(8),
                            right: VirValueId::new(9),
                        }),
                        instruction(VirInstruction::PermissionMove {
                            result: value(11, VirType::Permission),
                            source: VirValueId::new(10),
                        }),
                        instruction(VirInstruction::Check {
                            condition: VirValueId::new(7),
                        }),
                    ],
                    terminator: terminator(VirTerminator::Branch {
                        condition: VirValueId::new(7),
                        then_target: target(1, &[4, 1, 11]),
                        else_target: target(2, &[3, 1, 11]),
                    }),
                    source_span: span(),
                },
                VirBasicBlock {
                    id: VirBlockId::new(1),
                    parameters: vec![
                        value(20, VirType::U64),
                        value(21, pointer_type),
                        value(22, VirType::Permission),
                    ],
                    instructions: vec![instruction(VirInstruction::Call {
                        results: vec![value(23, VirType::U64)],
                        target: VirCallTarget {
                            symbol: "identity".to_owned(),
                            signature: VirSignature {
                                parameters: vec![VirType::U64],
                                results: vec![VirType::U64],
                            },
                            contract: VirContractId::new(1),
                            abi: None,
                        },
                        arguments: vec![VirValueId::new(20)],
                    })],
                    terminator: terminator(VirTerminator::Jump {
                        target: target(3, &[23, 21, 22]),
                    }),
                    source_span: span(),
                },
                VirBasicBlock {
                    id: VirBlockId::new(2),
                    parameters: vec![
                        value(30, VirType::U64),
                        value(31, pointer_type),
                        value(32, VirType::Permission),
                    ],
                    instructions: vec![instruction(VirInstruction::WordAdd {
                        result: value(33, VirType::U64),
                        left: VirValueId::new(30),
                        right: VirValueId::new(30),
                    })],
                    terminator: terminator(VirTerminator::Jump {
                        target: target(3, &[33, 31, 32]),
                    }),
                    source_span: span(),
                },
                VirBasicBlock {
                    id: VirBlockId::new(3),
                    parameters: vec![
                        value(40, VirType::U64),
                        value(41, pointer_type),
                        value(42, VirType::Permission),
                    ],
                    instructions: vec![instruction(VirInstruction::Free {
                        pointer: VirValueId::new(41),
                        permission: VirValueId::new(42),
                    })],
                    terminator: terminator(VirTerminator::Return {
                        values: vec![VirValueId::new(40)],
                    }),
                    source_span: span(),
                },
            ],
            source_span: span(),
        }],
    )
}

fn execute(program: &ValidatedVirUnit) -> Result<VirExecution, VirExecutionError> {
    let resolved = program.resolve().expect("test VIR resolves");
    interpret(resolved.runtime())
}

fn executable_representative_program() -> VirUnit {
    let mut program = representative_program();
    program.runtime.functions.push(identity_function());
    rebuild_source_map(&mut program);
    program
}

fn rebuild_source_map(program: &mut VirUnit) {
    program.runtime.abis = VirAbiEnvironment::identity(&program.runtime.functions);
    program.rebuild_implicit_contracts_from_runtime();
    program.rebuild_source_map_from_runtime("<vir-v0-test>", 100);
}

fn execute_valid_program(mut program: VirUnit) -> Result<VirExecution, VirExecutionError> {
    rebuild_source_map(&mut program);
    let validated = program.into_validated().expect("test VIR is well formed");
    execute(&validated)
}

fn set_constant(program: &mut VirUnit, id: u32, word: u64) {
    let instruction = program.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .find(|spanned| {
            matches!(
                spanned.instruction,
                VirInstruction::Constant { result, .. } if result.id == VirValueId::new(id)
            )
        })
        .expect("constant exists");
    let VirInstruction::Constant { value, .. } = &mut instruction.instruction else {
        unreachable!();
    };
    *value = VirConstant::U64(word);
}

fn set_comparison(program: &mut VirUnit, predicate: VirIntegerPredicate) {
    let instruction = program.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .find(|spanned| matches!(spanned.instruction, VirInstruction::Compare { .. }))
        .expect("comparison exists");
    let VirInstruction::Compare {
        predicate: current, ..
    } = &mut instruction.instruction
    else {
        unreachable!();
    };
    *current = predicate;
}

fn instruction_position(program: &VirUnit, predicate: impl Fn(&VirInstruction) -> bool) -> usize {
    program.runtime.functions[0].blocks[0]
        .instructions
        .iter()
        .position(|spanned| predicate(&spanned.instruction))
        .expect("instruction exists")
}

#[derive(Clone, Copy)]
enum MemoryWrite {
    Initialize,
    Write,
    Store,
}

fn single_block_memory_program(write: MemoryWrite, alignment: u64) -> VirUnit {
    let pointer_type = VirType::Pointer {
        access: nera::VirMemoryAccess::core_u64(),
    };
    let write = match write {
        MemoryWrite::Initialize => VirInstruction::Initialize {
            pointer: VirValueId::new(1),
            value: VirValueId::new(3),
            permission: VirValueId::new(2),
            access: nera::VirMemoryAccess::core_u64(),
        },
        MemoryWrite::Write => VirInstruction::Write {
            pointer: VirValueId::new(1),
            value: VirValueId::new(3),
            permission: VirValueId::new(2),
            access: nera::VirMemoryAccess::core_u64(),
        },
        MemoryWrite::Store => VirInstruction::Store {
            pointer: VirValueId::new(1),
            value: VirValueId::new(3),
            permission: VirValueId::new(2),
            access: nera::VirMemoryAccess::core_u64(),
        },
    };
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "compat".to_owned(),
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
                    instruction(VirInstruction::Constant {
                        result: value(0, VirType::U64),
                        value: VirConstant::U64(8),
                    }),
                    instruction(VirInstruction::Allocate {
                        pointer_result: value(1, pointer_type),
                        permission_result: value(2, VirType::Permission),
                        size_bytes: VirValueId::new(0),
                        alignment,
                        region: VirRegionId::new(0),
                        element: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Constant {
                        result: value(3, VirType::U64),
                        value: VirConstant::U64(1),
                    }),
                    instruction(write),
                ],
                terminator: terminator(VirTerminator::Return { values: Vec::new() }),
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

fn loop_program() -> VirUnit {
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "loop".to_owned(),
            signature: VirSignature {
                parameters: Vec::new(),
                results: Vec::new(),
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: Vec::new(),
                instructions: Vec::new(),
                terminator: terminator(VirTerminator::Jump {
                    target: target(0, &[]),
                }),
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

fn recursive_program() -> VirUnit {
    let signature = VirSignature {
        parameters: Vec::new(),
        results: Vec::new(),
    };
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "recursive".to_owned(),
            signature: signature.clone(),
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: Vec::new(),
                instructions: vec![instruction(VirInstruction::Call {
                    results: Vec::new(),
                    target: VirCallTarget {
                        symbol: "recursive".to_owned(),
                        signature,
                        contract: VirContractId::new(0),
                        abi: None,
                    },
                    arguments: Vec::new(),
                })],
                terminator: terminator(VirTerminator::Return { values: Vec::new() }),
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

fn permission_call_program() -> VirUnit {
    let pointer_type = VirType::Pointer {
        access: nera::VirMemoryAccess::core_u64(),
    };
    let permission_signature = VirSignature {
        parameters: vec![VirType::Permission],
        results: vec![VirType::Permission],
    };
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![
            VirFunction {
                id: VirFunctionId::new(0),
                name: "main".to_owned(),
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
                        instruction(VirInstruction::Constant {
                            result: value(0, VirType::U64),
                            value: VirConstant::U64(8),
                        }),
                        instruction(VirInstruction::Allocate {
                            pointer_result: value(1, pointer_type),
                            permission_result: value(2, VirType::Permission),
                            size_bytes: VirValueId::new(0),
                            alignment: 8,
                            region: VirRegionId::new(0),
                            element: nera::VirMemoryAccess::core_u64(),
                        }),
                        instruction(VirInstruction::Call {
                            results: vec![value(3, VirType::Permission)],
                            target: VirCallTarget {
                                symbol: "pass_permission".to_owned(),
                                signature: permission_signature.clone(),
                                contract: VirContractId::new(1),
                                abi: None,
                            },
                            arguments: vec![VirValueId::new(2)],
                        }),
                        instruction(VirInstruction::Free {
                            pointer: VirValueId::new(1),
                            permission: VirValueId::new(3),
                        }),
                    ],
                    terminator: terminator(VirTerminator::Return { values: Vec::new() }),
                    source_span: span(),
                }],
                source_span: span(),
            },
            VirFunction {
                id: VirFunctionId::new(1),
                name: "pass_permission".to_owned(),
                signature: permission_signature,
                contract: VirContractId::new(1),
                entry: VirBlockId::new(0),
                blocks: vec![VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![value(0, VirType::Permission)],
                    instructions: Vec::new(),
                    terminator: terminator(VirTerminator::Return {
                        values: vec![VirValueId::new(0)],
                    }),
                    source_span: span(),
                }],
                source_span: span(),
            },
        ],
    )
}

fn identity_function() -> VirFunction {
    VirFunction {
        id: VirFunctionId::new(1),
        name: "identity".to_owned(),
        signature: VirSignature {
            parameters: vec![VirType::U64],
            results: vec![VirType::U64],
        },
        contract: VirContractId::new(1),
        entry: VirBlockId::new(0),
        blocks: vec![VirBasicBlock {
            id: VirBlockId::new(0),
            parameters: vec![value(0, VirType::U64)],
            instructions: Vec::new(),
            terminator: terminator(VirTerminator::Return {
                values: vec![VirValueId::new(0)],
            }),
            source_span: span(),
        }],
        source_span: span(),
    }
}

fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

fn instruction(instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(),
    }
}

fn terminator(terminator: VirTerminator) -> SpannedVirTerminator {
    SpannedVirTerminator {
        terminator,
        source_span: span(),
    }
}

fn target(block: u32, arguments: &[u32]) -> VirBlockTarget {
    VirBlockTarget {
        block: VirBlockId::new(block),
        arguments: arguments.iter().copied().map(VirValueId::new).collect(),
    }
}

fn span() -> ByteSpan {
    ByteSpan::new(0, 100).expect("valid test span")
}

const EXPECTED_DUMP: &str = r#"vir-unit-v27
memory {
target little pointer 8/8 usize 8/8
type type0 = u64 layout layout0 capabilities copy/trivial-drop/resource-free/sized
layout layout0 type type0 size 8 align 8 abi scalar fields []
}
borrow-regions {
}
runtime {
entry fn0

fn fn0 "main\nquoted\"" () -> (u64) contract contract0 entry bb0 @0..100 {
  bb0() @0..100:
    %0: u64 = const.u64 8 @0..100
    %3: u64 = const.u64 41 @0..100
    %1: ptr<type0/layout0>, %2: permission = alloc %0 align 8 region0 access type0/layout0 @0..100
    init %1, %3 using %2 access type0/layout0 @0..100
    %4: u64 = load %1 using %2 access type0/layout0 @0..100
    %5: u64 = const.u64 0 @0..100
    %6: ptr<type0/layout0> = offset %1, %5 @0..100
    store %6, %4 using %2 access type0/layout0 @0..100
    write %6, %4 using %2 access type0/layout0 @0..100
    %7: bool = cmp.eq %4, %3 @0..100
    %12: u64 = const.u64 4 @0..100
    %8: permission, %9: permission = permission.split %2 at %12 @0..100
    %10: permission = permission.join %8, %9 @0..100
    %11: permission = permission.move %10 @0..100
    check %7 @0..100
    branch %7 then bb1(%4, %1, %11) else bb2(%3, %1, %11) @0..100
  bb1(%20: u64, %21: ptr<type0/layout0>, %22: permission) @0..100:
    %23: u64 = call "identity" contract contract1 (%20) : (u64) -> (u64) @0..100
    jump bb3(%23, %21, %22) @0..100
  bb2(%30: u64, %31: ptr<type0/layout0>, %32: permission) @0..100:
    %33: u64 = add %30, %30 @0..100
    jump bb3(%33, %31, %32) @0..100
  bb3(%40: u64, %41: ptr<type0/layout0>, %42: permission) @0..100:
    free %41 using %42 @0..100
    return (%40) @0..100
}
}
specs {
contract contract0 function fn0 () -> (u64) {
  binder binder0 ensures slot0: u64
  clauses []
}
}
source-map {
source source0 "<hand-authored-vir>" bytes 100
origin origin0 = user source0 @0..100
origin origin1 = generated origin0 reason control-flow-block
origin origin2 = generated origin0 reason block-parameter
location fn0:entry -> origin0
location fn0/bb0:entry -> origin0
location fn0/bb1:entry -> origin1
location fn0/bb2:entry -> origin1
location fn0/bb3:entry -> origin1
location fn0/bb1:parameter0 -> origin2
location fn0/bb1:parameter1 -> origin2
location fn0/bb1:parameter2 -> origin2
location fn0/bb2:parameter0 -> origin2
location fn0/bb2:parameter1 -> origin2
location fn0/bb2:parameter2 -> origin2
location fn0/bb3:parameter0 -> origin2
location fn0/bb3:parameter1 -> origin2
location fn0/bb3:parameter2 -> origin2
location fn0/bb0:instruction0 -> origin0
location fn0/bb0:instruction1 -> origin0
location fn0/bb0:instruction2 -> origin0
location fn0/bb0:instruction3 -> origin0
location fn0/bb0:instruction4 -> origin0
location fn0/bb0:instruction5 -> origin0
location fn0/bb0:instruction6 -> origin0
location fn0/bb0:instruction7 -> origin0
location fn0/bb0:instruction8 -> origin0
location fn0/bb0:instruction9 -> origin0
location fn0/bb0:instruction10 -> origin0
location fn0/bb0:instruction11 -> origin0
location fn0/bb0:instruction12 -> origin0
location fn0/bb0:instruction13 -> origin0
location fn0/bb0:instruction14 -> origin0
location fn0/bb1:instruction0 -> origin0
location fn0/bb2:instruction0 -> origin0
location fn0/bb3:instruction0 -> origin0
location fn0/bb1:call-edge0 -> origin0
location fn0/bb0:terminator -> origin0
location fn0/bb1:terminator -> origin0
location fn0/bb2:terminator -> origin0
location fn0/bb3:terminator -> origin0
}
"#;
