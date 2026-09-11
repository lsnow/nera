use nera::backend::{
    X86_64_UNKNOWN_LINUX_GNU, X86_64CodegenErrorKind, X86_64ConditionCode, X86_64ExternalSymbol,
    X86_64IntegerRegister, X86_64MachineInstruction, X86_64MachineLabel, X86_64MachineRead,
    X86_64MachineSymbol, X86_64MachineWrite, X86_64PlanningErrorKind, X86_64RuntimeHelper,
};
use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, VirBasicBlock, VirBlockId, VirConstant,
    VirContractId, VirFunction, VirFunctionId, VirInstruction, VirIntegerPredicate, VirRegionId,
    VirSignature, VirTerminator, VirType, VirUnit, VirValue, VirValueId,
};

#[path = "support/address_program.rs"]
mod address_program;

#[test]
fn typed_addresses_use_canonical_field_offset_and_array_stride() {
    let validated = address_program::validated();
    let resolved = validated.resolve().expect("typed address fixture resolves");
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("typed addresses are selectable");
    let function = machine
        .function(VirFunctionId::new(0))
        .expect("entry function exists");
    let body = block(function, vir_block_label(0, 0));
    assert!(body.instructions().iter().any(|instruction| matches!(
        instruction,
        X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Register(X86_64IntegerRegister::R11),
            source: X86_64MachineRead::Immediate(8),
        }
    )));
    assert!(body.instructions().iter().any(|instruction| matches!(
        instruction,
        X86_64MachineInstruction::Multiply64 {
            destination: X86_64IntegerRegister::R10,
            source: X86_64MachineRead::Register(X86_64IntegerRegister::R11),
        }
    )));
    let assembly = X86_64_UNKNOWN_LINUX_GNU
        .emit_assembly(&machine)
        .expect("typed address machine plan emits");
    assert!(assembly.contains("imul r10, r11"));

    let mut wrong_target = validated.as_unit().clone();
    wrong_target.memory.target.usize_size_bytes = 4;
    wrong_target.memory.target.usize_alignment = 4;
    let wrong_target = wrong_target
        .into_validated()
        .expect("32-bit usize target remains a valid abstract VIR profile");
    let wrong_target = wrong_target.resolve().expect("fixture has no calls");
    let error = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(wrong_target.runtime())
        .expect_err("x86_64 backend must reject a foreign memory target");
    assert!(matches!(
        error.kind(),
        X86_64CodegenErrorKind::Planning(planning)
            if planning.kind() == &X86_64PlanningErrorKind::UnsupportedMemoryTarget
    ));
}

#[test]
fn memory_operations_lower_without_dynamic_safety_checks() {
    let validated = memory_program()
        .into_validated()
        .expect("memory VIR is well formed");
    let resolved = validated.resolve().expect("there are no source calls");
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("the complete VIR v0 instruction set is selectable");
    let function = machine
        .function(VirFunctionId::new(0))
        .expect("entry function exists");
    let body = block(function, vir_block_label(0, 0));
    assert!(
        machine
            .planning()
            .function(VirFunctionId::new(0))
            .expect("function plan exists")
            .frame()
            .value_slot(VirValueId::new(2))
            .is_none()
    );

    let allocator_call = body
        .instructions()
        .iter()
        .position(|instruction| {
            *instruction
                == X86_64MachineInstruction::CallRuntime {
                    helper: X86_64RuntimeHelper::AllocOrAbort,
                }
        })
        .expect("Allocate calls the private allocator");
    assert_eq!(
        body.instructions()[allocator_call - 1],
        X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Register(X86_64IntegerRegister::Rsi),
            source: X86_64MachineRead::Immediate(8),
        },
        "requested alignment 4 is raised to the native word alignment"
    );
    assert!(matches!(
        body.instructions()[allocator_call + 1],
        X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Memory(_),
            source: X86_64MachineRead::Register(X86_64IntegerRegister::Rax),
        }
    ));

    let raw_stores = body
        .instructions()
        .iter()
        .filter(|instruction| {
            matches!(
                instruction,
                X86_64MachineInstruction::Move64 {
                    destination: X86_64MachineWrite::Memory(memory),
                    source: X86_64MachineRead::Register(X86_64IntegerRegister::R10),
                } if memory.base() == X86_64IntegerRegister::R11
                    && memory.displacement() == 0
            )
        })
        .count();
    assert_eq!(
        raw_stores, 3,
        "Initialize, Write and Store share one raw store"
    );

    let raw_loads = body
        .instructions()
        .iter()
        .filter(|instruction| {
            matches!(
                instruction,
                X86_64MachineInstruction::Move64 {
                    destination: X86_64MachineWrite::Register(X86_64IntegerRegister::R10),
                    source: X86_64MachineRead::Memory(memory),
                } if memory.base() == X86_64IntegerRegister::R11
                    && memory.displacement() == 0
            )
        })
        .count();
    assert_eq!(raw_loads, 2);

    let delta_slot = machine
        .planning()
        .function(VirFunctionId::new(0))
        .expect("function plan exists")
        .frame()
        .value_slot(VirValueId::new(5))
        .expect("delta has a frame slot");
    assert!(body.instructions().iter().any(|instruction| {
        matches!(
            instruction,
            X86_64MachineInstruction::Add64 {
                destination: X86_64IntegerRegister::R10,
                source: X86_64MachineRead::Memory(memory),
            } if memory.base() == X86_64IntegerRegister::Rbp
                && memory.displacement() == delta_slot.offset_from_rbp_bytes()
        )
    }));

    assert!(
        body.instructions()
            .contains(&X86_64MachineInstruction::CallExternal {
                symbol: X86_64ExternalSymbol::Free,
            })
    );
    let runtime_calls = body
        .instructions()
        .iter()
        .filter(|instruction| {
            matches!(
                instruction,
                X86_64MachineInstruction::CallRuntime { .. }
                    | X86_64MachineInstruction::CallExternal { .. }
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        runtime_calls,
        vec![
            &X86_64MachineInstruction::CallRuntime {
                helper: X86_64RuntimeHelper::AllocOrAbort,
            },
            &X86_64MachineInstruction::CallExternal {
                symbol: X86_64ExternalSymbol::Free,
            },
        ],
        "raw memory operations do not receive dynamic safety helpers"
    );
    let check_branches = body
        .instructions()
        .iter()
        .filter(|instruction| {
            **instruction
                == X86_64MachineInstruction::JumpIf {
                    condition: X86_64ConditionCode::Equal,
                    target: X86_64MachineLabel::FunctionAbort(VirFunctionId::new(0)),
                }
        })
        .count();
    assert_eq!(
        check_branches, 2,
        "runtime checks are retained even for the same value"
    );

    let abort_blocks = function
        .blocks()
        .iter()
        .filter(|block| block.label() == X86_64MachineLabel::FunctionAbort(VirFunctionId::new(0)))
        .collect::<Vec<_>>();
    assert_eq!(
        abort_blocks.len(),
        1,
        "one failure block is shared per function"
    );
    assert_eq!(
        abort_blocks[0].instructions(),
        &[
            X86_64MachineInstruction::CallExternal {
                symbol: X86_64ExternalSymbol::Abort,
            },
            X86_64MachineInstruction::Trap,
        ]
    );

    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(resolved.runtime())
            .expect("selection is deterministic"),
        machine
    );
}

#[test]
fn allocator_helper_checks_rounding_and_libc_failures() {
    let validated = memory_program()
        .into_validated()
        .expect("memory VIR is well formed");
    let resolved = validated.resolve().expect("there are no source calls");
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("allocator runtime is selectable");

    assert_eq!(machine.runtime_functions().len(), 1);
    let allocator = machine
        .runtime_helper(X86_64RuntimeHelper::AllocOrAbort)
        .expect("the allocator is emitted on demand");
    assert_eq!(
        allocator.symbol(),
        X86_64MachineSymbol::RuntimeHelper(X86_64RuntimeHelper::AllocOrAbort)
    );
    assert_eq!(allocator.blocks().len(), 2);

    let entry = &allocator.blocks()[0];
    let failure = X86_64MachineLabel::RuntimeFailure(X86_64RuntimeHelper::AllocOrAbort);
    assert_eq!(
        entry.label(),
        X86_64MachineLabel::RuntimeHelper(X86_64RuntimeHelper::AllocOrAbort)
    );
    assert!(entry.instructions().windows(2).any(|window| {
        matches!(
            window,
            [
                X86_64MachineInstruction::Compare64 {
                    left: X86_64IntegerRegister::Rdi,
                    right: X86_64MachineRead::Immediate(0),
                },
                X86_64MachineInstruction::JumpIf {
                    condition: X86_64ConditionCode::Equal,
                    target,
                }
            ] if *target == failure
        )
    }));
    assert!(entry.instructions().windows(2).any(|window| {
        matches!(
            window,
            [
                X86_64MachineInstruction::Compare64 {
                    left: X86_64IntegerRegister::Rsi,
                    right: X86_64MachineRead::Immediate(8),
                },
                X86_64MachineInstruction::JumpIf {
                    condition: X86_64ConditionCode::Below,
                    target,
                }
            ] if *target == failure
        )
    }));
    assert!(
        entry
            .instructions()
            .contains(&X86_64MachineInstruction::Subtract64 {
                destination: X86_64IntegerRegister::R10,
                source: X86_64MachineRead::Immediate(1),
            })
    );
    assert_eq!(
        entry
            .instructions()
            .iter()
            .filter(|instruction| matches!(instruction, X86_64MachineInstruction::And64 { .. }))
            .count(),
        2,
        "one and checks power-of-two and one rounds the size"
    );
    assert!(
        entry
            .instructions()
            .contains(&X86_64MachineInstruction::JumpIf {
                condition: X86_64ConditionCode::Carry,
                target: failure,
            })
    );
    assert!(
        entry
            .instructions()
            .contains(&X86_64MachineInstruction::Negate64 {
                register: X86_64IntegerRegister::R10,
            })
    );
    assert!(
        entry
            .instructions()
            .contains(&X86_64MachineInstruction::CallExternal {
                symbol: X86_64ExternalSymbol::AlignedAlloc,
            })
    );
    assert!(entry.instructions().windows(2).any(|window| {
        matches!(
            window,
            [
                X86_64MachineInstruction::Compare64 {
                    left: X86_64IntegerRegister::Rax,
                    right: X86_64MachineRead::Immediate(0),
                },
                X86_64MachineInstruction::JumpIf {
                    condition: X86_64ConditionCode::Equal,
                    target,
                }
            ] if *target == failure
        )
    }));
    assert_eq!(
        allocator.blocks()[1].instructions(),
        &[
            X86_64MachineInstruction::CallExternal {
                symbol: X86_64ExternalSymbol::Abort,
            },
            X86_64MachineInstruction::Trap,
        ]
    );
}

fn memory_program() -> VirUnit {
    let pointer_type = VirType::Pointer {
        access: nera::VirMemoryAccess::core_u64(),
    };
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "main".to_owned(),
            signature: VirSignature {
                parameters: vec![],
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: vec![],
                instructions: vec![
                    constant_u64(0, 16),
                    instruction(VirInstruction::Allocate {
                        pointer_result: value(1, pointer_type),
                        permission_result: value(2, VirType::Permission),
                        size_bytes: VirValueId::new(0),
                        alignment: 4,
                        region: VirRegionId::new(0),
                        element: nera::VirMemoryAccess::core_u64(),
                    }),
                    constant_u64(3, 40),
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
                    constant_u64(5, 8),
                    instruction(VirInstruction::PointerOffset {
                        result: value(6, pointer_type),
                        base: VirValueId::new(1),
                        delta_bytes: VirValueId::new(5),
                    }),
                    constant_u64(7, 2),
                    instruction(VirInstruction::Write {
                        pointer: VirValueId::new(6),
                        value: VirValueId::new(7),
                        permission: VirValueId::new(2),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Store {
                        pointer: VirValueId::new(6),
                        value: VirValueId::new(7),
                        permission: VirValueId::new(2),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::Load {
                        result: value(8, VirType::U64),
                        pointer: VirValueId::new(6),
                        permission: VirValueId::new(2),
                        access: nera::VirMemoryAccess::core_u64(),
                    }),
                    instruction(VirInstruction::WordAdd {
                        result: value(9, VirType::U64),
                        left: VirValueId::new(4),
                        right: VirValueId::new(8),
                    }),
                    constant_u64(10, 42),
                    instruction(VirInstruction::Compare {
                        result: value(11, VirType::Bool),
                        predicate: VirIntegerPredicate::Equal,
                        left: VirValueId::new(9),
                        right: VirValueId::new(10),
                    }),
                    instruction(VirInstruction::Check {
                        condition: VirValueId::new(11),
                    }),
                    instruction(VirInstruction::Check {
                        condition: VirValueId::new(11),
                    }),
                    instruction(VirInstruction::Free {
                        pointer: VirValueId::new(1),
                        permission: VirValueId::new(2),
                    }),
                ],
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return {
                        values: vec![VirValueId::new(9)],
                    },
                    source_span: span(),
                },
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

fn block(
    function: &nera::backend::X86_64MachineFunction,
    label: X86_64MachineLabel,
) -> &nera::backend::X86_64MachineBlock {
    function
        .blocks()
        .iter()
        .find(|block| block.label() == label)
        .expect("machine block exists")
}

const fn vir_block_label(function: u32, block: u32) -> X86_64MachineLabel {
    X86_64MachineLabel::VirBlock {
        function: VirFunctionId::new(function),
        block: VirBlockId::new(block),
    }
}

fn constant_u64(id: u32, constant: u64) -> SpannedVirInstruction {
    instruction(VirInstruction::Constant {
        result: value(id, VirType::U64),
        value: VirConstant::U64(constant),
    })
}

fn instruction(instruction: VirInstruction) -> SpannedVirInstruction {
    SpannedVirInstruction {
        instruction,
        source_span: span(),
    }
}

const fn value(id: u32, ty: VirType) -> VirValue {
    VirValue {
        id: VirValueId::new(id),
        ty,
    }
}

fn span() -> ByteSpan {
    ByteSpan::new(0, 1).expect("test span is valid")
}
