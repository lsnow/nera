use nera::backend::{
    X86_64_UNKNOWN_LINUX_GNU, X86_64ByteRegister, X86_64CodegenErrorKind, X86_64ConditionCode,
    X86_64MachineInstruction, X86_64MachineLabel, X86_64MachineRead, X86_64MachineSymbol,
    X86_64MachineWrite,
};
use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, VirBasicBlock, VirBlockId,
    VirBlockTarget, VirCallTarget, VirConstant, VirContractId, VirFunction, VirFunctionId,
    VirInstruction, VirIntegerPredicate, VirSignature, VirTerminator, VirType, VirUnit, VirValue,
    VirValueId,
};

#[test]
fn scalar_cfg_lowers_to_explicit_machine_blocks_and_main_wrapper() {
    let validated = scalar_cfg_program()
        .into_validated()
        .expect("test VIR is well formed");
    let resolved = validated.resolve().expect("there are no unresolved calls");
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("the scalar CFG subset is selectable");

    assert_eq!(machine.entry(), VirFunctionId::new(0));
    assert_eq!(machine.functions().len(), 1);
    assert!(machine.runtime_functions().is_empty());
    let function = machine
        .function(VirFunctionId::new(0))
        .expect("internal function exists");
    assert_eq!(
        function.symbol(),
        X86_64MachineSymbol::InternalFunction(VirFunctionId::new(0))
    );
    assert_eq!(function.blocks().len(), 7);
    assert_eq!(
        function.blocks()[0].label(),
        X86_64MachineLabel::InternalFunction(VirFunctionId::new(0))
    );
    assert_eq!(
        function.blocks()[0].instructions(),
        &[
            X86_64MachineInstruction::Push64 {
                register: nera::backend::X86_64IntegerRegister::Rbp,
            },
            X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Register(
                    nera::backend::X86_64IntegerRegister::Rbp,
                ),
                source: X86_64MachineRead::Register(nera::backend::X86_64IntegerRegister::Rsp,),
            },
            X86_64MachineInstruction::SubtractStackPointer { bytes: 64 },
            X86_64MachineInstruction::Jump {
                target: block_label(0, 0),
            },
        ]
    );

    let entry = block(function, block_label(0, 0));
    assert!(entry.instructions().iter().any(|instruction| {
        matches!(
            instruction,
            X86_64MachineInstruction::Add64 {
                destination: nera::backend::X86_64IntegerRegister::R10,
                source: X86_64MachineRead::Memory(_),
            }
        )
    }));
    assert!(entry.instructions().iter().any(|instruction| {
        matches!(
            instruction,
            X86_64MachineInstruction::SetCondition8 {
                condition: X86_64ConditionCode::AboveOrEqual,
                destination: X86_64ByteRegister::R10b,
            }
        )
    }));
    let branch_tail = &entry.instructions()[entry.instructions().len() - 4..];
    assert!(matches!(
        branch_tail,
        [
            X86_64MachineInstruction::Move64 { .. },
            X86_64MachineInstruction::Compare64 {
                right: X86_64MachineRead::Immediate(0),
                ..
            },
            X86_64MachineInstruction::JumpIf {
                condition: X86_64ConditionCode::NotEqual,
                target: X86_64MachineLabel::SyntheticEdge { .. },
            },
            X86_64MachineInstruction::Jump {
                target: X86_64MachineLabel::SyntheticEdge { .. },
            },
        ]
    ));

    let edge_blocks = function
        .blocks()
        .iter()
        .filter(|block| matches!(block.label(), X86_64MachineLabel::SyntheticEdge { .. }))
        .collect::<Vec<_>>();
    assert_eq!(edge_blocks.len(), 2);
    for edge in edge_blocks {
        assert_eq!(edge.instructions().len(), 5);
        assert!(matches!(
            edge.instructions().last(),
            Some(X86_64MachineInstruction::Jump {
                target: X86_64MachineLabel::VirBlock { .. }
            })
        ));
    }

    let then_return = block(function, block_label(0, 1));
    assert!(matches!(
        then_return.instructions(),
        [
            X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Register(
                    nera::backend::X86_64IntegerRegister::Rax
                ),
                source: X86_64MachineRead::Memory(_),
            },
            X86_64MachineInstruction::Jump {
                target: X86_64MachineLabel::FunctionEpilogue(_)
            },
        ]
    ));
    assert_eq!(
        function
            .blocks()
            .last()
            .expect("epilogue exists")
            .instructions(),
        &[
            X86_64MachineInstruction::Leave,
            X86_64MachineInstruction::Return,
        ]
    );

    let wrapper = machine.executable_entry();
    assert_eq!(wrapper.symbol(), X86_64MachineSymbol::ExecutableEntry);
    assert_eq!(wrapper.blocks().len(), 1);
    assert_eq!(
        wrapper.blocks()[0].instructions(),
        &[
            X86_64MachineInstruction::Push64 {
                register: nera::backend::X86_64IntegerRegister::Rbp,
            },
            X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Register(
                    nera::backend::X86_64IntegerRegister::Rbp,
                ),
                source: X86_64MachineRead::Register(nera::backend::X86_64IntegerRegister::Rsp,),
            },
            X86_64MachineInstruction::CallInternal {
                function: VirFunctionId::new(0),
            },
            X86_64MachineInstruction::Leave,
            X86_64MachineInstruction::Return,
        ]
    );

    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU
            .codegen_program(resolved.runtime())
            .expect("selection is deterministic"),
        machine
    );
    assert_legal_operand_shapes(&machine);
}

#[test]
fn local_call_materializes_stack_arguments_and_indirect_results() {
    let validated = multi_result_call_program()
        .into_validated()
        .expect("test VIR is well formed");
    let resolved = validated.resolve().expect("the local call resolves");
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("scalar local calls are selectable");

    let caller = machine
        .function(VirFunctionId::new(0))
        .expect("caller exists");
    let caller_block = block(caller, block_label(0, 0));
    let call_index = caller_block
        .instructions()
        .iter()
        .position(|instruction| {
            *instruction
                == X86_64MachineInstruction::CallInternal {
                    function: VirFunctionId::new(1),
                }
        })
        .expect("resolved local call was selected");
    assert!(
        caller_block.instructions()[..call_index]
            .iter()
            .any(|instruction| {
                matches!(
                    instruction,
                    X86_64MachineInstruction::SubtractStackPointer { bytes: 16 }
                )
            })
    );
    assert!(
        caller_block.instructions()[..call_index]
            .iter()
            .any(|instruction| {
                matches!(
                    instruction,
                    X86_64MachineInstruction::LoadEffectiveAddress64 {
                        destination: nera::backend::X86_64IntegerRegister::Rdi,
                        source,
                    } if source.base() == nera::backend::X86_64IntegerRegister::Rbp
                )
            })
    );
    let stack_stores = caller_block.instructions()[..call_index]
        .iter()
        .filter_map(|instruction| match instruction {
            X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Memory(memory),
                source: X86_64MachineRead::Register(nera::backend::X86_64IntegerRegister::R10),
            } if memory.base() == nera::backend::X86_64IntegerRegister::Rsp => {
                Some(memory.displacement())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(stack_stores, vec![0, 8]);
    assert_eq!(
        caller_block.instructions()[call_index + 1],
        X86_64MachineInstruction::AddStackPointer { bytes: 16 }
    );
    let result_area_loads =
        caller_block.instructions()[call_index + 2..]
            .iter()
            .filter_map(|instruction| match instruction {
                X86_64MachineInstruction::Move64 {
                    destination:
                        X86_64MachineWrite::Register(nera::backend::X86_64IntegerRegister::R10),
                    source: X86_64MachineRead::Memory(memory),
                } if memory.base() == nera::backend::X86_64IntegerRegister::Rbp => {
                    Some(memory.displacement())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
    assert_eq!(result_area_loads.len(), 2);
    assert_eq!(result_area_loads[1] - result_area_loads[0], 8);

    let callee = machine
        .function(VirFunctionId::new(1))
        .expect("callee exists");
    let callee_prologue = &callee.blocks()[0];
    assert!(callee_prologue.instructions().iter().any(|instruction| {
        matches!(
            instruction,
            X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Memory(_),
                source: X86_64MachineRead::Register(nera::backend::X86_64IntegerRegister::Rdi,),
            }
        )
    }));
    let incoming_stack_loads =
        callee_prologue
            .instructions()
            .iter()
            .filter_map(|instruction| match instruction {
                X86_64MachineInstruction::Move64 {
                    destination:
                        X86_64MachineWrite::Register(nera::backend::X86_64IntegerRegister::R10),
                    source: X86_64MachineRead::Memory(memory),
                } if memory.base() == nera::backend::X86_64IntegerRegister::Rbp
                    && memory.displacement() > 0 =>
                {
                    Some(memory.displacement())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
    assert_eq!(incoming_stack_loads, vec![16, 24]);

    let callee_body = block(callee, block_label(1, 0));
    assert!(matches!(
        callee_body.instructions().first(),
        Some(X86_64MachineInstruction::Move64 {
            destination: X86_64MachineWrite::Register(nera::backend::X86_64IntegerRegister::R10),
            source: X86_64MachineRead::Immediate(1),
        })
    ));
    assert!(callee_body.instructions().iter().any(|instruction| {
        matches!(
            instruction,
            X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Register(
                    nera::backend::X86_64IntegerRegister::R11,
                ),
                source: X86_64MachineRead::Memory(_),
            }
        )
    }));
    let result_stores = callee_body
        .instructions()
        .iter()
        .filter_map(|instruction| match instruction {
            X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Memory(memory),
                source: X86_64MachineRead::Register(nera::backend::X86_64IntegerRegister::R10),
            } if memory.base() == nera::backend::X86_64IntegerRegister::R11 => {
                Some(memory.displacement())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(result_stores, vec![0, 8]);
    assert_legal_operand_shapes(&machine);
}

#[test]
fn recursive_calls_and_permission_only_calls_remain_structural() {
    let validated = recursive_and_ghost_program()
        .into_validated()
        .expect("test VIR is well formed");
    let resolved = validated.resolve().expect("all calls resolve");
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("unit and ghost-only calls are selectable");

    let recursive = machine
        .function(VirFunctionId::new(1))
        .expect("recursive function exists");
    assert!(block(recursive, block_label(1, 0)).instructions().contains(
        &X86_64MachineInstruction::CallInternal {
            function: VirFunctionId::new(1),
        }
    ));

    let ghost_caller = machine
        .function(VirFunctionId::new(2))
        .expect("ghost caller exists");
    assert_eq!(
        block(ghost_caller, block_label(2, 0)).instructions(),
        &[
            X86_64MachineInstruction::CallInternal {
                function: VirFunctionId::new(3),
            },
            X86_64MachineInstruction::Jump {
                target: X86_64MachineLabel::FunctionEpilogue(VirFunctionId::new(2)),
            },
        ]
    );
    assert_eq!(
        ghost_caller
            .blocks()
            .first()
            .expect("prologue exists")
            .instructions()
            .iter()
            .filter(|instruction| matches!(instruction, X86_64MachineInstruction::Move64 { .. }))
            .count(),
        1,
        "only mov rbp, rsp remains; permission parameters have no spill"
    );

    assert!(
        machine.executable_entry().blocks()[0]
            .instructions()
            .contains(&X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Register(
                    nera::backend::X86_64IntegerRegister::Rax,
                ),
                source: X86_64MachineRead::Immediate(0),
            })
    );
}

#[test]
fn every_integer_predicate_uses_the_unsigned_x86_condition() {
    let validated = predicate_program()
        .into_validated()
        .expect("test VIR is well formed");
    let resolved = validated.resolve().expect("there are no calls");
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("all VIR predicates are selectable");
    let body = block(
        machine
            .function(VirFunctionId::new(0))
            .expect("function exists"),
        block_label(0, 0),
    );
    let conditions = body
        .instructions()
        .iter()
        .filter_map(|instruction| match instruction {
            X86_64MachineInstruction::SetCondition8 { condition, .. } => Some(*condition),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        conditions,
        vec![
            X86_64ConditionCode::Equal,
            X86_64ConditionCode::NotEqual,
            X86_64ConditionCode::Below,
            X86_64ConditionCode::BelowOrEqual,
            X86_64ConditionCode::Above,
            X86_64ConditionCode::AboveOrEqual,
        ]
    );
    assert!(
        machine.executable_entry().blocks()[0]
            .instructions()
            .contains(&X86_64MachineInstruction::CallInternal {
                function: VirFunctionId::new(0),
            })
    );
    assert!(
        !machine.executable_entry().blocks()[0]
            .instructions()
            .iter()
            .any(|instruction| matches!(
                instruction,
                X86_64MachineInstruction::Move64 {
                    destination: X86_64MachineWrite::Register(
                        nera::backend::X86_64IntegerRegister::Rax
                    ),
                    source: X86_64MachineRead::Immediate(_),
                }
            )),
        "a bool entry must preserve its normalized rax result"
    );
}

#[test]
fn invalid_entry_fails_closed() {
    let validated = invalid_entry_program()
        .into_validated()
        .expect("test VIR is well formed");
    let resolved = validated.resolve().expect("there are no calls");
    let error = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect_err("native executable entries cannot receive parameters");
    assert!(matches!(error.kind(), X86_64CodegenErrorKind::EntryAbi(_)));
    assert_eq!(error.function(), Some(VirFunctionId::new(0)));
    assert_eq!(error.block(), None);
}

fn scalar_cfg_program() -> VirUnit {
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
            blocks: vec![
                VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![],
                    instructions: vec![
                        constant_u64(0, 40),
                        constant_u64(1, 2),
                        instruction(VirInstruction::WordAdd {
                            result: value(2, VirType::U64),
                            left: VirValueId::new(0),
                            right: VirValueId::new(1),
                        }),
                        constant_u64(3, 42),
                        instruction(VirInstruction::Compare {
                            result: value(4, VirType::Bool),
                            predicate: VirIntegerPredicate::GreaterOrEqual,
                            left: VirValueId::new(2),
                            right: VirValueId::new(3),
                        }),
                    ],
                    terminator: terminator(VirTerminator::Branch {
                        condition: VirValueId::new(4),
                        then_target: target(1, &[2]),
                        else_target: target(2, &[0]),
                    }),
                    source_span: span(),
                },
                return_block(1, 10),
                return_block(2, 20),
            ],
            source_span: span(),
        }],
    )
}

fn multi_result_call_program() -> VirUnit {
    let callee_signature = VirSignature {
        parameters: vec![VirType::U64; 7],
        results: vec![VirType::U64, VirType::Bool],
    };
    let mut instructions = (0..7)
        .map(|id| constant_u64(id, u64::from(id)))
        .collect::<Vec<_>>();
    instructions.push(instruction(VirInstruction::Call {
        results: vec![value(20, VirType::U64), value(21, VirType::Bool)],
        target: VirCallTarget {
            symbol: "callee".to_owned(),
            signature: callee_signature.clone(),
            contract: VirContractId::new(1),
            abi: None,
        },
        arguments: (0..7).map(VirValueId::new).collect(),
    }));
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![
            VirFunction {
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
                    instructions,
                    terminator: terminator(VirTerminator::Return {
                        values: vec![VirValueId::new(20)],
                    }),
                    source_span: span(),
                }],
                source_span: span(),
            },
            VirFunction {
                id: VirFunctionId::new(1),
                name: "callee".to_owned(),
                signature: callee_signature,
                contract: VirContractId::new(1),
                entry: VirBlockId::new(0),
                blocks: vec![VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: (0..7).map(|id| value(id, VirType::U64)).collect(),
                    instructions: vec![instruction(VirInstruction::Constant {
                        result: value(7, VirType::Bool),
                        value: VirConstant::Bool(true),
                    })],
                    terminator: terminator(VirTerminator::Return {
                        values: vec![VirValueId::new(0), VirValueId::new(7)],
                    }),
                    source_span: span(),
                }],
                source_span: span(),
            },
        ],
    )
}

fn recursive_and_ghost_program() -> VirUnit {
    let unit = VirSignature {
        parameters: vec![],
        results: vec![],
    };
    let permission = VirSignature {
        parameters: vec![VirType::Permission],
        results: vec![VirType::Permission],
    };
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![
            call_only_function(
                0,
                "main",
                unit.clone(),
                1,
                "recurse",
                unit.clone(),
                vec![],
                vec![],
            ),
            call_only_function(
                1,
                "recurse",
                unit.clone(),
                1,
                "recurse",
                unit,
                vec![],
                vec![],
            ),
            VirFunction {
                id: VirFunctionId::new(2),
                name: "ghost_caller".to_owned(),
                signature: permission.clone(),
                contract: VirContractId::new(2),
                entry: VirBlockId::new(0),
                blocks: vec![VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![value(0, VirType::Permission)],
                    instructions: vec![
                        instruction(VirInstruction::PermissionMove {
                            result: value(1, VirType::Permission),
                            source: VirValueId::new(0),
                        }),
                        instruction(VirInstruction::Call {
                            results: vec![value(2, VirType::Permission)],
                            target: VirCallTarget {
                                symbol: "ghost_pass".to_owned(),
                                signature: permission.clone(),
                                contract: VirContractId::new(3),
                                abi: None,
                            },
                            arguments: vec![VirValueId::new(1)],
                        }),
                    ],
                    terminator: terminator(VirTerminator::Return {
                        values: vec![VirValueId::new(2)],
                    }),
                    source_span: span(),
                }],
                source_span: span(),
            },
            VirFunction {
                id: VirFunctionId::new(3),
                name: "ghost_pass".to_owned(),
                signature: permission,
                contract: VirContractId::new(3),
                entry: VirBlockId::new(0),
                blocks: vec![VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![value(0, VirType::Permission)],
                    instructions: vec![],
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

fn predicate_program() -> VirUnit {
    let predicates = [
        VirIntegerPredicate::Equal,
        VirIntegerPredicate::NotEqual,
        VirIntegerPredicate::LessThan,
        VirIntegerPredicate::LessOrEqual,
        VirIntegerPredicate::GreaterThan,
        VirIntegerPredicate::GreaterOrEqual,
    ];
    let mut instructions = vec![constant_u64(0, 1), constant_u64(1, 2)];
    for (index, predicate) in predicates.into_iter().enumerate() {
        instructions.push(instruction(VirInstruction::Compare {
            result: value(
                u32::try_from(index + 2).expect("test id fits"),
                VirType::Bool,
            ),
            predicate,
            left: VirValueId::new(0),
            right: VirValueId::new(1),
        }));
    }
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "predicates".to_owned(),
            signature: VirSignature {
                parameters: vec![],
                results: vec![VirType::Bool],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: vec![],
                instructions,
                terminator: terminator(VirTerminator::Return {
                    values: vec![VirValueId::new(7)],
                }),
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

fn invalid_entry_program() -> VirUnit {
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "invalid_entry".to_owned(),
            signature: VirSignature {
                parameters: vec![VirType::U64],
                results: vec![],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: vec![value(0, VirType::U64)],
                instructions: vec![],
                terminator: terminator(VirTerminator::Return { values: vec![] }),
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

#[allow(clippy::too_many_arguments)]
fn call_only_function(
    id: u32,
    name: &str,
    signature: VirSignature,
    callee_id: u32,
    callee_name: &str,
    callee_signature: VirSignature,
    arguments: Vec<VirValueId>,
    results: Vec<VirValue>,
) -> VirFunction {
    VirFunction {
        id: VirFunctionId::new(id),
        name: name.to_owned(),
        signature,
        contract: VirContractId::new(id),
        entry: VirBlockId::new(0),
        blocks: vec![VirBasicBlock {
            id: VirBlockId::new(0),
            parameters: vec![],
            instructions: vec![instruction(VirInstruction::Call {
                results,
                target: VirCallTarget {
                    symbol: callee_name.to_owned(),
                    signature: callee_signature,
                    contract: VirContractId::new(callee_id),
                    abi: None,
                },
                arguments,
            })],
            terminator: terminator(VirTerminator::Return { values: vec![] }),
            source_span: span(),
        }],
        source_span: span(),
    }
}

fn return_block(block: u32, value_id: u32) -> VirBasicBlock {
    VirBasicBlock {
        id: VirBlockId::new(block),
        parameters: vec![value(value_id, VirType::U64)],
        instructions: vec![],
        terminator: terminator(VirTerminator::Return {
            values: vec![VirValueId::new(value_id)],
        }),
        source_span: span(),
    }
}

fn constant_u64(id: u32, word: u64) -> SpannedVirInstruction {
    instruction(VirInstruction::Constant {
        result: value(id, VirType::U64),
        value: VirConstant::U64(word),
    })
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

fn block_label(function: u32, block: u32) -> X86_64MachineLabel {
    X86_64MachineLabel::VirBlock {
        function: VirFunctionId::new(function),
        block: VirBlockId::new(block),
    }
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

fn assert_legal_operand_shapes(machine: &nera::backend::X86_64MachineProgram) {
    for function in machine
        .functions()
        .iter()
        .chain(machine.runtime_functions())
        .chain(std::iter::once(machine.executable_entry()))
    {
        for instruction in function
            .blocks()
            .iter()
            .flat_map(|block| block.instructions())
        {
            if let X86_64MachineInstruction::Move64 {
                destination: X86_64MachineWrite::Memory(_),
                source,
            } = instruction
            {
                assert!(
                    matches!(source, X86_64MachineRead::Register(_)),
                    "x86_64 cannot encode this move directly: {instruction:?}"
                );
            }
        }
    }
}

fn span() -> ByteSpan {
    ByteSpan::new(0, 100).expect("valid test span")
}
