use nera::backend::{
    X86_64_UNKNOWN_LINUX_GNU, X86_64AbiParameterLocation, X86_64AbiResultLocation, X86_64BranchArm,
    X86_64CallerStackLocation, X86_64EdgeCopyPlacement, X86_64InstructionPlan,
    X86_64IntegerRegister, X86_64RuntimeType, X86_64TerminatorPlan,
};
use nera::{
    ByteSpan, SpannedVirInstruction, SpannedVirTerminator, VirBasicBlock, VirBlockId,
    VirBlockTarget, VirCallTarget, VirConstant, VirContractId, VirFunction, VirFunctionId,
    VirInstruction, VirSignature, VirTerminator, VirType, VirUnit, VirValue, VirValueId,
};

#[test]
fn frame_plan_erases_permissions_and_materializes_resolved_call_abi() {
    let validated = call_program()
        .into_validated()
        .expect("test VIR is well formed");
    let resolved = validated.resolve().expect("test calls resolve");
    let VirInstruction::Call { target, .. } =
        &resolved.runtime().functions[0].blocks[0].instructions[8].instruction
    else {
        panic!("the test call is present");
    };
    assert_eq!(
        resolved.runtime().call_target_id(target),
        Some(VirFunctionId::new(1))
    );
    let mut mismatched_summary = target.clone();
    mismatched_summary.contract = VirContractId::new(99);
    assert_eq!(resolved.runtime().call_target_id(&mismatched_summary), None);
    let plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("small scalar program is plannable");

    assert_eq!(plan.entry(), VirFunctionId::new(0));
    assert_eq!(plan.functions().len(), 2);
    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU.maximum_frame_size_bytes(),
        2_147_483_632
    );
    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU.maximum_outgoing_stack_size_bytes(),
        2_147_483_632
    );

    let caller = plan
        .function(VirFunctionId::new(0))
        .expect("caller plan exists");
    assert_eq!(caller.symbol(), ".Lnera_v0_fn_0");
    assert!(caller.incoming_parameters().is_empty());
    assert_eq!(caller.frame().value_slots().len(), 9);
    assert_eq!(caller.frame().value_slot(VirValueId::new(100)), None);
    assert_eq!(caller.frame().value_slot(VirValueId::new(7)), None);
    assert_eq!(caller.frame().value_slot(VirValueId::new(21)), None);
    assert_eq!(
        caller
            .frame()
            .hidden_result_buffer_pointer()
            .expect("multiple function results require an incoming pointer")
            .offset_from_rbp_bytes(),
        -8
    );
    assert_eq!(caller.frame().used_bytes(), 96);
    assert_eq!(caller.frame().size_bytes(), 96);
    assert!(caller.frame().parallel_copy_temporaries().is_empty());
    let result_area = caller
        .frame()
        .indirect_call_result_area()
        .expect("the multi-result call needs local result storage");
    assert_eq!(result_area.base_offset_from_rbp_bytes(), -96);
    assert_eq!(result_area.size_bytes(), 16);
    assert_eq!(result_area.alignment_bytes(), 8);
    assert_eq!(caller.maximum_outgoing_stack_size_bytes(), 16);

    let block = caller
        .block(VirBlockId::new(0))
        .expect("caller block exists");
    assert_eq!(block.instructions().len(), 9);
    assert_eq!(
        block.instructions()[7],
        X86_64InstructionPlan::ErasedPermission
    );
    let X86_64InstructionPlan::Call(call) = &block.instructions()[8] else {
        panic!("the final instruction must retain a resolved call plan");
    };
    assert_eq!(call.callee(), VirFunctionId::new(1));
    assert_eq!(call.arguments().len(), 7);
    assert_eq!(call.results().len(), 2);
    assert_eq!(call.indirect_result_area(), Some(result_area));
    assert_eq!(call.signature().stack_parameter_count(), 2);
    assert_eq!(call.signature().outgoing_stack_size_bytes(), 16);
    assert_eq!(
        call.arguments()
            .iter()
            .map(|argument| (argument.vir_index(), argument.value(), argument.location()))
            .collect::<Vec<_>>(),
        vec![
            (
                0,
                VirValueId::new(0),
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rsi),
            ),
            (
                1,
                VirValueId::new(1),
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rdx),
            ),
            (
                2,
                VirValueId::new(2),
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rcx),
            ),
            (
                3,
                VirValueId::new(3),
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::R8),
            ),
            (
                4,
                VirValueId::new(4),
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::R9),
            ),
            (
                5,
                VirValueId::new(5),
                X86_64AbiParameterLocation::CallerStack(X86_64CallerStackLocation::from_slot(0),),
            ),
            (
                6,
                VirValueId::new(6),
                X86_64AbiParameterLocation::CallerStack(X86_64CallerStackLocation::from_slot(1),),
            ),
        ]
    );
    assert_eq!(call.results()[0].vir_index(), 0);
    assert_eq!(call.results()[0].value(), VirValueId::new(20));
    assert_eq!(call.results()[0].ty(), X86_64RuntimeType::U64);
    assert_eq!(
        call.results()[0].location(),
        X86_64AbiResultLocation::ResultBuffer { offset_bytes: 0 }
    );
    assert_eq!(call.results()[1].vir_index(), 2);
    assert_eq!(call.results()[1].value(), VirValueId::new(22));
    assert_eq!(call.results()[1].ty(), X86_64RuntimeType::Bool);
    assert_eq!(
        call.results()[1].location(),
        X86_64AbiResultLocation::ResultBuffer { offset_bytes: 8 }
    );
    assert_eq!(
        call.results()[0].destination(),
        caller
            .frame()
            .value_slot(VirValueId::new(20))
            .expect("runtime call result has a slot")
    );

    let X86_64TerminatorPlan::Return { values } = block.terminator() else {
        panic!("caller returns its call results");
    };
    assert_eq!(values.len(), 2);
    assert_eq!(values[0].vir_index(), 0);
    assert_eq!(values[0].value(), VirValueId::new(20));
    assert_eq!(
        values[0].destination(),
        X86_64AbiResultLocation::ResultBuffer { offset_bytes: 0 }
    );
    assert_eq!(values[1].vir_index(), 2);
    assert_eq!(values[1].value(), VirValueId::new(22));

    let callee = plan
        .function(VirFunctionId::new(1))
        .expect("callee plan exists");
    assert_eq!(callee.incoming_parameters().len(), 7);
    assert_eq!(callee.frame().used_bytes(), 72);
    assert_eq!(callee.frame().size_bytes(), 80);
    assert_eq!(
        callee.incoming_parameters()[0].source(),
        X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rsi)
    );
    assert_eq!(
        callee.incoming_parameters()[5].source(),
        X86_64AbiParameterLocation::CallerStack(X86_64CallerStackLocation::from_slot(0))
    );
    assert_eq!(
        callee.incoming_parameters()[6].source(),
        X86_64AbiParameterLocation::CallerStack(X86_64CallerStackLocation::from_slot(1))
    );
    assert_eq!(
        callee.incoming_parameters()[6]
            .source()
            .caller_stack()
            .expect("the seventh runtime parameter is on the stack")
            .offset_from_callee_frame_pointer_bytes(),
        24
    );

    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU
            .plan_program(resolved.runtime())
            .expect("planning is deterministic"),
        plan
    );
}

#[test]
fn resource_heap_plan_requires_one_exact_object_and_canonical_empty_slots() {
    let output = nera::analyze(&nera::SourceFile::from_text(
        "heap-plan.nera",
        "enum Item { Full(Own<u64>, u64), Empty, } fn main() -> u64 { let p = alloc<Item>(1); free(p); return 42; }",
    ));
    let unit = output.vir().unwrap();
    let resolved = unit.resolve().unwrap();
    let plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .unwrap();
    let storage = plan.functions()[0].blocks()[0]
        .instructions()
        .iter()
        .find(|step| matches!(step, X86_64InstructionPlan::HeapStorage { .. }))
        .unwrap();
    let X86_64InstructionPlan::HeapStorage {
        empty_resource_offsets,
        cleanup_tag: Some(tag),
    } = storage
    else {
        panic!("root enum has a physical cleanup tag");
    };
    assert_eq!(empty_resource_offsets, &[8]);
    assert_eq!(tag.discriminant(), 0);

    let mut unit = unit.as_unit().clone();
    let size_id = unit.runtime.functions[0].blocks[0]
        .instructions
        .iter()
        .find_map(|item| match item.instruction {
            VirInstruction::Allocate { size_bytes, .. } => Some(size_bytes),
            _ => None,
        })
        .unwrap();
    for item in &mut unit.runtime.functions[0].blocks[0].instructions {
        if let VirInstruction::Constant {
            result,
            value: VirConstant::U64(value),
        } = &mut item.instruction
            && result.id == size_id
        {
            *value *= 2;
        }
    }
    let unit = unit.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let error = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .unwrap_err();
    assert!(matches!(
        error.kind(),
        nera::backend::X86_64PlanningErrorKind::UnsupportedObjectEffectType { .. }
    ));
}

#[test]
fn parallel_copy_uses_shared_temporaries_and_splits_only_branch_edges() {
    let validated = cyclic_edge_program()
        .into_validated()
        .expect("test VIR is well formed");
    let resolved = validated.resolve().expect("there are no unresolved calls");
    let plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("cyclic block arguments are plannable");
    let function = plan
        .function(VirFunctionId::new(0))
        .expect("function plan exists");

    assert_eq!(function.frame().value_slots().len(), 5);
    assert_eq!(function.frame().used_bytes(), 56);
    assert_eq!(function.frame().size_bytes(), 64);
    assert_eq!(function.frame().parallel_copy_temporaries().len(), 2);
    assert_eq!(
        function.frame().parallel_copy_temporaries()[0].offset_from_rbp_bytes(),
        -48
    );
    assert_eq!(
        function.frame().parallel_copy_temporaries()[1].offset_from_rbp_bytes(),
        -56
    );

    let entry = function
        .block(VirBlockId::new(0))
        .expect("entry plan exists");
    let X86_64TerminatorPlan::Branch {
        then_edge,
        else_edge,
    } = entry.terminator()
    else {
        panic!("entry terminator is a branch");
    };
    let X86_64EdgeCopyPlacement::SplitBlock(then_split) = then_edge.placement() else {
        panic!("the cyclic branch edge must be split");
    };
    assert_eq!(then_split.predecessor(), VirBlockId::new(0));
    assert_eq!(then_split.arm(), X86_64BranchArm::Then);
    assert_eq!(then_edge.target(), VirBlockId::new(0));
    assert_eq!(then_edge.copies().len(), 2);
    assert_eq!(then_edge.copies()[0].source_value(), VirValueId::new(1));
    assert_eq!(
        then_edge.copies()[0].destination_value(),
        VirValueId::new(0)
    );
    assert_eq!(then_edge.copies()[1].source_value(), VirValueId::new(0));
    assert_eq!(
        then_edge.copies()[1].destination_value(),
        VirValueId::new(1)
    );
    assert_eq!(
        then_edge.copies()[0].temporary(),
        function.frame().parallel_copy_temporaries()[0]
    );
    assert_eq!(
        then_edge.copies()[1].temporary(),
        function.frame().parallel_copy_temporaries()[1]
    );
    assert_eq!(
        then_edge.copies()[0].source(),
        function
            .frame()
            .value_slot(VirValueId::new(1))
            .expect("source slot exists")
    );
    assert_eq!(
        then_edge.copies()[0].destination(),
        function
            .frame()
            .value_slot(VirValueId::new(0))
            .expect("destination slot exists")
    );

    let X86_64EdgeCopyPlacement::SplitBlock(else_split) = else_edge.placement() else {
        panic!("a branch edge with a transfer must be split");
    };
    assert_eq!(else_split.arm(), X86_64BranchArm::Else);
    assert_eq!(else_edge.copies().len(), 1);
    assert_eq!(
        else_edge.copies()[0].temporary(),
        then_edge.copies()[0].temporary()
    );

    let middle = function
        .block(VirBlockId::new(1))
        .expect("middle block plan exists");
    let X86_64TerminatorPlan::Jump { edge } = middle.terminator() else {
        panic!("middle terminator is a jump");
    };
    assert_eq!(edge.placement(), X86_64EdgeCopyPlacement::InlineBeforeJump);
    assert_eq!(edge.copies().len(), 1);
    assert_eq!(
        edge.copies()[0].temporary(),
        then_edge.copies()[0].temporary()
    );
}

#[test]
fn permission_only_noop_edge_has_no_frame_or_synthetic_block() {
    let validated = permission_only_loop()
        .into_validated()
        .expect("test VIR is well formed");
    let resolved = validated.resolve().expect("there are no calls");
    let plan = X86_64_UNKNOWN_LINUX_GNU
        .plan_program(resolved.runtime())
        .expect("permission-only flow erases completely");
    let function = plan.functions().first().expect("function plan exists");

    assert_eq!(function.frame().used_bytes(), 0);
    assert_eq!(function.frame().size_bytes(), 0);
    assert!(function.frame().value_slots().is_empty());
    assert!(function.incoming_parameters().is_empty());
    let X86_64TerminatorPlan::Jump { edge } = function.blocks()[0].terminator() else {
        panic!("loop terminator is a jump");
    };
    assert_eq!(edge.placement(), X86_64EdgeCopyPlacement::Direct);
    assert!(edge.copies().is_empty());
}

fn call_program() -> VirUnit {
    let call_signature = VirSignature {
        parameters: vec![
            VirType::U64,
            VirType::U64,
            VirType::U64,
            VirType::U64,
            VirType::U64,
            VirType::U64,
            VirType::U64,
            VirType::Permission,
        ],
        results: vec![VirType::U64, VirType::Permission, VirType::Bool],
    };
    let mut caller_instructions = (0..7)
        .map(|id| {
            instruction(VirInstruction::Constant {
                result: value(id, VirType::U64),
                value: VirConstant::U64(u64::from(id)),
            })
        })
        .collect::<Vec<_>>();
    caller_instructions.push(instruction(VirInstruction::PermissionMove {
        result: value(7, VirType::Permission),
        source: VirValueId::new(100),
    }));
    caller_instructions.push(instruction(VirInstruction::Call {
        results: vec![
            value(20, VirType::U64),
            value(21, VirType::Permission),
            value(22, VirType::Bool),
        ],
        target: VirCallTarget {
            symbol: "callee".to_owned(),
            signature: call_signature.clone(),
            contract: VirContractId::new(1),
            abi: None,
        },
        arguments: (0..=7).map(VirValueId::new).collect(),
    }));

    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![
            VirFunction {
                id: VirFunctionId::new(0),
                name: "caller".to_owned(),
                signature: VirSignature {
                    parameters: vec![VirType::Permission],
                    results: call_signature.results.clone(),
                },
                contract: VirContractId::new(0),
                entry: VirBlockId::new(0),
                blocks: vec![VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![value(100, VirType::Permission)],
                    instructions: caller_instructions,
                    terminator: terminator(VirTerminator::Return {
                        values: vec![
                            VirValueId::new(20),
                            VirValueId::new(21),
                            VirValueId::new(22),
                        ],
                    }),
                    source_span: span(),
                }],
                source_span: span(),
            },
            VirFunction {
                id: VirFunctionId::new(1),
                name: "callee".to_owned(),
                signature: call_signature,
                contract: VirContractId::new(1),
                entry: VirBlockId::new(0),
                blocks: vec![VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![
                        value(0, VirType::U64),
                        value(1, VirType::U64),
                        value(2, VirType::U64),
                        value(3, VirType::U64),
                        value(4, VirType::U64),
                        value(5, VirType::U64),
                        value(6, VirType::U64),
                        value(7, VirType::Permission),
                    ],
                    instructions: vec![instruction(VirInstruction::Constant {
                        result: value(8, VirType::Bool),
                        value: VirConstant::Bool(true),
                    })],
                    terminator: terminator(VirTerminator::Return {
                        values: vec![VirValueId::new(0), VirValueId::new(7), VirValueId::new(8)],
                    }),
                    source_span: span(),
                }],
                source_span: span(),
            },
        ],
    )
}

fn cyclic_edge_program() -> VirUnit {
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "edges".to_owned(),
            signature: VirSignature {
                parameters: vec![
                    VirType::U64,
                    VirType::U64,
                    VirType::Bool,
                    VirType::Permission,
                ],
                results: vec![VirType::U64, VirType::Permission],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![
                VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![
                        value(0, VirType::U64),
                        value(1, VirType::U64),
                        value(2, VirType::Bool),
                        value(3, VirType::Permission),
                    ],
                    instructions: vec![],
                    terminator: terminator(VirTerminator::Branch {
                        condition: VirValueId::new(2),
                        then_target: target(0, &[1, 0, 2, 3]),
                        else_target: target(1, &[0, 3]),
                    }),
                    source_span: span(),
                },
                VirBasicBlock {
                    id: VirBlockId::new(1),
                    parameters: vec![value(10, VirType::U64), value(11, VirType::Permission)],
                    instructions: vec![],
                    terminator: terminator(VirTerminator::Jump {
                        target: target(2, &[10, 11]),
                    }),
                    source_span: span(),
                },
                VirBasicBlock {
                    id: VirBlockId::new(2),
                    parameters: vec![value(20, VirType::U64), value(21, VirType::Permission)],
                    instructions: vec![],
                    terminator: terminator(VirTerminator::Return {
                        values: vec![VirValueId::new(20), VirValueId::new(21)],
                    }),
                    source_span: span(),
                },
            ],
            source_span: span(),
        }],
    )
}

fn permission_only_loop() -> VirUnit {
    VirUnit::from_runtime(
        nera::VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "ghost_loop".to_owned(),
            signature: VirSignature {
                parameters: vec![VirType::Permission],
                results: vec![VirType::Permission],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: vec![value(0, VirType::Permission)],
                instructions: vec![],
                terminator: terminator(VirTerminator::Jump {
                    target: target(0, &[0]),
                }),
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
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

trait CallerStackLocationExt {
    fn caller_stack(self) -> Option<X86_64CallerStackLocation>;
}

impl CallerStackLocationExt for X86_64AbiParameterLocation {
    fn caller_stack(self) -> Option<X86_64CallerStackLocation> {
        match self {
            X86_64AbiParameterLocation::CallerStack(location) => Some(location),
            X86_64AbiParameterLocation::Register(_) => None,
        }
    }
}
