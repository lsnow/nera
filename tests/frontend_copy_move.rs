use nera::{
    CfgAnalysisConfig, FrontendOutput, FrontendStatus, HirExpressionKind, HirPatternKind,
    HirProgram, HirProgramTables, HirStatementKind, HirUseMode, ObligationStatus,
    ResourceObligationKind, SourceFile, SpannedVirInstruction, VerifierDiagnosticKind,
    VirInstruction, VirMemoryTypeKind, VirObjectSourceMode, VirRuntimeValue, VirType, VirValue,
    VirValueId, analyze, analyze_function_cfg, interpret, verify_program,
};

fn accepted(name: &str, source: &str) -> FrontendOutput {
    let output = analyze(&SourceFile::from_text(name, source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{name}: {:?}",
        output.issues()
    );
    output
}

fn clone_tables(program: &HirProgram) -> HirProgramTables {
    HirProgramTables {
        data_layout: program.data_layout(),
        entry_module: program.entry_module_id(),
        entry_function: program.entry_function_id(),
        modules: program.modules().to_vec(),
        types: program.types().to_vec(),
        type_capabilities: program.type_capability_table().to_vec(),
        layouts: program.layouts().to_vec(),
        fields: program.fields().to_vec(),
        variants: program.variants().to_vec(),
        generic_parameters: program.generic_parameters().to_vec(),
        regions: program.regions().to_vec(),
        region_constraints: program.region_constraints().to_vec(),
        functions: program.functions().to_vec(),
        contracts: program.contracts().to_vec(),
        predicates: program.predicates().to_vec(),
        specs: program.specs().clone(),
    }
}

#[test]
fn source_copy_move_is_explicit_and_reaches_all_runtime_consumers() {
    let source = include_str!("../spec/cases/aggregate/copy-move.nera");
    let output = accepted("copy-move.nera", source);
    let hir = output.hir().expect("copy/move source has HIR");
    assert_eq!(hir.version(), nera::HirVersion::V20);
    let body = hir.entry_function().body().expect("entry body");

    let HirStatementKind::Let { value, .. } = &body.root.statements[2].kind else {
        panic!("owner aggregate constructor");
    };
    let HirExpressionKind::StructConstructor { fields } = &value.kind else {
        panic!("struct constructor");
    };
    assert!(matches!(
        fields[0].value.kind,
        HirExpressionKind::Read {
            mode: HirUseMode::Move,
            ..
        }
    ));
    let expected_modes = [HirUseMode::Move, HirUseMode::Copy, HirUseMode::Move];
    for (statement, expected) in body.root.statements[3..6].iter().zip(expected_modes) {
        let HirStatementKind::Let { value, .. } = &statement.kind else {
            panic!("copy/move let");
        };
        assert!(matches!(
            value.kind,
            HirExpressionKind::Read { mode, .. } if mode == expected
        ));
    }

    let vir = output.vir().expect("copy/move source has VIR");
    let instructions = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect::<Vec<_>>();
    assert!(instructions.iter().any(|instruction| matches!(
        instruction.instruction,
        VirInstruction::PermissionMove { .. }
    )));
    assert!(instructions.iter().any(|instruction| matches!(
        instruction.instruction,
        VirInstruction::ResourceInitialize { .. }
    )));
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(
                instruction.instruction,
                VirInstruction::ObjectTransfer {
                    source_mode: VirObjectSourceMode::Move,
                    ..
                }
            ))
            .count(),
        2
    );
    assert!(
        instructions.iter().any(|instruction| matches!(
            instruction.instruction,
            VirInstruction::ResourceTake { .. }
        ))
    );

    let resolved = vir.resolve().expect("copy/move VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("copy/move verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("copy/move program executes")
            .values(),
        [VirRuntimeValue::U64(7)]
    );
}

#[test]
fn pattern_binding_carries_move_and_takes_the_active_payload() {
    let source = include_str!("../spec/cases/aggregate/pattern-move.nera");
    let output = accepted("pattern-move.nera", source);
    let hir = output.hir().expect("pattern source has HIR");
    let body = hir.entry_function().body().expect("entry body");
    let HirStatementKind::Match { arms, .. } = &body.root.statements[2].kind else {
        panic!("enum match");
    };
    let HirPatternKind::Variant { fields, .. } = &arms[1].pattern.kind else {
        panic!("full variant");
    };
    assert!(matches!(
        fields[0].kind,
        HirPatternKind::Binding {
            mode: HirUseMode::Move,
            ..
        }
    ));

    let vir = output.vir().expect("pattern source has VIR");
    assert!(
        vir.runtime().functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .any(|instruction| matches!(
                instruction.instruction,
                VirInstruction::ResourceTake { .. }
            ))
    );
    let resolved = vir.resolve().expect("pattern VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("pattern verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("pattern program executes")
            .values(),
        [VirRuntimeValue::U64(1)]
    );
}

#[test]
fn hir_validator_rejects_copy_mode_forged_for_move_only_value() {
    let source = "fn identity(owner: Own<u64>) -> Own<u64> { return owner; }";
    let output = accepted("forged-copy.nera", source);
    let mut tables = clone_tables(output.hir().expect("owned HIR"));
    let body = tables.functions[0].body.as_mut().expect("owned body");
    let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[0].kind else {
        panic!("owned return");
    };
    let HirExpressionKind::Read { mode, .. } = &mut value.kind else {
        panic!("owned return read");
    };
    *mode = HirUseMode::Copy;

    let error =
        HirProgram::from_tables(tables).expect_err("MoveOnly copy must fail HIR validation");
    assert_eq!(error.table(), "expression");
    assert!(error.problem().contains("read use mode"));

    let pattern_source = include_str!("../spec/cases/aggregate/pattern-move.nera");
    let pattern_output = accepted("forged-pattern-copy.nera", pattern_source);
    let mut pattern_tables = clone_tables(pattern_output.hir().expect("pattern HIR"));
    let body = pattern_tables.functions[0]
        .body
        .as_mut()
        .expect("pattern body");
    let HirStatementKind::Match { arms, .. } = &mut body.root.statements[2].kind else {
        panic!("pattern match");
    };
    let HirPatternKind::Variant { fields, .. } = &mut arms[1].pattern.kind else {
        panic!("full pattern");
    };
    let HirPatternKind::Binding { mode, .. } = &mut fields[0].kind else {
        panic!("payload binding");
    };
    *mode = HirUseMode::Copy;
    let error = HirProgram::from_tables(pattern_tables)
        .expect_err("MoveOnly pattern Copy must fail HIR validation");
    assert_eq!(error.table(), "pattern");
    assert!(error.problem().contains("binding use mode"));
}

#[test]
fn verifier_rejects_use_after_scalar_and_whole_object_move_at_the_use_site() {
    let cases = [
        (
            "scalar-use-after-move.nera",
            "fn main() -> u64 {
                let first = alloc<u64>(1);
                *first = 9;
                let second = first;
                let invalid = *first;
                free(second);
                return invalid;
            }",
            "*first",
        ),
        (
            "object-use-after-move.nera",
            "struct Boxed { owner: Own<u64>, value: u64, }
             fn main() -> u64 {
                let owner = alloc<u64>(1);
                let first = Boxed { owner: owner, value: 3 };
                let second = first;
                let invalid = first.value;
                let extracted = second.owner;
                free(extracted);
                return invalid;
             }",
            "first.value",
        ),
    ];
    for (name, source, invalid_use) in cases {
        let output = accepted(name, source);
        let resolved = output
            .vir()
            .expect("negative source has VIR")
            .resolve()
            .expect("negative VIR resolves");
        let verification = verify_program(&resolved, CfgAnalysisConfig::default())
            .expect("negative verification converges");
        let start = source.rfind(invalid_use).expect("invalid use text");
        let expected = nera::ByteSpan::new(start, start + invalid_use.len()).expect("use span");
        assert!(
            verification.diagnostics().iter().any(|diagnostic| {
                diagnostic.kind() == VerifierDiagnosticKind::RefutedObligation
                    && diagnostic.source_span() == expected
            }),
            "{name}: {:?}",
            verification.diagnostics()
        );
    }
}

#[test]
fn verifier_rejects_whole_read_after_partial_move() {
    let source = "struct Boxed { owner: Own<u64>, value: u64, }
         fn main() -> u64 {
            let owner = alloc<u64>(1);
            let container = Boxed { owner: owner, value: 3 };
            let extracted = container.owner;
            let invalid = container;
            free(extracted);
            return invalid.value;
         }";
    let output = accepted("whole-after-partial-move.nera", source);
    let resolved = output
        .vir()
        .expect("negative source has VIR")
        .resolve()
        .expect("negative VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("negative verification converges");
    let invalid_statement = "let invalid = container;";
    let start = source.find(invalid_statement).expect("invalid statement");
    let end = start + invalid_statement.len();
    assert!(
        verification.diagnostics().iter().any(|diagnostic| {
            diagnostic.kind() == VerifierDiagnosticKind::RefutedObligation
                && diagnostic.source_span().start() >= start
                && diagnostic.source_span().end() <= end
        }),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
}

#[test]
fn live_resource_replacement_runs_builtin_drop_before_assignment() {
    let source = "struct Boxed { owner: Own<u64>, }
         fn main() -> u64 {
            let first_owner = alloc<u64>(1);
            let second_owner = alloc<u64>(1);
            let mut first = Boxed { owner: first_owner };
            let second = Boxed { owner: second_owner };
            first = second;
            let extracted = first.owner;
            free(extracted);
            return 0;
         }";
    let output = accepted("live-resource-replacement.nera", source);
    assert!(
        output
            .vir()
            .expect("replacement source has VIR")
            .runtime()
            .functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .any(|instruction| matches!(
                instruction.instruction,
                VirInstruction::ObjectDrop { .. }
            ))
    );
    let resolved = output
        .vir()
        .expect("replacement source has VIR")
        .resolve()
        .expect("replacement VIR resolves");
    let verification = verify_program(&resolved, CfgAnalysisConfig::default())
        .expect("replacement verification converges");
    assert!(
        verification.is_memory_checked_core0(),
        "diagnostics: {:?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("replacement executes")
            .values(),
        [VirRuntimeValue::U64(0)]
    );
}

#[test]
fn owned_call_arguments_and_returns_preserve_move_mode() {
    let source = include_str!("../spec/cases/control-flow/owned-call.nera");
    let output = accepted("owned-call.nera", source);
    let hir = output.hir().expect("owned call HIR");
    let mut move_reads = 0;
    for function in hir.functions() {
        let Some(body) = function.body() else {
            continue;
        };
        for statement in &body.root.statements {
            match &statement.kind {
                HirStatementKind::Let { value, .. } => {
                    if let HirExpressionKind::Call(call) = &value.kind {
                        move_reads += call
                            .arguments
                            .iter()
                            .filter(|argument| {
                                matches!(
                                    argument.kind,
                                    HirExpressionKind::Read {
                                        mode: HirUseMode::Move,
                                        ..
                                    }
                                )
                            })
                            .count();
                    }
                }
                HirStatementKind::Return { value: Some(value) }
                    if matches!(
                        value.kind,
                        HirExpressionKind::Read {
                            mode: HirUseMode::Move,
                            ..
                        }
                    ) =>
                {
                    move_reads += 1;
                }
                _ => {}
            }
        }
    }
    assert_eq!(move_reads, 2);
    assert!(
        output
            .vir()
            .expect("owned call VIR")
            .runtime()
            .functions
            .iter()
            .flat_map(|function| &function.blocks)
            .flat_map(|block| &block.instructions)
            .filter(|instruction| matches!(
                instruction.instruction,
                VirInstruction::PermissionMove { .. }
            ))
            .count()
            >= 2
    );
}

#[test]
fn moving_a_payload_from_an_inactive_variant_is_refuted() {
    let source = "enum Package { Empty, Full(Own<u64>), }
        fn main() -> u64 {
            let package = Package::Empty;
            match package {
                Package::Empty => { return 0; },
                Package::Full(extracted) => { free(extracted); return 1; },
            }
        }";
    let output = accepted("inactive-pattern-move.nera", source);
    let mut unit = output.vir().expect("pattern VIR").as_unit().clone();
    let enum_type = unit
        .memory
        .types
        .iter()
        .find(|ty| matches!(ty.kind, VirMemoryTypeKind::Enum { .. }))
        .expect("resource enum");
    let enum_access = unit.memory.access(enum_type.id).expect("enum access");
    let field = unit
        .memory
        .fields
        .iter()
        .find(|field| field.owner == enum_type.id)
        .expect("resource payload field");
    let field_access = unit.memory.access(field.ty).expect("field access");
    let VirMemoryTypeKind::Pointer { pointee, .. } =
        unit.memory.kind(field.ty).expect("resource field type")
    else {
        panic!("resource field is a pointer");
    };
    let pointee_access = unit.memory.access(*pointee).expect("pointee access");
    let layout = unit.memory.layout(enum_access.layout).expect("enum layout");
    let variants = layout.variants.as_ref().expect("enum variant layout");
    let full_case = variants
        .cases
        .iter()
        .find(|case| !case.fields.is_empty())
        .expect("full case");
    let offset_bytes = full_case.payload_offset_bytes + full_case.fields[0].offset_bytes;
    let empty_block = unit.runtime.functions[0]
        .blocks
        .iter_mut()
        .find(|block| {
            block.parameters.len() >= 2
                && block.instructions.iter().any(|instruction| {
                    matches!(
                        instruction.instruction,
                        VirInstruction::Constant {
                            value: nera::VirConstant::U64(0),
                            ..
                        }
                    )
                })
        })
        .expect("empty-variant block");
    let object = empty_block.parameters[0].id;
    let permission = empty_block.parameters[1].id;
    let source_span = empty_block.source_span;
    empty_block.instructions.splice(
        0..0,
        [
            SpannedVirInstruction {
                instruction: VirInstruction::FieldAddress {
                    result: VirValue {
                        id: VirValueId::new(10_000),
                        ty: VirType::Pointer {
                            access: field_access,
                        },
                    },
                    base: object,
                    field: field.id,
                    owner: enum_access,
                    field_access,
                    offset_bytes,
                },
                source_span,
            },
            SpannedVirInstruction {
                instruction: VirInstruction::ResourceTake {
                    pointer_result: VirValue {
                        id: VirValueId::new(10_001),
                        ty: VirType::Pointer {
                            access: pointee_access,
                        },
                    },
                    permission_result: VirValue {
                        id: VirValueId::new(10_002),
                        ty: VirType::Permission,
                    },
                    source: VirValueId::new(10_000),
                    source_permission: permission,
                    access: field_access,
                },
                source_span,
            },
        ],
    );
    unit.rebuild_source_map_from_runtime("inactive-pattern-move.vir", source.len());
    let validated = unit
        .into_validated()
        .expect("inactive payload move is structurally valid VIR");
    let resolved = validated.resolve().expect("inactive payload VIR resolves");
    let analysis = analyze_function_cfg(&resolved, nera::VirFunctionId::new(0))
        .expect("inactive payload analysis converges");
    assert!(analysis.obligations().iter().any(|record| {
        matches!(
            record.obligation().kind(),
            ResourceObligationKind::ActiveVariantAllowsAccess { .. }
        ) && record.obligation().status() == ObligationStatus::Refuted
    }));
}
