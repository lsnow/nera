use super::FrontendFailure;
mod contract_snapshots;
mod loop_schema;
mod spec_arithmetic;
mod spec_assertions;
mod spec_exists;
mod spec_memory;
mod spec_separation;
use crate::ValidatedVirUnit;
use crate::backend::X86_64_UNKNOWN_LINUX_GNU;
use crate::frontend::hir::{
    HirAbiClass, HirCall, HirContract, HirContractId, HirDeclaration, HirExpression,
    HirExpressionKind, HirField, HirFieldId, HirFieldInitializer, HirFieldLayout, HirFunction,
    HirFunctionId, HirFunctionType, HirGenericParameter, HirGenericParameterId, HirIntegerType,
    HirLayout, HirLayoutId, HirMutability, HirNodeId, HirPlace, HirPlaceBase, HirProgram,
    HirProgramTables, HirProjection, HirProjectionKind, HirRegion, HirRegionId, HirRegionOrigin,
    HirRegionOwner, HirSpecClause, HirSpecClauseId, HirSpecClauseOwner, HirSpecContractPosition,
    HirSpecEnvironment, HirSpecLocation, HirSpecProve, HirSpecProveId, HirSpecSnapshot,
    HirSpecTerm, HirSpecTermId, HirSpecTermKind, HirStatement, HirStatementKind, HirTypeDefinition,
    HirTypeId, HirTypeKind, HirUseMode, HirVariant, HirVariantCaseLayout, HirVariantId,
    HirVariantLayout,
};
use crate::vir::{
    VirConstant, VirIndexBounds, VirInstruction, VirMemoryTypeKind, VirObjectDestinationMode,
    VirSpecClauseKind, VirSpecClauseOrigin, VirSpecClauseOwner, VirSpecSnapshot, VirSpecTermKind,
    VirTerminator,
};
use crate::{ByteSpan, SourceFile, analyze, interpret, verify_program};

fn hir_from_tables(
    mut tables: HirProgramTables,
) -> Result<HirProgram, super::super::hir::HirProgramValidationError> {
    tables.assign_canonical_node_ids()?;
    tables.assign_canonical_type_capabilities()?;
    HirProgram::from_tables(tables)
}

fn accepted_program(source: &str) -> HirProgram {
    analyze(&SourceFile::from_text("lowering-gate.nera", source))
        .hir()
        .expect("fixture source is accepted")
        .clone()
}

fn rebuild(
    base: &HirProgram,
    types: Vec<HirTypeDefinition>,
    generic_parameters: Vec<HirGenericParameter>,
    functions: Vec<HirFunction>,
) -> HirProgram {
    rebuild_result(base, types, generic_parameters, functions)
        .expect("mutation remains structurally table-valid")
}

fn rebuild_result(
    base: &HirProgram,
    types: Vec<HirTypeDefinition>,
    generic_parameters: Vec<HirGenericParameter>,
    functions: Vec<HirFunction>,
) -> Result<HirProgram, crate::HirProgramValidationError> {
    hir_from_tables(HirProgramTables {
        data_layout: base.data_layout(),
        entry_module: base.entry_module_id(),
        entry_function: base.entry_function_id(),
        modules: base.modules().to_vec(),
        types,
        type_capabilities: Vec::new(),
        layouts: base.layouts().to_vec(),
        fields: base.fields().to_vec(),
        variants: base.variants().to_vec(),
        generic_parameters,
        regions: base.regions().to_vec(),
        region_constraints: base.region_constraints().to_vec(),
        functions,
        contracts: base.contracts().to_vec(),
        predicates: base.predicates().to_vec(),
        specs: base.specs().clone(),
    })
}

fn append_concrete_type(
    tables: &mut HirProgramTables,
    name: &str,
    kind: HirTypeKind,
    size_bytes: u64,
    alignment: u64,
    abi: HirAbiClass,
    fields: Vec<HirFieldLayout>,
) -> (HirTypeId, HirLayoutId) {
    let ty = HirTypeId::new(u32::try_from(tables.types.len()).expect("small type table"));
    let layout = HirLayoutId::new(u32::try_from(tables.layouts.len()).expect("small layout table"));
    tables.types.push(HirTypeDefinition {
        id: ty,
        name: Some(name.to_owned()),
        kind,
        generic_parameters: Vec::new(),
        layout: Some(layout),
    });
    tables.layouts.push(HirLayout {
        id: layout,
        ty,
        size_bytes,
        alignment,
        abi,
        fields,
        variants: None,
    });
    (ty, layout)
}

fn program_tables(base: &HirProgram) -> HirProgramTables {
    HirProgramTables {
        data_layout: base.data_layout(),
        entry_module: base.entry_module_id(),
        entry_function: base.entry_function_id(),
        modules: base.modules().to_vec(),
        types: base.types().to_vec(),
        type_capabilities: Vec::new(),
        layouts: base.layouts().to_vec(),
        fields: base.fields().to_vec(),
        variants: base.variants().to_vec(),
        generic_parameters: base.generic_parameters().to_vec(),
        regions: base.regions().to_vec(),
        region_constraints: base.region_constraints().to_vec(),
        functions: base.functions().to_vec(),
        contracts: base.contracts().to_vec(),
        predicates: base.predicates().to_vec(),
        specs: base.specs().clone(),
    }
}

fn append_pair_type(
    tables: &mut HirProgramTables,
    span: ByteSpan,
) -> (HirTypeId, HirLayoutId, HirFieldId, HirFieldId) {
    let u64_ty = tables
        .types
        .iter()
        .find(|ty| ty.kind == HirTypeKind::Integer(HirIntegerType::U64))
        .expect("Core0 u64")
        .id;
    let pair = HirTypeId::new(u32::try_from(tables.types.len()).expect("small type table"));
    let left = HirFieldId::new(u32::try_from(tables.fields.len()).expect("small field table"));
    let right = HirFieldId::new(left.get() + 1);
    tables.fields.extend([
        HirField {
            id: left,
            owner: pair,
            name: "left".to_owned(),
            ty: u64_ty,
            span,
        },
        HirField {
            id: right,
            owner: pair,
            name: "right".to_owned(),
            ty: u64_ty,
            span,
        },
    ]);
    let (actual, layout) = append_concrete_type(
        tables,
        "Pair",
        HirTypeKind::Struct {
            fields: vec![left, right],
        },
        16,
        8,
        HirAbiClass::Aggregate,
        vec![
            HirFieldLayout {
                field: left,
                offset_bytes: 0,
            },
            HirFieldLayout {
                field: right,
                offset_bytes: 8,
            },
        ],
    );
    assert_eq!(actual, pair);
    (pair, layout, left, right)
}

fn pair_constructor(
    ty: HirTypeId,
    u64_ty: HirTypeId,
    left: HirFieldId,
    right: HirFieldId,
    first: u64,
    second: u64,
    span: ByteSpan,
) -> HirExpression {
    HirExpression {
        id: HirNodeId::new(0),
        kind: HirExpressionKind::StructConstructor {
            // Deliberately reverse declaration order: this is the source
            // evaluation order and must not be canonicalized by field ID.
            fields: vec![
                HirFieldInitializer {
                    field: right,
                    value: HirExpression {
                        id: HirNodeId::new(0),
                        kind: HirExpressionKind::Integer(second),
                        ty: u64_ty,
                        span,
                    },
                },
                HirFieldInitializer {
                    field: left,
                    value: HirExpression {
                        id: HirNodeId::new(0),
                        kind: HirExpressionKind::Integer(first),
                        ty: u64_ty,
                        span,
                    },
                },
            ],
        },
        ty,
        span,
    }
}

fn local_read(local: crate::HirLocalId, ty: HirTypeId, span: ByteSpan) -> HirExpression {
    HirExpression {
        id: HirNodeId::new(0),
        kind: HirExpressionKind::Read {
            place: Box::new(HirPlace {
                id: HirNodeId::new(0),
                base: HirPlaceBase::Local(local),
                projections: Vec::new(),
                ty,
                span,
            }),
            mode: HirUseMode::Copy,
        },
        ty,
        span,
    }
}

fn field_place(
    local: crate::HirLocalId,
    field: HirFieldId,
    field_ty: HirTypeId,
    span: ByteSpan,
) -> HirPlace {
    HirPlace {
        id: HirNodeId::new(0),
        base: HirPlaceBase::Local(local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::Field { field },
            result_type: field_ty,
            span,
        }],
        ty: field_ty,
        span,
    }
}

fn add_generic_parameter_type(
    base: &HirProgram,
    types: &mut Vec<HirTypeDefinition>,
) -> (HirGenericParameter, HirTypeId) {
    let parameter = HirGenericParameter {
        id: HirGenericParameterId::new(0),
        name: "T".to_owned(),
        span: base.entry_function().span,
    };
    let ty = HirTypeId::new(u32::try_from(types.len()).expect("small test table"));
    types.push(HirTypeDefinition {
        id: ty,
        name: Some("T".to_owned()),
        kind: HirTypeKind::GenericParameter(parameter.id),
        generic_parameters: Vec::new(),
        layout: None,
    });
    (parameter, ty)
}

#[test]
fn aggregate_constructors_and_assignments_lower_through_object_storage() {
    let base = accepted_program(
        "fn aggregate() -> u64 { let source = 0; let mut destination = 0; destination = source; return destination; }",
    );
    let mut tables = program_tables(&base);
    let span = base.entry_function().span;
    let u64_ty = tables.functions[0].signature.return_type;
    let (pair, pair_layout, left, right) = append_pair_type(&mut tables, span);
    let body = tables.functions[0].body.as_mut().expect("fixture body");
    let source = body.locals[0].id;
    let destination = body.locals[1].id;
    for local in &mut body.locals {
        local.ty = pair;
        local.layout = pair_layout;
    }
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[0].kind else {
        panic!("source let");
    };
    *value = pair_constructor(pair, u64_ty, left, right, 20, 22, value.span);
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[1].kind else {
        panic!("destination let");
    };
    *value = pair_constructor(pair, u64_ty, left, right, 1, 2, value.span);
    let HirStatementKind::Assign {
        destination: place,
        value,
    } = &mut body.root.statements[2].kind
    else {
        panic!("aggregate assignment");
    };
    place.ty = pair;
    *value = local_read(source, pair, value.span);
    let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[3].kind else {
        panic!("aggregate field return");
    };
    value.kind = HirExpressionKind::Read {
        place: Box::new(field_place(destination, right, u64_ty, value.span)),
        mode: HirUseMode::Copy,
    };
    value.ty = u64_ty;
    let self_assignment_span = body.root.statements[2].span;
    body.root.statements.insert(
        3,
        HirStatement {
            id: HirNodeId::new(0),
            kind: HirStatementKind::Assign {
                destination: HirPlace {
                    id: HirNodeId::new(0),
                    base: HirPlaceBase::Local(destination),
                    projections: Vec::new(),
                    ty: pair,
                    span: self_assignment_span,
                },
                value: local_read(destination, pair, self_assignment_span),
            },
            span: self_assignment_span,
        },
    );

    let hir = hir_from_tables(tables).expect("validated aggregate HIR");
    let vir = lower_test(&hir).expect("aggregate HIR lowers");
    let instructions = &vir.runtime().functions[0].blocks[0].instructions;
    assert_eq!(
        instructions
            .iter()
            .take_while(|instruction| {
                matches!(instruction.instruction, VirInstruction::LocalStorage { .. })
            })
            .count(),
        4,
        "two local identities and two constructor temporaries are entry storage"
    );
    let constructor_constants = instructions
        .iter()
        .filter_map(|instruction| match instruction.instruction {
            VirInstruction::Constant {
                value: VirConstant::U64(value),
                ..
            } if matches!(value, 22 | 20 | 2 | 1) => Some(value),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(constructor_constants, [22, 20, 2, 1]);
    let modes = instructions
        .iter()
        .filter_map(|instruction| match instruction.instruction {
            VirInstruction::ObjectTransfer {
                destination_mode, ..
            } => Some(destination_mode),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        modes,
        [
            VirObjectDestinationMode::Initialize,
            VirObjectDestinationMode::Initialize,
        ]
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|item| matches!(item.instruction, VirInstruction::Store { .. }))
            .count(),
        2
    );
    let resolved = vir.resolve().expect("aggregate VIR resolves");
    assert!(
        verify_program(&resolved, crate::CfgAnalysisConfig::default())
            .expect("aggregate verifier")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("aggregate interpreter")
            .values(),
        [crate::VirRuntimeValue::U64(22)]
    );
}

#[test]
fn aggregate_constructor_validation_rejects_missing_duplicate_and_wrong_fields() {
    let base = accepted_program("fn aggregate() -> u64 { let value = 0; return 0; }");
    let mut tables = program_tables(&base);
    let span = base.entry_function().span;
    let u64_ty = tables.functions[0].signature.return_type;
    let (pair, pair_layout, left, right) = append_pair_type(&mut tables, span);
    let body = tables.functions[0].body.as_mut().expect("fixture body");
    body.locals[0].ty = pair;
    body.locals[0].layout = pair_layout;
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[0].kind else {
        panic!("aggregate let");
    };
    *value = pair_constructor(pair, u64_ty, left, right, 1, 2, value.span);

    let valid = tables.clone();
    hir_from_tables(valid).expect("complete constructor");

    let mut missing = tables.clone();
    let HirStatementKind::Let { value, .. } =
        &mut missing.functions[0].body.as_mut().unwrap().root.statements[0].kind
    else {
        unreachable!()
    };
    let HirExpressionKind::StructConstructor { fields } = &mut value.kind else {
        unreachable!()
    };
    fields.pop();
    assert!(hir_from_tables(missing).is_err());

    let mut duplicate = tables;
    let HirStatementKind::Let { value, .. } = &mut duplicate.functions[0]
        .body
        .as_mut()
        .unwrap()
        .root
        .statements[0]
        .kind
    else {
        unreachable!()
    };
    let HirExpressionKind::StructConstructor { fields } = &mut value.kind else {
        unreachable!()
    };
    fields[1].field = fields[0].field;
    assert!(hir_from_tables(duplicate).is_err());
}

#[test]
fn tuple_array_enum_and_bool_constructors_reach_every_runtime_consumer() {
    let base = accepted_program(
        "fn shapes() -> u64 { let tuple = 0; let array = 0; let choice = 0; return 7; }",
    );
    let mut tables = program_tables(&base);
    let span = base.entry_function().span;
    let u64_ty = tables.functions[0].signature.return_type;
    let bool_ty = tables
        .types
        .iter()
        .find(|ty| ty.kind == HirTypeKind::Bool)
        .expect("Core0 bool")
        .id;
    let unit_ty = tables
        .types
        .iter()
        .find(|ty| ty.kind == HirTypeKind::Unit)
        .expect("Core0 unit")
        .id;

    let (tuple_ty, tuple_layout) = append_concrete_type(
        &mut tables,
        "WordFlag",
        HirTypeKind::Tuple(vec![u64_ty, bool_ty, unit_ty]),
        16,
        8,
        HirAbiClass::Aggregate,
        Vec::new(),
    );
    let (array_ty, array_layout) = append_concrete_type(
        &mut tables,
        "TwoWords",
        HirTypeKind::Array {
            element: u64_ty,
            length: 2,
        },
        16,
        8,
        HirAbiClass::Aggregate,
        Vec::new(),
    );

    let enum_ty = HirTypeId::new(u32::try_from(tables.types.len()).expect("small type table"));
    let payload = HirFieldId::new(u32::try_from(tables.fields.len()).expect("small field table"));
    let flag = HirFieldId::new(payload.get() + 1);
    tables.fields.extend([
        HirField {
            id: payload,
            owner: enum_ty,
            name: "payload".to_owned(),
            ty: u64_ty,
            span,
        },
        HirField {
            id: flag,
            owner: enum_ty,
            name: "flag".to_owned(),
            ty: bool_ty,
            span,
        },
    ]);
    let variant =
        HirVariantId::new(u32::try_from(tables.variants.len()).expect("small variant table"));
    tables.variants.push(HirVariant {
        id: variant,
        owner: enum_ty,
        name: "Present".to_owned(),
        fields: vec![payload, flag],
        discriminant: 3,
        span,
    });
    let (actual_enum_ty, enum_layout) = append_concrete_type(
        &mut tables,
        "Choice",
        HirTypeKind::Enum {
            variants: vec![variant],
        },
        24,
        8,
        HirAbiClass::Aggregate,
        Vec::new(),
    );
    assert_eq!(actual_enum_ty, enum_ty);
    tables.layouts[enum_layout.index()].variants = Some(HirVariantLayout {
        tag_size_bytes: 1,
        tag_alignment: 1,
        cases: vec![HirVariantCaseLayout {
            variant,
            payload_offset_bytes: 8,
            fields: vec![
                HirFieldLayout {
                    field: payload,
                    offset_bytes: 0,
                },
                HirFieldLayout {
                    field: flag,
                    offset_bytes: 8,
                },
            ],
        }],
    });

    let body = tables.functions[0].body.as_mut().expect("fixture body");
    for (local, (ty, layout)) in body.locals.iter_mut().zip([
        (tuple_ty, tuple_layout),
        (array_ty, array_layout),
        (enum_ty, enum_layout),
    ]) {
        local.ty = ty;
        local.layout = layout;
    }
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[0].kind else {
        panic!("tuple let");
    };
    value.kind = HirExpressionKind::TupleConstructor {
        elements: vec![
            HirExpression {
                id: HirNodeId::new(0),
                kind: HirExpressionKind::Integer(9),
                ty: u64_ty,
                span: value.span,
            },
            HirExpression {
                id: HirNodeId::new(0),
                kind: HirExpressionKind::Bool(true),
                ty: bool_ty,
                span: value.span,
            },
            HirExpression {
                id: HirNodeId::new(0),
                kind: HirExpressionKind::Unit,
                ty: unit_ty,
                span: value.span,
            },
        ],
    };
    value.ty = tuple_ty;
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[1].kind else {
        panic!("array let");
    };
    value.kind = HirExpressionKind::ArrayConstructor {
        elements: vec![
            HirExpression {
                id: HirNodeId::new(0),
                kind: HirExpressionKind::Integer(10),
                ty: u64_ty,
                span: value.span,
            },
            HirExpression {
                id: HirNodeId::new(0),
                kind: HirExpressionKind::Integer(11),
                ty: u64_ty,
                span: value.span,
            },
        ],
    };
    value.ty = array_ty;
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[2].kind else {
        panic!("enum let");
    };
    value.kind = HirExpressionKind::EnumConstructor {
        variant,
        fields: vec![
            HirFieldInitializer {
                field: flag,
                value: HirExpression {
                    id: HirNodeId::new(0),
                    kind: HirExpressionKind::Bool(false),
                    ty: bool_ty,
                    span: value.span,
                },
            },
            HirFieldInitializer {
                field: payload,
                value: HirExpression {
                    id: HirNodeId::new(0),
                    kind: HirExpressionKind::Integer(55),
                    ty: u64_ty,
                    span: value.span,
                },
            },
        ],
    };
    value.ty = enum_ty;

    let hir = hir_from_tables(tables).expect("validated constructor HIR");
    let vir = lower_test(&hir).expect("all aggregate constructors lower");
    let instructions = vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect::<Vec<_>>();
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(
                instruction.instruction,
                VirInstruction::TupleElementAddress { .. }
            ))
            .count(),
        3
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(
                instruction.instruction,
                VirInstruction::ObjectTransfer {
                    source_mode: crate::VirObjectSourceMode::Move,
                    ..
                }
            ))
            .count(),
        3
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(
                instruction.instruction,
                VirInstruction::IndexAddress {
                    bounds: VirIndexBounds::Array { length: 2 },
                    ..
                }
            ))
            .count(),
        2
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(
                instruction.instruction,
                VirInstruction::EnumSetDiscriminant { .. }
            ))
            .count(),
        1
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| matches!(
                instruction.instruction,
                VirInstruction::ObjectDeinitialize { .. }
            ))
            .count(),
        0
    );

    let resolved = vir.resolve().expect("constructor VIR resolves");
    assert!(
        verify_program(&resolved, crate::CfgAnalysisConfig::default())
            .expect("constructor verifier")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime())
            .expect("constructors execute")
            .values(),
        [crate::VirRuntimeValue::U64(7)]
    );
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("constructors lower to x86_64");
    X86_64_UNKNOWN_LINUX_GNU
        .emit_assembly(&machine)
        .expect("constructor machine plan emits assembly");
}

#[test]
fn aggregate_assignment_refinement_handles_branch_and_loop_joins() {
    let branch_base = accepted_program(
        "fn branch() -> u64 { let mut value = 0; if true { value = 1; } else { value = 2; } return value; }",
    );
    let mut branch_tables = program_tables(&branch_base);
    let branch_span = branch_base.entry_function().span;
    let branch_u64 = branch_tables.functions[0].signature.return_type;
    let (pair, pair_layout, left, right) = append_pair_type(&mut branch_tables, branch_span);
    let body = branch_tables.functions[0]
        .body
        .as_mut()
        .expect("branch body");
    let local = body.locals[0].id;
    body.locals[0].ty = pair;
    body.locals[0].layout = pair_layout;
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[0].kind else {
        panic!("branch initial value");
    };
    *value = pair_constructor(pair, branch_u64, left, right, 10, 12, value.span);
    let HirStatementKind::If {
        then_block,
        else_block: Some(else_block),
        ..
    } = &mut body.root.statements[1].kind
    else {
        panic!("branch statement");
    };
    for (block, first, second) in [(then_block, 30, 32), (else_block, 40, 42)] {
        let HirStatementKind::Assign { destination, value } = &mut block.statements[0].kind else {
            panic!("branch assignment");
        };
        destination.ty = pair;
        *value = pair_constructor(pair, branch_u64, left, right, first, second, value.span);
    }
    let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[2].kind else {
        panic!("branch return");
    };
    value.kind = HirExpressionKind::Read {
        place: Box::new(field_place(local, right, branch_u64, value.span)),
        mode: HirUseMode::Copy,
    };
    value.ty = branch_u64;
    let branch_hir = hir_from_tables(branch_tables).expect("branch aggregate HIR");
    let branch_vir = lower_test(&branch_hir).expect("branch aggregate lowering");
    let branch_modes = branch_vir.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction.instruction {
            VirInstruction::ObjectTransfer {
                destination_mode, ..
            } => Some(destination_mode),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        branch_modes
            .iter()
            .filter(|mode| **mode == VirObjectDestinationMode::Initialize)
            .count(),
        1
    );
    assert_eq!(
        branch_vir.runtime().functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter(|item| matches!(item.instruction, VirInstruction::Store { .. }))
            .count(),
        4
    );
    let branch_resolved = branch_vir.resolve().expect("branch resolve");
    assert!(
        verify_program(&branch_resolved, crate::CfgAnalysisConfig::default())
            .expect("branch verify")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(branch_resolved.runtime())
            .expect("branch execute")
            .values(),
        [crate::VirRuntimeValue::U64(32)]
    );

    let loop_base = accepted_program(
        "fn looping() -> u64 { let mut value = 0; let mut counter = 0; while counter < 1 { value = 1; counter = 1; } return value; }",
    );
    let mut loop_tables = program_tables(&loop_base);
    let loop_span = loop_base.entry_function().span;
    let loop_u64 = loop_tables.functions[0].signature.return_type;
    let (pair, pair_layout, left, right) = append_pair_type(&mut loop_tables, loop_span);
    let body = loop_tables.functions[0].body.as_mut().expect("loop body");
    let value_local = body.locals[0].id;
    body.locals[0].ty = pair;
    body.locals[0].layout = pair_layout;
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[0].kind else {
        panic!("loop initial value");
    };
    *value = pair_constructor(pair, loop_u64, left, right, 10, 12, value.span);
    let HirStatementKind::While {
        body: loop_body, ..
    } = &mut body.root.statements[2].kind
    else {
        panic!("loop statement");
    };
    let HirStatementKind::Assign { destination, value } = &mut loop_body.statements[0].kind else {
        panic!("loop aggregate assignment");
    };
    destination.ty = pair;
    *value = pair_constructor(pair, loop_u64, left, right, 40, 42, value.span);
    let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[3].kind else {
        panic!("loop return");
    };
    value.kind = HirExpressionKind::Read {
        place: Box::new(field_place(value_local, right, loop_u64, value.span)),
        mode: HirUseMode::Copy,
    };
    value.ty = loop_u64;
    let loop_hir = hir_from_tables(loop_tables).expect("loop aggregate HIR");
    let loop_vir = lower_test(&loop_hir).expect("loop aggregate lowering");
    assert!(loop_vir.runtime().functions[0].blocks.iter().any(|block| {
        block
            .instructions
            .iter()
            .any(|instruction| matches!(instruction.instruction, VirInstruction::Store { .. }))
    }));
    let loop_resolved = loop_vir.resolve().expect("loop resolve");
    assert!(
        verify_program(&loop_resolved, crate::CfgAnalysisConfig::default())
            .expect("loop verify")
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(loop_resolved.runtime())
            .expect("loop execute")
            .values(),
        [crate::VirRuntimeValue::U64(42)]
    );
}

#[test]
fn partial_aggregate_construction_must_be_complete_before_whole_copy() {
    let base = accepted_program(
        "fn partial() -> u64 { let mut source = 0; let destination = source; return destination; }",
    );
    let mut tables = program_tables(&base);
    let span = base.entry_function().span;
    let u64_ty = tables.functions[0].signature.return_type;
    let (pair, pair_layout, left, right) = append_pair_type(&mut tables, span);
    let body = tables.functions[0].body.as_mut().expect("partial body");
    let source = body.locals[0].id;
    let destination = body.locals[1].id;
    for local in &mut body.locals {
        local.ty = pair;
        local.layout = pair_layout;
    }
    let assignment_span = body.root.statements[0].span;
    body.root.statements[0] = HirStatement {
        id: HirNodeId::new(0),
        kind: HirStatementKind::Assign {
            destination: field_place(source, left, u64_ty, assignment_span),
            value: HirExpression {
                id: HirNodeId::new(0),
                kind: HirExpressionKind::Integer(20),
                ty: u64_ty,
                span: assignment_span,
            },
        },
        span: assignment_span,
    };
    body.root.statements.insert(
        1,
        HirStatement {
            id: HirNodeId::new(0),
            kind: HirStatementKind::Assign {
                destination: field_place(source, right, u64_ty, assignment_span),
                value: HirExpression {
                    id: HirNodeId::new(0),
                    kind: HirExpressionKind::Integer(22),
                    ty: u64_ty,
                    span: assignment_span,
                },
            },
            span: assignment_span,
        },
    );
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[2].kind else {
        panic!("partial destination let");
    };
    *value = local_read(source, pair, value.span);
    let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[3].kind else {
        panic!("partial return");
    };
    value.kind = HirExpressionKind::Read {
        place: Box::new(field_place(destination, right, u64_ty, value.span)),
        mode: HirUseMode::Copy,
    };
    value.ty = u64_ty;

    let complete = hir_from_tables(tables.clone()).expect("partial field HIR");
    let complete = lower_test(&complete).expect("completed object copies");
    let modes = complete.runtime().functions[0].blocks[0]
        .instructions
        .iter()
        .filter_map(|instruction| match instruction.instruction {
            VirInstruction::Initialize { .. } => Some("leaf-init"),
            VirInstruction::ObjectTransfer {
                destination_mode: VirObjectDestinationMode::Initialize,
                ..
            } => Some("object-init"),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(modes, ["leaf-init", "leaf-init", "object-init"]);

    let mut incomplete = tables;
    incomplete.functions[0]
        .body
        .as_mut()
        .unwrap()
        .root
        .statements
        .remove(1);
    let incomplete = hir_from_tables(incomplete).expect("partial HIR is structural");
    let incomplete = lower_test(&incomplete).expect("lowering preserves the unsafe read");
    let resolved = incomplete.resolve().expect("incomplete VIR resolves");
    let verification = verify_program(&resolved, crate::CfgAnalysisConfig::default())
        .expect("incomplete object verification converges");
    assert!(!verification.is_memory_checked_core0());
}

#[test]
fn typed_spec_hir_lowers_into_the_shared_spec_vir_arenas() {
    let base = accepted_program("fn identity(value: u64) -> u64 { return value; }");
    let function = base.entry_function();
    let function_id = function.id;
    let contract_id = function.contract;
    let parameter = function.body().expect("fixture body").parameters[0];
    let span = ByteSpan::new(function.span.start() + 1, function.span.end() - 1)
        .expect("nested spec span");
    let bool_ty = base
        .types()
        .iter()
        .find(|ty| ty.kind == HirTypeKind::Bool)
        .expect("bool type")
        .id;
    let u64_ty = base
        .types()
        .iter()
        .find(|ty| ty.kind == HirTypeKind::Integer(HirIntegerType::U64))
        .expect("u64 type")
        .id;
    let mut contracts = base.contracts().to_vec();
    contracts[contract_id.index()].clauses = vec![HirSpecClauseId::new(1)];
    let specs = HirSpecEnvironment {
        assertions: vec![],
        binders: Vec::new(),
        terms: vec![
            HirSpecTerm {
                id: HirSpecTermId::new(0),
                clause: HirSpecClauseId::new(0),
                ty: u64_ty,
                kind: HirSpecTermKind::Snapshot(HirSpecSnapshot::Local {
                    function: function_id,
                    local: parameter,
                }),
                span,
            },
            HirSpecTerm {
                id: HirSpecTermId::new(1),
                clause: HirSpecClauseId::new(0),
                ty: u64_ty,
                kind: HirSpecTermKind::U64(10),
                span,
            },
            HirSpecTerm {
                id: HirSpecTermId::new(2),
                clause: HirSpecClauseId::new(0),
                ty: bool_ty,
                kind: HirSpecTermKind::LessOrEqual {
                    left: HirSpecTermId::new(0),
                    right: HirSpecTermId::new(1),
                },
                span,
            },
            HirSpecTerm {
                id: HirSpecTermId::new(3),
                clause: HirSpecClauseId::new(1),
                ty: u64_ty,
                kind: HirSpecTermKind::Snapshot(HirSpecSnapshot::Result {
                    function: function_id,
                }),
                span,
            },
            HirSpecTerm {
                id: HirSpecTermId::new(4),
                clause: HirSpecClauseId::new(1),
                ty: u64_ty,
                kind: HirSpecTermKind::U64(10),
                span,
            },
            HirSpecTerm {
                id: HirSpecTermId::new(5),
                clause: HirSpecClauseId::new(1),
                ty: bool_ty,
                kind: HirSpecTermKind::Equal {
                    left: HirSpecTermId::new(3),
                    right: HirSpecTermId::new(4),
                },
                span,
            },
        ],
        clauses: vec![
            HirSpecClause {
                id: HirSpecClauseId::new(0),
                owner: HirSpecClauseOwner::Prove(HirSpecProveId::new(0)),
                location: HirSpecLocation::FunctionEntry {
                    function: function_id,
                },
                root: HirSpecTermId::new(2).into(),
                span,
            },
            HirSpecClause {
                id: HirSpecClauseId::new(1),
                owner: HirSpecClauseOwner::Contract {
                    contract: contract_id,
                    position: HirSpecContractPosition::Ensures,
                },
                location: HirSpecLocation::FunctionResult {
                    function: function_id,
                },
                root: HirSpecTermId::new(5).into(),
                span,
            },
        ],
        proves: vec![HirSpecProve {
            id: HirSpecProveId::new(0),
            function: function_id,
            location: HirSpecLocation::FunctionEntry {
                function: function_id,
            },
            clause: HirSpecClauseId::new(0),
            span,
        }],
        trust_entries: Vec::new(),
        loop_invariants: Vec::new(),
    };
    let hir = hir_from_tables(HirProgramTables {
        data_layout: base.data_layout(),
        entry_module: base.entry_module_id(),
        entry_function: base.entry_function_id(),
        modules: base.modules().to_vec(),
        types: base.types().to_vec(),
        type_capabilities: Vec::new(),
        layouts: base.layouts().to_vec(),
        fields: base.fields().to_vec(),
        variants: base.variants().to_vec(),
        generic_parameters: base.generic_parameters().to_vec(),
        regions: base.regions().to_vec(),
        region_constraints: base.region_constraints().to_vec(),
        functions: base.functions().to_vec(),
        contracts,
        predicates: base.predicates().to_vec(),
        specs,
    })
    .expect("typed Spec HIR fixture");

    let unit = lower_test(&hir).expect("typed Spec HIR lowers");
    let specs = &unit.as_unit().specs;
    assert_eq!(specs.terms().len(), 6);
    assert_eq!(specs.clauses().len(), 2);
    assert_eq!(specs.proves().len(), 1);
    assert_eq!(
        specs
            .contract(crate::VirContractId::new(0))
            .unwrap()
            .clauses,
        [crate::VirSpecClauseId::new(1)]
    );
    assert!(matches!(
        specs.terms()[0].kind,
        VirSpecTermKind::Snapshot(VirSpecSnapshot::Parameter { slot: 0, .. })
    ));
    assert!(matches!(
        specs.terms()[3].kind,
        VirSpecTermKind::Snapshot(VirSpecSnapshot::Result { slot: 0, .. })
    ));
    assert!(matches!(
        specs.clauses()[0].owner,
        VirSpecClauseOwner::Prove(_)
    ));
    assert!(matches!(
        specs.clauses()[1].kind,
        VirSpecClauseKind::Logic { .. }
    ));
    assert_eq!(
        unit.as_unit()
            .source_map
            .source_span_for_origin(specs.clauses()[0].origin.origin())
            .expect("spec-only origin")
            .span,
        span
    );
}

#[test]
fn unresolved_runtime_layout_fails_closed() {
    let base = accepted_program("fn f() -> u64 { return 1; }");
    let mut types = base.types().to_vec();
    let unresolved_type = HirTypeId::new(u32::try_from(types.len()).expect("small test table"));
    types.push(HirTypeDefinition {
        id: unresolved_type,
        name: Some("unresolved-u64".to_owned()),
        kind: HirTypeKind::Integer(crate::HirIntegerType::U64),
        generic_parameters: Vec::new(),
        layout: None,
    });
    let mut functions = base.functions().to_vec();
    let function = &mut functions[0];
    function.signature.return_type = unresolved_type;
    let signature_type = function.signature.ty;
    types[signature_type.index()].kind = HirTypeKind::Function(HirFunctionType {
        parameters: function.signature.parameters.clone(),
        return_type: unresolved_type,
        calling_convention: function.signature.calling_convention,
    });
    let body = function.body.as_mut().expect("fixture body");
    let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[0].kind else {
        panic!("fixture return value");
    };
    value.ty = unresolved_type;
    let malformed = rebuild(&base, types, base.generic_parameters().to_vec(), functions);

    assert!(lower_test(&malformed).is_err());
}

#[test]
fn unused_generic_definition_stays_in_hir_but_not_vir() {
    let base = accepted_program("fn f() { return; }");
    let mut types = base.types().to_vec();
    let (parameter, _) = add_generic_parameter_type(&base, &mut types);
    let extended = rebuild(&base, types, vec![parameter], base.functions().to_vec());

    assert!(lower_test(&extended).is_ok());
}

#[test]
fn generic_runtime_signature_fails_closed() {
    let base = accepted_program("fn f() -> u64 { return 1; }");
    let mut types = base.types().to_vec();
    let (parameter, generic_type) = add_generic_parameter_type(&base, &mut types);
    let mut functions = base.functions().to_vec();
    let function = &mut functions[0];
    function.generic_parameters = vec![parameter.id];
    function.signature.return_type = generic_type;
    let signature_type = function.signature.ty;
    types[signature_type.index()].kind = HirTypeKind::Function(HirFunctionType {
        parameters: function.signature.parameters.clone(),
        return_type: generic_type,
        calling_convention: function.signature.calling_convention,
    });
    let body = function.body.as_mut().expect("fixture body");
    let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[0].kind else {
        panic!("fixture return value");
    };
    value.ty = generic_type;
    assert!(rebuild_result(&base, types, vec![parameter], functions).is_err());
}

#[test]
fn allocation_metadata_is_rederived_from_layout() {
    let base = accepted_program("fn f() { let memory = alloc<u64>(1); free(memory); return; }");
    let mut functions = base.functions().to_vec();
    let body = functions[0].body.as_mut().expect("fixture body");
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[0].kind else {
        panic!("fixture allocation");
    };
    let crate::HirExpressionKind::Allocate { size_bytes, .. } = &mut value.kind else {
        panic!("fixture allocation expression");
    };
    *size_bytes += 1;
    let malformed = rebuild_result(
        &base,
        base.types().to_vec(),
        base.generic_parameters().to_vec(),
        functions,
    );

    assert!(
        malformed.is_err(),
        "allocation layout metadata is checked at the HIR boundary"
    );
}

#[test]
fn aggregate_allocation_count_cannot_bypass_hir_admission() {
    let base =
        accepted_program("fn main() -> u64 { let p = alloc<(u64, u64)>(1); free(p); return 42; }");
    let mut functions = base.functions().to_vec();
    let body = functions[0].body.as_mut().unwrap();
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[0].kind else {
        panic!("allocation");
    };
    let HirExpressionKind::Allocate {
        element_count,
        size_bytes,
        ..
    } = &mut value.kind
    else {
        panic!("allocation");
    };
    // Internally consistent extent is still outside single-object admission.
    *element_count = 2;
    *size_bytes *= 2;
    assert!(
        rebuild_result(
            &base,
            base.types().to_vec(),
            base.generic_parameters().to_vec(),
            functions
        )
        .is_err()
    );
}

#[test]
fn raw_pointer_cannot_be_lowered_as_a_free_owner() {
    let base = accepted_program(
        "fn f() { let memory = alloc<u64>(2); let next = memory + 8; free(memory); return; }",
    );
    let mut functions = base.functions().to_vec();
    let body = functions[0].body.as_mut().expect("fixture body");
    let raw_local = body
        .locals
        .iter()
        .find(|local| local.name == "next")
        .expect("raw local")
        .id;
    let free = body
        .root
        .statements
        .iter_mut()
        .find(|statement| matches!(statement.kind, HirStatementKind::Free { .. }))
        .expect("free statement");
    free.kind = HirStatementKind::Free { pointer: raw_local };
    let malformed = rebuild_result(
        &base,
        base.types().to_vec(),
        base.generic_parameters().to_vec(),
        functions,
    );

    assert!(malformed.is_err());
}

#[test]
fn inferred_own_contracts_are_rederived_from_the_hir_type() {
    let owned = accepted_program("fn identity(memory: Own<u64>) -> Own<u64> { return memory; }");
    let owned_vir = lower_test(&owned).expect("owned signature lowers");
    let owned_contract = &owned_vir.as_unit().specs.contracts()[0];
    assert_eq!(owned_contract.resources.len(), 2);
    assert_eq!(owned_contract.clauses.len(), 2);
    assert!(owned_contract.clauses.iter().all(|id| {
        let clause = owned_vir
            .as_unit()
            .specs
            .clause(*id)
            .expect("contract clause");
        matches!(clause.origin, VirSpecClauseOrigin::InferredType { .. })
            && matches!(clause.kind, VirSpecClauseKind::Resource(_))
    }));
    assert!(owned_vir.as_unit().specs.trust_entries().is_empty());

    let mut types = owned.types().to_vec();
    let own = types
        .iter_mut()
        .find(|definition| matches!(definition.kind, HirTypeKind::Own { .. }))
        .expect("owned type");
    let HirTypeKind::Own { pointee } = own.kind else {
        unreachable!("owned type retained")
    };
    own.kind = HirTypeKind::RawPointer {
        pointee,
        mutability: HirMutability::Mutable,
    };
    let mut functions = owned.functions().to_vec();
    let body = functions[0].body.as_mut().expect("owned body");
    let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[0].kind else {
        panic!("owned return");
    };
    let HirExpressionKind::Read { mode, .. } = &mut value.kind else {
        panic!("owned return read");
    };
    *mode = HirUseMode::Copy;
    let raw = rebuild(
        &owned,
        types,
        owned.generic_parameters().to_vec(),
        functions,
    );
    let raw_vir = lower_test(&raw).expect("raw pointer signature lowers");
    let raw_contract = &raw_vir.as_unit().specs.contracts()[0];
    assert!(raw_contract.resources.is_empty());
    assert!(raw_contract.clauses.is_empty());
    assert!(raw_vir.as_unit().specs.trust_entries().is_empty());
}

#[test]
fn raw_address_return_cannot_invent_authority_for_the_legacy_pointer_abi() {
    let base = accepted_program("fn f() -> u64 { let word = 1; return word; }");
    let mut types = base.types().to_vec();
    let mut functions = base.functions().to_vec();
    let u64_type = functions[0].body.as_ref().expect("fixture body").locals[0].ty;
    let raw_type = types
        .iter()
        .find(|definition| {
            definition.kind
                == HirTypeKind::RawPointer {
                    pointee: u64_type,
                    mutability: HirMutability::Mutable,
                }
        })
        .expect("Core0 mutable raw pointer")
        .id;
    let signature_type = functions[0].signature.ty;
    functions[0].signature.return_type = raw_type;
    types[signature_type.index()].kind = HirTypeKind::Function(HirFunctionType {
        parameters: functions[0].signature.parameters.clone(),
        return_type: raw_type,
        calling_convention: functions[0].signature.calling_convention,
    });
    let body = functions[0].body.as_mut().expect("fixture body");
    body.locals[0].mutable = true;
    let local = body.locals[0].id;
    let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[1].kind else {
        panic!("fixture return value");
    };
    value.kind = HirExpressionKind::RawAddress {
        place: Box::new(HirPlace {
            id: HirNodeId::new(0),
            base: HirPlaceBase::Local(local),
            projections: Vec::new(),
            ty: u64_type,
            span: value.span,
        }),
        mutability: HirMutability::Mutable,
    };
    value.ty = raw_type;
    let place_hir = rebuild(&base, types, base.generic_parameters().to_vec(), functions);

    assert!(lower_test(&place_hir).is_err());
}

#[test]
fn discarded_borrow_expression_cannot_leak_loan_authority() {
    let base = accepted_program("fn f() -> u64 { let word = 1; return word; }");
    let mut tables = program_tables(&base);
    let body = tables.functions[0].body.as_ref().expect("fixture body");
    let owner = tables.functions[0].id;
    let scope = body.root.scope;
    let local = body.locals[0].id;
    let u64_ty = body.locals[0].ty;
    let span = body.root.statements[1].span;
    tables.regions.push(HirRegion {
        id: HirRegionId::new(0),
        owner: HirRegionOwner::Function(owner),
        origin: HirRegionOrigin::Inferred { scope },
        span,
    });
    let (reference_ty, _) = append_concrete_type(
        &mut tables,
        "&u64",
        HirTypeKind::Reference {
            pointee: u64_ty,
            mutability: HirMutability::Const,
            region: HirRegionId::new(0),
        },
        8,
        8,
        HirAbiClass::Scalar,
        Vec::new(),
    );
    tables.functions[0]
        .body
        .as_mut()
        .expect("fixture body")
        .root
        .statements
        .insert(
            1,
            HirStatement {
                id: HirNodeId::new(0),
                kind: HirStatementKind::Evaluate {
                    expression: HirExpression {
                        id: HirNodeId::new(0),
                        kind: HirExpressionKind::Borrow {
                            place: Box::new(HirPlace {
                                id: HirNodeId::new(0),
                                base: HirPlaceBase::Local(local),
                                projections: Vec::new(),
                                ty: u64_ty,
                                span,
                            }),
                            mutability: HirMutability::Const,
                            region: HirRegionId::new(0),
                        },
                        ty: reference_ty,
                        span,
                    },
                },
                span,
            },
        );

    let hir = hir_from_tables(tables).expect("borrow mutation is valid typed HIR");
    assert!(lower_test(&hir).is_err());
}

#[test]
fn mutable_u64_local_assignment_reuses_the_ssa_slot_path() {
    let base = accepted_program("fn f() -> u64 { let word = 1; return word; }");
    let mut functions = base.functions().to_vec();
    let body = functions[0].body.as_mut().expect("fixture body");
    let local = body.locals[0].id;
    let ty = body.locals[0].ty;
    body.locals[0].mutable = true;
    let return_span = body.root.statements[1].span;
    let value_span = match &body.root.statements[1].kind {
        HirStatementKind::Return { value: Some(value) } => value.span,
        _ => panic!("fixture return"),
    };
    body.root.statements.insert(
        1,
        HirStatement {
            id: HirNodeId::new(0),
            kind: HirStatementKind::Assign {
                destination: HirPlace {
                    id: HirNodeId::new(0),
                    base: HirPlaceBase::Local(local),
                    projections: Vec::new(),
                    ty,
                    span: value_span,
                },
                value: HirExpression {
                    id: HirNodeId::new(0),
                    kind: HirExpressionKind::Integer(2),
                    ty,
                    span: value_span,
                },
            },
            span: return_span,
        },
    );
    let hir = rebuild(
        &base,
        base.types().to_vec(),
        base.generic_parameters().to_vec(),
        functions,
    );
    let vir = lower_test(&hir).expect("local assignment stays in the validated subset");
    let block = &vir.runtime().functions[0].blocks[0];
    assert!(!block.instructions.iter().any(|instruction| matches!(
        instruction.instruction,
        VirInstruction::Write { .. }
            | VirInstruction::FieldAddress { .. }
            | VirInstruction::IndexAddress { .. }
    )));
    let assigned = block
        .instructions
        .iter()
        .find_map(|instruction| match instruction.instruction {
            VirInstruction::Constant {
                result,
                value: VirConstant::U64(2),
            } => Some(result.id),
            _ => None,
        })
        .expect("assigned SSA value");
    assert!(matches!(
        block.terminator.terminator,
        VirTerminator::Return { ref values } if values == &[assigned]
    ));
}

#[test]
fn resolved_field_and_index_paths_lower_once_in_source_order() {
    let base = accepted_program(
        "fn f() -> u64 { let memory = alloc<u64>(1); *memory = 7; free(memory); return 0; }",
    );
    let mut tables = HirProgramTables {
        data_layout: base.data_layout(),
        entry_module: base.entry_module_id(),
        entry_function: base.entry_function_id(),
        modules: base.modules().to_vec(),
        types: base.types().to_vec(),
        type_capabilities: Vec::new(),
        layouts: base.layouts().to_vec(),
        fields: base.fields().to_vec(),
        variants: base.variants().to_vec(),
        generic_parameters: base.generic_parameters().to_vec(),
        regions: base.regions().to_vec(),
        region_constraints: base.region_constraints().to_vec(),
        functions: base.functions().to_vec(),
        contracts: base.contracts().to_vec(),
        predicates: base.predicates().to_vec(),
        specs: base.specs().clone(),
    };
    let u64_ty = tables
        .types
        .iter()
        .find(|ty| ty.kind == HirTypeKind::Integer(HirIntegerType::U64))
        .expect("Core0 u64 type")
        .id;
    let (usize_ty, _) = append_concrete_type(
        &mut tables,
        "usize",
        HirTypeKind::Integer(HirIntegerType::Usize),
        8,
        8,
        HirAbiClass::Scalar,
        Vec::new(),
    );
    let (array_ty, _) = append_concrete_type(
        &mut tables,
        "[u64; 4]",
        HirTypeKind::Array {
            element: u64_ty,
            length: 4,
        },
        32,
        8,
        HirAbiClass::Aggregate,
        Vec::new(),
    );
    let struct_ty = HirTypeId::new(u32::try_from(tables.types.len()).expect("small type table"));
    let field = HirFieldId::new(u32::try_from(tables.fields.len()).expect("small field table"));
    tables.fields.push(HirField {
        id: field,
        owner: struct_ty,
        name: "words".to_owned(),
        ty: array_ty,
        span: base.entry_function().span,
    });
    let (actual_struct_ty, _) = append_concrete_type(
        &mut tables,
        "Record",
        HirTypeKind::Struct {
            fields: vec![field],
        },
        40,
        8,
        HirAbiClass::Aggregate,
        vec![HirFieldLayout {
            field,
            offset_bytes: 8,
        }],
    );
    assert_eq!(actual_struct_ty, struct_ty);
    let (own_struct_ty, own_struct_layout) = append_concrete_type(
        &mut tables,
        "own<Record>",
        HirTypeKind::Own { pointee: struct_ty },
        8,
        8,
        HirAbiClass::Scalar,
        Vec::new(),
    );

    let body = tables.functions[0].body.as_mut().expect("fixture body");
    let memory = body.locals[0].id;
    body.locals[0].ty = own_struct_ty;
    body.locals[0].layout = own_struct_layout;
    let HirStatementKind::Let { value, .. } = &mut body.root.statements[0].kind else {
        panic!("fixture allocation");
    };
    value.ty = own_struct_ty;
    let HirExpressionKind::Allocate {
        element_type,
        element_count,
        size_bytes,
        alignment,
    } = &mut value.kind
    else {
        panic!("fixture allocation expression");
    };
    *element_type = struct_ty;
    *element_count = 1;
    *size_bytes = 40;
    *alignment = 8;

    let HirStatementKind::Assign { destination, .. } = &mut body.root.statements[1].kind else {
        panic!("fixture assignment");
    };
    let start = destination.span.start();
    let end = destination.span.end();
    assert!(end - start >= 3);
    let dereference_span = ByteSpan::new(start, start + 1).expect("deref span");
    let field_span = ByteSpan::new(start + 1, start + 2).expect("field span");
    let index_span = ByteSpan::new(start + 2, end).expect("index span");
    destination.base = HirPlaceBase::Local(memory);
    destination.projections = vec![
        HirProjection {
            kind: HirProjectionKind::Dereference,
            result_type: struct_ty,
            span: dereference_span,
        },
        HirProjection {
            kind: HirProjectionKind::Field { field },
            result_type: array_ty,
            span: field_span,
        },
        HirProjection {
            kind: HirProjectionKind::DynamicIndex {
                index: Box::new(HirExpression {
                    id: HirNodeId::new(0),
                    kind: HirExpressionKind::Integer(2),
                    ty: usize_ty,
                    span: index_span,
                }),
            },
            result_type: u64_ty,
            span: index_span,
        },
    ];
    destination.ty = u64_ty;

    let mut constant_tables = tables.clone();
    let HirStatementKind::Assign { destination, .. } = &mut constant_tables.functions[0]
        .body
        .as_mut()
        .expect("fixture body")
        .root
        .statements[1]
        .kind
    else {
        panic!("fixture assignment");
    };
    destination.projections[2].kind = HirProjectionKind::ConstantIndex { index: 3 };
    let mut read_place = destination.clone();
    let body = constant_tables.functions[0]
        .body
        .as_mut()
        .expect("fixture body");
    let allocation = body.root.statements[0].clone();
    let mut return_statement = body.root.statements[3].clone();
    let HirStatementKind::Return { value: Some(value) } = &mut return_statement.kind else {
        panic!("fixture return");
    };
    read_place.span = value.span;
    for projection in &mut read_place.projections {
        projection.span = value.span;
    }
    value.kind = HirExpressionKind::Read {
        place: Box::new(read_place),
        mode: HirUseMode::Copy,
    };
    value.ty = u64_ty;
    body.root.statements = vec![allocation, return_statement];

    let dynamic_hir = hir_from_tables(tables).expect("dynamic Place HIR validates");
    let dynamic = lower_test(&dynamic_hir).expect("dynamic Place reaches production lowering");
    let dynamic = dynamic.runtime();
    let instructions = &dynamic.functions[0].blocks[0].instructions;
    let field_position = instructions
        .iter()
        .position(|instruction| {
            matches!(instruction.instruction, VirInstruction::FieldAddress { .. })
        })
        .expect("field address");
    let index_operand_position = instructions
        .iter()
        .position(|instruction| {
            matches!(
                instruction.instruction,
                VirInstruction::Constant {
                    value: VirConstant::U64(2),
                    ..
                }
            )
        })
        .expect("dynamic index operand");
    let index_position = instructions
        .iter()
        .position(|instruction| {
            matches!(instruction.instruction, VirInstruction::IndexAddress { .. })
        })
        .expect("index address");
    let rhs_position = instructions
        .iter()
        .position(|instruction| {
            matches!(
                instruction.instruction,
                VirInstruction::Constant {
                    value: VirConstant::U64(7),
                    ..
                }
            )
        })
        .expect("assignment RHS");
    let write_position = instructions
        .iter()
        .position(|instruction| {
            matches!(
                instruction.instruction,
                VirInstruction::Initialize { .. } | VirInstruction::Store { .. }
            )
        })
        .expect("final write");
    assert!(
        field_position < index_operand_position
            && index_operand_position < index_position
            && index_position < rhs_position
            && rhs_position < write_position
    );
    assert_eq!(
        instructions
            .iter()
            .filter(|instruction| {
                matches!(
                    instruction.instruction,
                    VirInstruction::Constant {
                        value: VirConstant::U64(2),
                        ..
                    }
                )
            })
            .count(),
        1
    );

    let field_definition = &dynamic.memory.fields[0];
    let VirInstruction::FieldAddress {
        result: field_result,
        field: lowered_field,
        owner,
        field_access,
        offset_bytes,
        ..
    } = instructions[field_position].instruction
    else {
        unreachable!()
    };
    assert_eq!(instructions[field_position].source_span, field_span);
    assert_eq!(lowered_field, field_definition.id);
    assert_eq!(owner.ty, field_definition.owner);
    assert_eq!(field_access.ty, field_definition.ty);
    assert_eq!(offset_bytes, 8);

    let VirInstruction::IndexAddress {
        base,
        index,
        source,
        element,
        stride_bytes,
        bounds,
        ..
    } = instructions[index_position].instruction
    else {
        unreachable!()
    };
    assert_eq!(instructions[index_position].source_span, index_span);
    assert_eq!(base, field_result.id);
    assert_eq!(stride_bytes, 8);
    assert_eq!(bounds, VirIndexBounds::Array { length: 4 });
    assert_eq!(source.ty, field_definition.ty);
    assert!(matches!(
        dynamic.memory.kind(source.ty),
        Some(VirMemoryTypeKind::Array { length: 4, .. })
    ));
    assert_eq!(
        dynamic.memory.kind(element.ty),
        Some(&VirMemoryTypeKind::Integer(crate::VirIntegerType::U64))
    );
    assert!(matches!(
        &instructions[index_operand_position].instruction,
        VirInstruction::Constant { result, .. } if result.id == index
    ));
    assert!(!instructions.iter().any(|instruction| matches!(
        instruction.instruction,
        VirInstruction::PointerOffset { .. }
    )));

    let constant_hir = hir_from_tables(constant_tables).expect("constant Place HIR validates");
    let constant = lower_test(&constant_hir).expect("constant Place reaches production lowering");
    let instructions = &constant.runtime().functions[0].blocks[0].instructions;
    let constant_index = instructions
        .iter()
        .find_map(|instruction| match instruction.instruction {
            VirInstruction::Constant {
                result,
                value: VirConstant::U64(3),
            } => Some(result.id),
            _ => None,
        })
        .expect("constant index SSA value");
    let constant_address = instructions
        .iter()
        .find_map(|instruction| match instruction.instruction {
            VirInstruction::IndexAddress {
                result,
                index,
                stride_bytes: 8,
                bounds: VirIndexBounds::Array { length: 4 },
                ..
            } if index == constant_index => Some(result.id),
            _ => None,
        })
        .expect("constant index address");
    assert!(instructions.iter().any(|instruction| matches!(
        instruction.instruction,
        VirInstruction::Load {
            pointer,
            ..
        } if pointer == constant_address
    )));
}

#[test]
fn transient_slice_projection_lowers_to_explicit_pointer_length_permission() {
    let base = accepted_program(
        "fn f() -> u64 { let values = [10, 20, 30, 40]; return values[index()]; }\n\
         fn outer_start() -> usize { return 1usize; }\n\
         fn outer_end() -> usize { return 4usize; }\n\
         fn inner_start() -> usize { return 1usize; }\n\
         fn inner_end() -> usize { return 3usize; }\n\
         fn index() -> usize { return 1usize; }",
    );
    let mut tables = program_tables(&base);
    let u64_ty = tables.functions[0].signature.return_type;
    let usize_ty = tables
        .types
        .iter()
        .find(|ty| ty.kind == HirTypeKind::Integer(HirIntegerType::Usize))
        .expect("array index introduces usize")
        .id;
    let (slice_ty, _) = append_concrete_type(
        &mut tables,
        "slice<u64>",
        HirTypeKind::Slice {
            element: u64_ty,
            mutability: HirMutability::Const,
        },
        16,
        8,
        HirAbiClass::ScalarPair,
        Vec::new(),
    );
    let place_span = {
        let body = tables.functions[0].body.as_ref().expect("fixture body");
        let HirStatementKind::Return { value: Some(value) } = &body.root.statements[1].kind else {
            panic!("fixture return")
        };
        let HirExpressionKind::Read { place, .. } = &value.kind else {
            panic!("fixture indexed read")
        };
        place.span
    };
    let call = |name: &str, span: ByteSpan| {
        let function = tables
            .functions
            .iter()
            .find(|function| function.name == name)
            .expect("helper function");
        HirExpression {
            id: HirNodeId::new(0),
            kind: HirExpressionKind::Call(HirCall {
                callee: function.id,
                instantiated_signature: function.signature.clone(),
                arguments: Vec::new(),
                contract: function.contract,
                calling_convention: function.signature.calling_convention,
            }),
            ty: usize_ty,
            span,
        }
    };
    let outer_start = call("outer_start", place_span);
    let outer_end = call("outer_end", place_span);
    let inner_start = call("inner_start", place_span);
    let inner_end = call("inner_end", place_span);
    let index = call("index", place_span);
    let body = tables.functions[0].body.as_mut().expect("fixture body");
    let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[1].kind else {
        panic!("fixture return")
    };
    let HirExpressionKind::Read { place, .. } = &mut value.kind else {
        panic!("fixture indexed read")
    };
    place.projections = vec![
        HirProjection {
            kind: HirProjectionKind::Slice {
                start: Some(Box::new(outer_start)),
                end: Some(Box::new(outer_end)),
            },
            result_type: slice_ty,
            span: place.span,
        },
        HirProjection {
            kind: HirProjectionKind::Slice {
                start: Some(Box::new(inner_start)),
                end: Some(Box::new(inner_end)),
            },
            result_type: slice_ty,
            span: place.span,
        },
        HirProjection {
            kind: HirProjectionKind::DynamicIndex {
                index: Box::new(index),
            },
            result_type: u64_ty,
            span: place.span,
        },
    ];
    place.ty = u64_ty;
    value.ty = u64_ty;

    let hir = hir_from_tables(tables).expect("transient slice HIR validates");
    let vir = lower_test(&hir).expect("transient slice reaches VIR lowering");
    let instructions = &vir.runtime().functions[0].blocks[0].instructions;
    let slice_positions = instructions
        .iter()
        .enumerate()
        .filter_map(|(index, instruction)| {
            matches!(instruction.instruction, VirInstruction::SliceRange { .. }).then_some(index)
        })
        .collect::<Vec<_>>();
    assert_eq!(slice_positions.len(), 2);
    let call_positions = instructions
        .iter()
        .enumerate()
        .filter_map(|(index, instruction)| {
            matches!(instruction.instruction, VirInstruction::Call { .. }).then_some(index)
        })
        .collect::<Vec<_>>();
    assert_eq!(call_positions.len(), 5);
    let index_position = instructions
        .iter()
        .position(|instruction| {
            matches!(
                instruction.instruction,
                VirInstruction::IndexAddress {
                    bounds: VirIndexBounds::Slice { .. },
                    ..
                }
            )
        })
        .expect("slice index address");
    assert!(
        call_positions[0] < call_positions[1]
            && call_positions[1] < slice_positions[0]
            && slice_positions[0] < call_positions[2]
            && call_positions[2] < call_positions[3]
            && call_positions[3] < slice_positions[1]
            && slice_positions[1] < call_positions[4]
            && call_positions[4] < index_position
    );
    let resolved = vir.resolve().expect("slice VIR resolves");
    assert_eq!(
        interpret(resolved.runtime())
            .expect("transient slice executes")
            .values(),
        [crate::VirRuntimeValue::U64(40)]
    );
}

#[test]
fn slice_parameter_abi_carries_length_and_restores_the_source_permission() {
    let base = accepted_program(
        "fn f() -> u64 { let values = [10, 20, 30, 40]; let selected = first(values[0]); return selected + values[3]; }\n\
         fn first(value: u64) -> u64 { return value; }",
    );
    let mut tables = program_tables(&base);
    let u64_ty = tables.functions[0].signature.return_type;
    let (slice_ty, slice_layout) = append_concrete_type(
        &mut tables,
        "slice<u64>",
        HirTypeKind::Slice {
            element: u64_ty,
            mutability: HirMutability::Const,
        },
        16,
        8,
        HirAbiClass::ScalarPair,
        Vec::new(),
    );

    let callee_signature = {
        let callee = &mut tables.functions[1];
        callee.signature.parameters[0] = slice_ty;
        let signature_type = callee.signature.ty;
        tables.types[signature_type.index()].kind = HirTypeKind::Function(HirFunctionType {
            parameters: callee.signature.parameters.clone(),
            return_type: callee.signature.return_type,
            calling_convention: callee.signature.calling_convention,
        });
        let body = callee.body.as_mut().expect("slice callee body");
        let parameter = body.parameters[0];
        body.locals[parameter.index()].ty = slice_ty;
        body.locals[parameter.index()].layout = slice_layout;
        let HirStatementKind::Return { value: Some(value) } = &mut body.root.statements[0].kind
        else {
            panic!("slice callee return")
        };
        let HirExpressionKind::Read { place, .. } = &mut value.kind else {
            panic!("slice callee parameter read")
        };
        place.projections.push(HirProjection {
            kind: HirProjectionKind::ConstantIndex { index: 0 },
            result_type: u64_ty,
            span: place.span,
        });
        place.ty = u64_ty;
        callee.signature.clone()
    };

    let caller = tables.functions[0]
        .body
        .as_mut()
        .expect("slice caller body");
    let HirStatementKind::Let { value, .. } = &mut caller.root.statements[1].kind else {
        panic!("slice caller call")
    };
    let HirExpressionKind::Call(call) = &mut value.kind else {
        panic!("slice caller expression")
    };
    call.instantiated_signature = callee_signature;
    let argument = &mut call.arguments[0];
    let HirExpressionKind::Read { place, .. } = &mut argument.kind else {
        panic!("slice call argument")
    };
    place.projections = vec![HirProjection {
        kind: HirProjectionKind::Slice {
            start: None,
            end: None,
        },
        result_type: slice_ty,
        span: place.span,
    }];
    place.ty = slice_ty;
    argument.ty = slice_ty;

    let hir = hir_from_tables(tables).expect("slice ABI HIR validates");
    let vir = lower_test(&hir).expect("slice ABI reaches VIR lowering");
    let call = vir.runtime().functions[0].blocks[0]
        .instructions
        .iter()
        .find_map(|instruction| match &instruction.instruction {
            VirInstruction::Call {
                target,
                arguments,
                results,
            } if target.symbol == "first" => Some((target, arguments, results)),
            _ => None,
        })
        .expect("slice ABI call");
    assert_eq!(call.1.len(), 3);
    assert_eq!(call.2.len(), 2);
    let abi = call.0.abi.as_ref().expect("canonical slice ABI map");
    assert!(matches!(
        abi.parameters()[0].value(),
        crate::VirAbiValue::Slice { .. }
    ));
    assert_eq!(abi.parameters()[0].parameter_slots(), [0, 1, 2]);
    assert_eq!(abi.parameters()[0].result_slots(), [1]);
    let resolved = vir.resolve().expect("slice ABI resolves");
    assert_eq!(
        interpret(resolved.runtime())
            .expect("slice ABI executes")
            .values(),
        [crate::VirRuntimeValue::U64(50)]
    );
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .expect("slice ABI lowers to x86_64");
    X86_64_UNKNOWN_LINUX_GNU
        .emit_assembly(&machine)
        .expect("slice ABI machine plan emits assembly");
}

#[test]
fn bodyless_concrete_function_is_not_silently_dropped() {
    let base = accepted_program("fn f() { return; }");
    let mut modules = base.modules().to_vec();
    let mut functions = base.functions().to_vec();
    let mut imported = functions[0].clone();
    imported.id = HirFunctionId::new(1);
    imported.name = "imported".to_owned();
    imported.body = None;
    imported.contract = HirContractId::new(1);
    functions.push(imported);
    let mut contracts = base.contracts().to_vec();
    contracts.push(HirContract {
        id: HirContractId::new(1),
        function: HirFunctionId::new(1),
        is_implicit: true,
        clauses: Vec::new(),
        span: base.entry_function().span,
    });
    modules[0]
        .declarations
        .push(HirDeclaration::Function(HirFunctionId::new(1)));
    modules[0]
        .declarations
        .push(HirDeclaration::Contract(HirContractId::new(1)));
    let extended = hir_from_tables(HirProgramTables {
        data_layout: base.data_layout(),
        entry_module: base.entry_module_id(),
        entry_function: base.entry_function_id(),
        modules,
        types: base.types().to_vec(),
        type_capabilities: Vec::new(),
        layouts: base.layouts().to_vec(),
        fields: base.fields().to_vec(),
        variants: base.variants().to_vec(),
        generic_parameters: base.generic_parameters().to_vec(),
        regions: base.regions().to_vec(),
        region_constraints: base.region_constraints().to_vec(),
        functions,
        contracts,
        predicates: base.predicates().to_vec(),
        specs: base.specs().clone(),
    })
    .expect("additional function remains structurally valid HIR");

    assert!(lower_test(&extended).is_err());
}

fn lower_test(hir: &HirProgram) -> Result<ValidatedVirUnit, FrontendFailure> {
    let source_len = hir
        .functions()
        .iter()
        .map(|function| function.span.end())
        .max()
        .unwrap_or(0);
    super::lower(hir, &SourceFile::new("<lower-test>", vec![0; source_len]))
}
