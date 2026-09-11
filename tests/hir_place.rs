use nera::{
    ByteSpan, HirAbiClass, HirBoundsSource, HirExpression, HirExpressionKind, HirField, HirFieldId,
    HirFieldLayout, HirIntegerType, HirLayout, HirLayoutId, HirLocal, HirLocalId, HirMutability,
    HirPlace, HirPlaceAccess, HirPlaceBase, HirPlaceResolutionErrorKind, HirProgram,
    HirProgramTables, HirProjection, HirProjectionKind, HirRegion, HirRegionId, HirRegionOrigin,
    HirStatement, HirStatementKind, HirTypeDefinition, HirTypeId, HirTypeKind, HirUseMode,
    HirVariant, HirVariantCaseLayout, HirVariantId, HirVariantLayout, ResolvedHirProjectionKind,
    SourceFile, analyze,
};

fn base_tables() -> HirProgramTables {
    let program = analyze(&SourceFile::from_text(
        "hir-place.nera",
        "fn fixture() { return; }",
    ))
    .hir()
    .expect("fixture source is accepted")
    .clone();
    let mut tables = HirProgramTables {
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
    };
    tables.functions[0]
        .body
        .as_mut()
        .expect("fixture body")
        .root
        .span = program.entry_function().span;
    tables
}

fn from_tables(
    mut tables: HirProgramTables,
) -> Result<HirProgram, nera::HirProgramValidationError> {
    tables.assign_canonical_node_ids()?;
    tables.assign_canonical_type_capabilities()?;
    HirProgram::from_tables(tables)
}

fn span() -> ByteSpan {
    ByteSpan::new(0, 24).expect("ordered fixture span")
}

fn type_id(tables: &HirProgramTables, kind: &HirTypeKind) -> HirTypeId {
    tables
        .types
        .iter()
        .find(|definition| &definition.kind == kind)
        .expect("Core0 fixture type")
        .id
}

fn push_type(tables: &mut HirProgramTables, name: &str, kind: HirTypeKind) -> HirTypeId {
    let id = HirTypeId::new(u32::try_from(tables.types.len()).expect("small type table"));
    tables.types.push(HirTypeDefinition {
        id,
        name: Some(name.to_owned()),
        kind,
        generic_parameters: Vec::new(),
        layout: None,
    });
    id
}

fn push_inferred_region(tables: &mut HirProgramTables) -> HirRegionId {
    let id = HirRegionId::new(u32::try_from(tables.regions.len()).expect("small region table"));
    let function = &tables.functions[0];
    let scope = function.body.as_ref().expect("region body").root.scope;
    tables.regions.push(HirRegion {
        id,
        owner: nera::HirRegionOwner::Function(function.id),
        origin: HirRegionOrigin::Inferred { scope },
        span: span(),
    });
    id
}

fn attach_layout(
    tables: &mut HirProgramTables,
    ty: HirTypeId,
    size_bytes: u64,
    alignment: u64,
    abi: HirAbiClass,
    fields: Vec<HirFieldLayout>,
    variants: Option<HirVariantLayout>,
) -> HirLayoutId {
    let id = HirLayoutId::new(u32::try_from(tables.layouts.len()).expect("small layout table"));
    tables.layouts.push(HirLayout {
        id,
        ty,
        size_bytes,
        alignment,
        abi,
        fields,
        variants,
    });
    tables.types[ty.index()].layout = Some(id);
    id
}

fn push_local(
    tables: &mut HirProgramTables,
    name: &str,
    ty: HirTypeId,
    mutable: bool,
) -> HirLocalId {
    let body = tables.functions[0].body.as_mut().expect("local body");
    let id = HirLocalId::new(u32::try_from(body.locals.len()).expect("small local table"));
    body.locals.push(HirLocal {
        id,
        name: name.to_owned(),
        ty,
        layout: tables.types[ty.index()]
            .layout
            .expect("local type is sized"),
        scope: body.root.scope,
        mutable,
        declaration_span: span(),
    });
    body.root.locals.push(id);
    id
}

fn local_place(local: HirLocalId, ty: HirTypeId) -> HirPlace {
    HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(local),
        projections: Vec::new(),
        ty,
        span: span(),
    }
}

fn read(place: HirPlace) -> HirExpression {
    HirExpression {
        id: nera::HirNodeId::new(0),
        ty: place.ty,
        kind: HirExpressionKind::Read {
            place: Box::new(place),
            mode: HirUseMode::Copy,
        },
        span: span(),
    }
}

fn evaluate(expression: HirExpression) -> HirStatement {
    HirStatement {
        id: nera::HirNodeId::new(0),
        kind: HirStatementKind::Evaluate { expression },
        span: span(),
    }
}

fn integer(value: u64, ty: HirTypeId) -> HirExpression {
    HirExpression {
        id: nera::HirNodeId::new(0),
        kind: HirExpressionKind::Integer(value),
        ty,
        span: span(),
    }
}

fn dereferenced(local: HirLocalId, pointee: HirTypeId) -> HirPlace {
    HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::Dereference,
            result_type: pointee,
            span: span(),
        }],
        ty: pointee,
        span: span(),
    }
}

#[test]
fn core0_elaboration_uses_only_read_assign_and_place() {
    let output = analyze(&SourceFile::from_text(
        "core0-place.nera",
        "fn core0() -> u64 {
             let memory = alloc<u64>(1);
             *memory = 9;
             let value = *memory;
             free(memory);
             return value;
         }",
    ));
    let body = output
        .hir()
        .expect("Core0 fixture is accepted")
        .entry_function()
        .body()
        .expect("Core0 body");
    let [allocate, assign, load, free, return_] = body.root.statements.as_slice() else {
        panic!("fixture statement shape");
    };
    let HirStatementKind::Let { local: memory, .. } = allocate.kind else {
        panic!("allocation binding");
    };
    let HirStatementKind::Assign { destination, .. } = &assign.kind else {
        panic!("pointer assignment");
    };
    assert_eq!(destination.base, HirPlaceBase::Local(memory));
    assert!(matches!(
        destination.projections.as_slice(),
        [HirProjection {
            kind: HirProjectionKind::Dereference,
            ..
        }]
    ));

    let HirStatementKind::Let {
        local: value,
        value: load_value,
    } = &load.kind
    else {
        panic!("load binding");
    };
    let HirExpressionKind::Read { place, .. } = &load_value.kind else {
        panic!("dereference read");
    };
    assert_eq!(place.base, HirPlaceBase::Local(memory));
    assert!(matches!(
        place.projections.as_slice(),
        [HirProjection {
            kind: HirProjectionKind::Dereference,
            ..
        }]
    ));
    assert!(matches!(free.kind, HirStatementKind::Free { pointer } if pointer == memory));

    let HirStatementKind::Return {
        value: Some(return_value),
    } = &return_.kind
    else {
        panic!("return value");
    };
    let HirExpressionKind::Read { place, .. } = &return_value.kind else {
        panic!("local read");
    };
    assert_eq!(place.base, HirPlaceBase::Local(*value));
    assert!(place.projections.is_empty());
}

#[test]
fn read_assign_borrow_and_raw_address_are_typed_independently() {
    let mut tables = base_tables();
    let region = push_inferred_region(&mut tables);
    let u64_ty = type_id(&tables, &HirTypeKind::Integer(HirIntegerType::U64));
    let own_ty = type_id(&tables, &HirTypeKind::Own { pointee: u64_ty });
    let raw_mut_ty = type_id(
        &tables,
        &HirTypeKind::RawPointer {
            pointee: u64_ty,
            mutability: HirMutability::Mutable,
        },
    );
    let reference_ty = push_type(
        &mut tables,
        "&mut u64",
        HirTypeKind::Reference {
            pointee: u64_ty,
            mutability: HirMutability::Mutable,
            region,
        },
    );
    let pointer = push_local(&mut tables, "pointer", own_ty, false);

    tables.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements = vec![
        HirStatement {
            id: nera::HirNodeId::new(0),
            kind: HirStatementKind::Assign {
                destination: dereferenced(pointer, u64_ty),
                value: integer(11, u64_ty),
            },
            span: span(),
        },
        evaluate(read(dereferenced(pointer, u64_ty))),
        evaluate(HirExpression {
            id: nera::HirNodeId::new(0),
            kind: HirExpressionKind::Borrow {
                place: Box::new(dereferenced(pointer, u64_ty)),
                mutability: HirMutability::Mutable,
                region,
            },
            ty: reference_ty,
            span: span(),
        }),
        evaluate(HirExpression {
            id: nera::HirNodeId::new(0),
            kind: HirExpressionKind::RawAddress {
                place: Box::new(dereferenced(pointer, u64_ty)),
                mutability: HirMutability::Mutable,
            },
            ty: raw_mut_ty,
            span: span(),
        }),
    ];

    from_tables(tables).expect("all four place uses are structurally typed");
}

#[test]
fn borrow_region_must_match_the_reference_result_type() {
    let mut tables = base_tables();
    let type_region = push_inferred_region(&mut tables);
    let borrow_region = push_inferred_region(&mut tables);
    let u64_ty = type_id(&tables, &HirTypeKind::Integer(HirIntegerType::U64));
    let reference_ty = push_type(
        &mut tables,
        "&u64",
        HirTypeKind::Reference {
            pointee: u64_ty,
            mutability: HirMutability::Const,
            region: type_region,
        },
    );
    let value = push_local(&mut tables, "value", u64_ty, false);
    tables.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements
        .insert(
            0,
            evaluate(HirExpression {
                id: nera::HirNodeId::new(0),
                kind: HirExpressionKind::Borrow {
                    place: Box::new(local_place(value, u64_ty)),
                    mutability: HirMutability::Const,
                    region: borrow_region,
                },
                ty: reference_ty,
                span: span(),
            }),
        );

    let error = from_tables(tables).expect_err("region mismatch must invalidate typed HIR");
    assert_eq!(error.table(), "expression");
    assert_eq!(
        error.problem(),
        "borrow result type does not match place, mutability, and region"
    );
}

struct ProjectionFixture {
    tables: HirProgramTables,
    u64_ty: HirTypeId,
    usize_ty: HirTypeId,
    array_ty: HirTypeId,
    const_slice_ty: HirTypeId,
    struct_ty: HirTypeId,
    struct_field: HirFieldId,
    enum_ty: HirTypeId,
    enum_field: HirFieldId,
    variant: HirVariantId,
    array_local: HirLocalId,
    index_local: HirLocalId,
    struct_local: HirLocalId,
    enum_local: HirLocalId,
}

fn projection_fixture() -> ProjectionFixture {
    let mut tables = base_tables();
    let u64_ty = type_id(&tables, &HirTypeKind::Integer(HirIntegerType::U64));

    let usize_ty = push_type(
        &mut tables,
        "usize",
        HirTypeKind::Integer(HirIntegerType::Usize),
    );
    attach_layout(
        &mut tables,
        usize_ty,
        8,
        8,
        HirAbiClass::Scalar,
        vec![],
        None,
    );

    let array_ty = push_type(
        &mut tables,
        "[u64; 4]",
        HirTypeKind::Array {
            element: u64_ty,
            length: 4,
        },
    );
    attach_layout(
        &mut tables,
        array_ty,
        32,
        8,
        HirAbiClass::Aggregate,
        vec![],
        None,
    );
    let const_slice_ty = push_type(
        &mut tables,
        "[]const u64",
        HirTypeKind::Slice {
            element: u64_ty,
            mutability: HirMutability::Const,
        },
    );

    let struct_ty = HirTypeId::new(u32::try_from(tables.types.len()).expect("small table"));
    let struct_field = HirFieldId::new(u32::try_from(tables.fields.len()).expect("small table"));
    tables.fields.push(HirField {
        id: struct_field,
        owner: struct_ty,
        name: "word".to_owned(),
        ty: u64_ty,
        span: span(),
    });
    assert_eq!(
        push_type(
            &mut tables,
            "Record",
            HirTypeKind::Struct {
                fields: vec![struct_field],
            },
        ),
        struct_ty
    );
    attach_layout(
        &mut tables,
        struct_ty,
        8,
        8,
        HirAbiClass::Aggregate,
        vec![HirFieldLayout {
            field: struct_field,
            offset_bytes: 0,
        }],
        None,
    );

    let enum_ty = HirTypeId::new(u32::try_from(tables.types.len()).expect("small table"));
    let enum_field = HirFieldId::new(u32::try_from(tables.fields.len()).expect("small table"));
    tables.fields.push(HirField {
        id: enum_field,
        owner: enum_ty,
        name: "payload".to_owned(),
        ty: u64_ty,
        span: span(),
    });
    let variant = HirVariantId::new(u32::try_from(tables.variants.len()).expect("small table"));
    tables.variants.push(HirVariant {
        id: variant,
        owner: enum_ty,
        name: "Some".to_owned(),
        fields: vec![enum_field],
        discriminant: 1,
        span: span(),
    });
    assert_eq!(
        push_type(
            &mut tables,
            "MaybeWord",
            HirTypeKind::Enum {
                variants: vec![variant],
            },
        ),
        enum_ty
    );
    attach_layout(
        &mut tables,
        enum_ty,
        16,
        8,
        HirAbiClass::Aggregate,
        vec![],
        Some(HirVariantLayout {
            tag_size_bytes: 1,
            tag_alignment: 1,
            cases: vec![HirVariantCaseLayout {
                variant,
                payload_offset_bytes: 8,
                fields: vec![HirFieldLayout {
                    field: enum_field,
                    offset_bytes: 0,
                }],
            }],
        }),
    );

    let array_local = push_local(&mut tables, "array", array_ty, false);
    let index_local = push_local(&mut tables, "index", usize_ty, false);
    let struct_local = push_local(&mut tables, "record", struct_ty, false);
    let enum_local = push_local(&mut tables, "maybe", enum_ty, false);

    ProjectionFixture {
        tables,
        u64_ty,
        usize_ty,
        array_ty,
        const_slice_ty,
        struct_ty,
        struct_field,
        enum_ty,
        enum_field,
        variant,
        array_local,
        index_local,
        struct_local,
        enum_local,
    }
}

#[test]
fn every_projection_form_recomputes_its_intermediate_type() {
    let mut fixture = projection_fixture();
    let index = read(local_place(fixture.index_local, fixture.usize_ty));
    let statements = vec![
        evaluate(read(HirPlace {
            id: nera::HirNodeId::new(0),
            base: HirPlaceBase::Local(fixture.struct_local),
            projections: vec![HirProjection {
                kind: HirProjectionKind::Field {
                    field: fixture.struct_field,
                },
                result_type: fixture.u64_ty,
                span: span(),
            }],
            ty: fixture.u64_ty,
            span: span(),
        })),
        evaluate(read(HirPlace {
            id: nera::HirNodeId::new(0),
            base: HirPlaceBase::Local(fixture.array_local),
            projections: vec![HirProjection {
                kind: HirProjectionKind::ConstantIndex { index: 3 },
                result_type: fixture.u64_ty,
                span: span(),
            }],
            ty: fixture.u64_ty,
            span: span(),
        })),
        evaluate(read(HirPlace {
            id: nera::HirNodeId::new(0),
            base: HirPlaceBase::Local(fixture.array_local),
            projections: vec![HirProjection {
                kind: HirProjectionKind::DynamicIndex {
                    index: Box::new(index.clone()),
                },
                result_type: fixture.u64_ty,
                span: span(),
            }],
            ty: fixture.u64_ty,
            span: span(),
        })),
        evaluate(read(HirPlace {
            id: nera::HirNodeId::new(0),
            base: HirPlaceBase::Local(fixture.array_local),
            projections: vec![HirProjection {
                kind: HirProjectionKind::Slice {
                    start: Some(Box::new(index)),
                    end: Some(Box::new(integer(4, fixture.usize_ty))),
                },
                result_type: fixture.const_slice_ty,
                span: span(),
            }],
            ty: fixture.const_slice_ty,
            span: span(),
        })),
        evaluate(read(HirPlace {
            id: nera::HirNodeId::new(0),
            base: HirPlaceBase::Local(fixture.enum_local),
            projections: vec![
                HirProjection {
                    kind: HirProjectionKind::Downcast {
                        variant: fixture.variant,
                    },
                    result_type: fixture.enum_ty,
                    span: span(),
                },
                HirProjection {
                    kind: HirProjectionKind::Field {
                        field: fixture.enum_field,
                    },
                    result_type: fixture.u64_ty,
                    span: span(),
                },
            ],
            ty: fixture.u64_ty,
            span: span(),
        })),
    ];
    fixture.tables.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements = statements;

    from_tables(fixture.tables).expect("all projection schemas validate");
}

#[test]
fn projection_result_and_index_types_are_not_trusted() {
    let fixture = projection_fixture();
    let mut wrong_result = fixture.tables.clone();
    wrong_result.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements = vec![evaluate(read(HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::ConstantIndex { index: 0 },
            result_type: fixture.array_ty,
            span: span(),
        }],
        ty: fixture.array_ty,
        span: span(),
    }))];
    let error = from_tables(wrong_result).expect_err("forged result type must fail");
    assert_eq!(
        error.problem(),
        "place or projection result type does not match the resolved type"
    );

    let mut wrong_index = fixture.tables;
    wrong_index.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements = vec![evaluate(read(HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::DynamicIndex {
                index: Box::new(integer(0, fixture.u64_ty)),
            },
            result_type: fixture.u64_ty,
            span: span(),
        }],
        ty: fixture.u64_ty,
        span: span(),
    }))];
    let error = from_tables(wrong_index).expect_err("u64 index must fail");
    assert_eq!(
        error.problem(),
        "index projection requires a valid array or slice index"
    );
}

#[test]
fn mutable_uses_require_a_writable_place() {
    let mut tables = base_tables();
    let u64_ty = type_id(&tables, &HirTypeKind::Integer(HirIntegerType::U64));
    let raw_mut_ty = type_id(
        &tables,
        &HirTypeKind::RawPointer {
            pointee: u64_ty,
            mutability: HirMutability::Mutable,
        },
    );
    let immutable = push_local(&mut tables, "word", u64_ty, false);
    tables.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements = vec![evaluate(HirExpression {
        id: nera::HirNodeId::new(0),
        kind: HirExpressionKind::RawAddress {
            place: Box::new(local_place(immutable, u64_ty)),
            mutability: HirMutability::Mutable,
        },
        ty: raw_mut_ty,
        span: span(),
    })];
    let error = from_tables(tables).expect_err("mutable address must fail");
    assert_eq!(
        error.problem(),
        "place is not writable for the requested access"
    );

    let mut borrow_tables = base_tables();
    let region = push_inferred_region(&mut borrow_tables);
    let u64_ty = type_id(&borrow_tables, &HirTypeKind::Integer(HirIntegerType::U64));
    let reference_ty = push_type(
        &mut borrow_tables,
        "&mut u64",
        HirTypeKind::Reference {
            pointee: u64_ty,
            mutability: HirMutability::Mutable,
            region,
        },
    );
    let immutable = push_local(&mut borrow_tables, "word", u64_ty, false);
    borrow_tables.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements = vec![evaluate(HirExpression {
        id: nera::HirNodeId::new(0),
        kind: HirExpressionKind::Borrow {
            place: Box::new(local_place(immutable, u64_ty)),
            mutability: HirMutability::Mutable,
            region,
        },
        ty: reference_ty,
        span: span(),
    })];
    let error = from_tables(borrow_tables).expect_err("mutable borrow must require write access");
    assert_eq!(
        error.problem(),
        "place is not writable for the requested access"
    );
}

#[test]
fn final_type_owner_bounds_and_spans_are_checked() {
    let fixture = projection_fixture();

    let mut wrong_final = fixture.tables.clone();
    wrong_final.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements = vec![evaluate(read(HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::ConstantIndex { index: 0 },
            result_type: fixture.u64_ty,
            span: span(),
        }],
        ty: fixture.array_ty,
        span: span(),
    }))];
    let error = from_tables(wrong_final).expect_err("forged final type must fail");
    assert_eq!(
        error.problem(),
        "place or projection result type does not match the resolved type"
    );

    let mut foreign_field = fixture.tables.clone();
    foreign_field.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements = vec![evaluate(read(HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.struct_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::Field {
                field: fixture.enum_field,
            },
            result_type: fixture.u64_ty,
            span: span(),
        }],
        ty: fixture.u64_ty,
        span: span(),
    }))];
    let error = from_tables(foreign_field).expect_err("foreign field must fail");
    assert_eq!(
        error.problem(),
        "field projection does not belong to the current aggregate"
    );

    let mut out_of_bounds = fixture.tables.clone();
    out_of_bounds.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements = vec![evaluate(read(HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::ConstantIndex { index: 4 },
            result_type: fixture.u64_ty,
            span: span(),
        }],
        ty: fixture.u64_ty,
        span: span(),
    }))];
    let error = from_tables(out_of_bounds).expect_err("static OOB must fail");
    assert_eq!(
        error.problem(),
        "index projection requires a valid array or slice index"
    );

    let narrow_span = ByteSpan::new(0, 1).expect("ordered span");
    let mut outside_span = fixture.tables;
    outside_span.functions[0]
        .body
        .as_mut()
        .expect("body")
        .root
        .statements = vec![evaluate(read(HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::ConstantIndex { index: 0 },
            result_type: fixture.u64_ty,
            span: span(),
        }],
        ty: fixture.u64_ty,
        span: narrow_span,
    }))];
    let error = from_tables(outside_span).expect_err("outside span must fail");
    assert_eq!(
        error.problem(),
        "projection operand span is outside its parent span"
    );
}

#[test]
fn layout_resolver_canonicalizes_offsets_strides_bounds_and_downcasts() {
    let fixture = projection_fixture();
    let function = fixture.tables.entry_function;
    let program = from_tables(fixture.tables).expect("projection fixture program");

    let array_place = HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::ConstantIndex { index: 2 },
            result_type: fixture.u64_ty,
            span: span(),
        }],
        ty: fixture.u64_ty,
        span: span(),
    };
    let resolved = program
        .resolve_place(function, &array_place, HirPlaceAccess::Read)
        .expect("constant array index resolves");
    assert_eq!(resolved.static_offset_bytes, Some(16));
    assert_eq!(resolved.required_alignment, 8);
    assert!(matches!(
        resolved.projections[0].kind,
        ResolvedHirProjectionKind::ConstantIndex {
            index: 2,
            bounds: HirBoundsSource::Array { length: 4 },
            stride_bytes: 8,
            offset_bytes: 16,
        }
    ));

    let dynamic_place = HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::DynamicIndex {
                index: Box::new(read(local_place(fixture.index_local, fixture.usize_ty))),
            },
            result_type: fixture.u64_ty,
            span: span(),
        }],
        ty: fixture.u64_ty,
        span: span(),
    };
    let resolved = program
        .resolve_place(function, &dynamic_place, HirPlaceAccess::Read)
        .expect("dynamic array index resolves");
    assert_eq!(resolved.static_offset_bytes, None);
    assert!(matches!(
        &resolved.projections[0].kind,
        ResolvedHirProjectionKind::DynamicIndex {
            index,
            bounds: HirBoundsSource::Array { length: 4 },
            stride_bytes: 8,
        } if index.ty == fixture.usize_ty
    ));

    let slice_place = HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::Slice {
                start: Some(Box::new(read(local_place(
                    fixture.index_local,
                    fixture.usize_ty,
                )))),
                end: None,
            },
            result_type: fixture.const_slice_ty,
            span: span(),
        }],
        ty: fixture.const_slice_ty,
        span: span(),
    };
    let resolved = program
        .resolve_place(function, &slice_place, HirPlaceAccess::Read)
        .expect("array slice resolves");
    assert_eq!(resolved.static_offset_bytes, None);
    assert!(matches!(
        &resolved.projections[0].kind,
        ResolvedHirProjectionKind::Slice {
            start: Some(start),
            end: None,
            bounds: HirBoundsSource::Array { length: 4 },
            stride_bytes: 8,
            mutability: HirMutability::Const,
        } if start.ty == fixture.usize_ty
    ));

    let enum_place = HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.enum_local),
        projections: vec![
            HirProjection {
                kind: HirProjectionKind::Downcast {
                    variant: fixture.variant,
                },
                result_type: fixture.enum_ty,
                span: span(),
            },
            HirProjection {
                kind: HirProjectionKind::Field {
                    field: fixture.enum_field,
                },
                result_type: fixture.u64_ty,
                span: span(),
            },
        ],
        ty: fixture.u64_ty,
        span: span(),
    };
    let resolved = program
        .resolve_place(function, &enum_place, HirPlaceAccess::Read)
        .expect("enum payload field resolves");
    assert_eq!(resolved.static_offset_bytes, Some(8));
    assert!(matches!(
        resolved.projections[0].kind,
        ResolvedHirProjectionKind::Downcast {
            variant,
            payload_offset_bytes: 8,
        } if variant == fixture.variant
    ));
    assert!(matches!(
        resolved.projections[1].kind,
        ResolvedHirProjectionKind::Field {
            field,
            offset_bytes: 0,
        } if field == fixture.enum_field
    ));
}

#[test]
fn layout_resolver_fails_closed_on_immutable_unresolved_and_overflowing_places() {
    let fixture = projection_fixture();
    let function = fixture.tables.entry_function;
    let immutable_place = local_place(fixture.struct_local, fixture.struct_ty);
    let program = from_tables(fixture.tables).expect("projection fixture program");
    let error = program
        .resolve_place(function, &immutable_place, HirPlaceAccess::Write)
        .expect_err("immutable local write must fail");
    assert_eq!(error.kind(), HirPlaceResolutionErrorKind::ImmutableWrite);

    let invalid_dereference = HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.struct_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::Dereference,
            result_type: fixture.struct_ty,
            span: span(),
        }],
        ty: fixture.struct_ty,
        span: span(),
    };
    let error = program
        .resolve_place(function, &invalid_dereference, HirPlaceAccess::Read)
        .expect_err("non-pointer dereference must fail");
    assert_eq!(
        error.kind(),
        HirPlaceResolutionErrorKind::InvalidDereference
    );

    let invalid_downcast = HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.struct_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::Downcast {
                variant: fixture.variant,
            },
            result_type: fixture.struct_ty,
            span: span(),
        }],
        ty: fixture.struct_ty,
        span: span(),
    };
    let error = program
        .resolve_place(function, &invalid_downcast, HirPlaceAccess::Read)
        .expect_err("foreign downcast must fail");
    assert_eq!(error.kind(), HirPlaceResolutionErrorKind::InvalidDowncast);

    let mut fixture = projection_fixture();
    let function = fixture.tables.entry_function;
    fixture.tables.types[fixture.array_ty.index()].kind = HirTypeKind::Array {
        element: fixture.const_slice_ty,
        length: 4,
    };
    let unresolved_place = HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::ConstantIndex { index: 0 },
            result_type: fixture.const_slice_ty,
            span: span(),
        }],
        ty: fixture.const_slice_ty,
        span: span(),
    };
    let program = from_tables(fixture.tables).expect("unresolved element is structural");
    let error = program
        .resolve_place(function, &unresolved_place, HirPlaceAccess::Read)
        .expect_err("unresolved element layout must fail");
    assert_eq!(error.kind(), HirPlaceResolutionErrorKind::MissingLayout);

    let mut fixture = projection_fixture();
    let function = fixture.tables.entry_function;
    let array_layout = fixture.tables.types[fixture.array_ty.index()]
        .layout
        .expect("array layout");
    fixture.tables.layouts[array_layout.index()].size_bytes = 24;
    let inconsistent_place = HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::ConstantIndex { index: 0 },
            result_type: fixture.u64_ty,
            span: span(),
        }],
        ty: fixture.u64_ty,
        span: span(),
    };
    let program = from_tables(fixture.tables).expect("array shape is resolver-owned");
    let error = program
        .resolve_place(function, &inconsistent_place, HirPlaceAccess::Read)
        .expect_err("inconsistent array size must fail");
    assert_eq!(error.kind(), HirPlaceResolutionErrorKind::InvalidLayout);

    let mut fixture = projection_fixture();
    let function = fixture.tables.entry_function;
    fixture.tables.types[fixture.array_ty.index()].kind = HirTypeKind::Array {
        element: fixture.u64_ty,
        length: u64::MAX,
    };
    let overflowing_place = HirPlace {
        id: nera::HirNodeId::new(0),
        base: HirPlaceBase::Local(fixture.array_local),
        projections: vec![HirProjection {
            kind: HirProjectionKind::ConstantIndex { index: 0 },
            result_type: fixture.u64_ty,
            span: span(),
        }],
        ty: fixture.u64_ty,
        span: span(),
    };
    let program = from_tables(fixture.tables).expect("overflow is resolver-local");
    let error = program
        .resolve_place(function, &overflowing_place, HirPlaceAccess::Read)
        .expect_err("array layout multiplication must not wrap");
    assert_eq!(
        error.kind(),
        HirPlaceResolutionErrorKind::ArithmeticOverflow
    );
}
