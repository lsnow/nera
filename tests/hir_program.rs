use nera::{
    DropCapability, HirAbiClass, HirDeclaration, HirEndianness, HirField, HirFieldId,
    HirFieldLayout, HirFunctionType, HirGenericParameter, HirGenericParameterId, HirIntegerType,
    HirLayout, HirLayoutId, HirModuleId, HirMutability, HirPredicate, HirPredicateId, HirProgram,
    HirProgramTables, HirRegion, HirRegionId, HirRegionOrigin, HirTargetDataLayout,
    HirTypeDefinition, HirTypeId, HirTypeKind, HirVariant, HirVariantCaseLayout, HirVariantId,
    HirVariantLayout, SizeCapability, SourceFile, ValueCapability, analyze,
};

fn accepted_program(source: &str) -> HirProgram {
    analyze(&SourceFile::from_text("hir-program.nera", source))
        .hir()
        .expect("fixture source is accepted")
        .clone()
}

fn tables(program: &HirProgram) -> HirProgramTables {
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
fn deferred_declaration_validation_rejects_immutable_and_duplicate_storage() {
    let program =
        accepted_program("fn main() -> u64 { let mut value: u64; value = 42; return value; }");
    let mut immutable = tables(&program);
    immutable.functions[0].body.as_mut().unwrap().locals[0].mutable = false;
    assert!(HirProgram::from_tables(immutable).is_err());
    let mut duplicate = tables(&program);
    let body = duplicate.functions[0].body.as_mut().unwrap();
    let mut declaration = body.root.statements[0].clone();
    declaration.id = body.root.statements[1].id;
    body.root.statements[1] = declaration;
    assert!(HirProgram::from_tables(duplicate).is_err());
}

fn push_type(types: &mut Vec<HirTypeDefinition>, name: &str, kind: HirTypeKind) -> HirTypeId {
    let id = HirTypeId::new(u32::try_from(types.len()).expect("small test type table"));
    types.push(HirTypeDefinition {
        id,
        name: Some(name.to_owned()),
        kind,
        generic_parameters: Vec::new(),
        layout: None,
    });
    id
}

fn program_covering_the_hir_type_model() -> HirProgram {
    let base = accepted_program("fn all_types() { return; }");
    let mut tables = tables(&base);
    let span = base.entry_function().span;
    let u64_type = base
        .types()
        .iter()
        .find(|definition| definition.kind == HirTypeKind::Integer(HirIntegerType::U64))
        .expect("Core0 u64 type")
        .id;
    let root = &base.entry_function().body().expect("fixture body").root;
    tables.regions.push(HirRegion {
        id: HirRegionId::new(0),
        owner: nera::HirRegionOwner::Function(base.entry_function().id),
        origin: HirRegionOrigin::LexicalScope { scope: root.scope },
        span: root.span,
    });

    for integer in [
        HirIntegerType::U8,
        HirIntegerType::U16,
        HirIntegerType::U32,
        HirIntegerType::U64,
        HirIntegerType::U128,
        HirIntegerType::Usize,
        HirIntegerType::I8,
        HirIntegerType::I16,
        HirIntegerType::I32,
        HirIntegerType::I64,
        HirIntegerType::I128,
        HirIntegerType::Isize,
    ] {
        push_type(
            &mut tables.types,
            &format!("integer-{integer:?}"),
            HirTypeKind::Integer(integer),
        );
    }

    push_type(
        &mut tables.types,
        "*const u64",
        HirTypeKind::RawPointer {
            pointee: u64_type,
            mutability: HirMutability::Const,
        },
    );
    for mutability in [HirMutability::Const, HirMutability::Mutable] {
        push_type(
            &mut tables.types,
            &format!("reference-{mutability:?}"),
            HirTypeKind::Reference {
                pointee: u64_type,
                mutability,
                region: HirRegionId::new(0),
            },
        );
    }
    let array = push_type(
        &mut tables.types,
        "[u64; 4]",
        HirTypeKind::Array {
            element: u64_type,
            length: 4,
        },
    );
    for mutability in [HirMutability::Const, HirMutability::Mutable] {
        push_type(
            &mut tables.types,
            &format!("slice-{mutability:?}"),
            HirTypeKind::Slice {
                element: u64_type,
                mutability,
            },
        );
    }
    push_type(
        &mut tables.types,
        "tuple",
        HirTypeKind::Tuple(vec![u64_type, array]),
    );

    let struct_type =
        HirTypeId::new(u32::try_from(tables.types.len()).expect("small test type table"));
    let struct_field =
        HirFieldId::new(u32::try_from(tables.fields.len()).expect("small test field table"));
    tables.fields.push(HirField {
        id: struct_field,
        owner: struct_type,
        name: "value".to_owned(),
        ty: u64_type,
        span,
    });
    let pushed_struct = push_type(
        &mut tables.types,
        "Record",
        HirTypeKind::Struct {
            fields: vec![struct_field],
        },
    );
    assert_eq!(pushed_struct, struct_type);

    let enum_type =
        HirTypeId::new(u32::try_from(tables.types.len()).expect("small test type table"));
    let enum_field =
        HirFieldId::new(u32::try_from(tables.fields.len()).expect("small test field table"));
    tables.fields.push(HirField {
        id: enum_field,
        owner: enum_type,
        name: "payload".to_owned(),
        ty: u64_type,
        span,
    });
    let variant =
        HirVariantId::new(u32::try_from(tables.variants.len()).expect("small test variant table"));
    tables.variants.push(HirVariant {
        id: variant,
        owner: enum_type,
        name: "Some".to_owned(),
        fields: vec![enum_field],
        discriminant: 1,
        span,
    });
    let pushed_enum = push_type(
        &mut tables.types,
        "MaybeWord",
        HirTypeKind::Enum {
            variants: vec![variant],
        },
    );
    assert_eq!(pushed_enum, enum_type);

    let generic_parameter = HirGenericParameterId::new(
        u32::try_from(tables.generic_parameters.len()).expect("small test generic parameter table"),
    );
    tables.generic_parameters.push(HirGenericParameter {
        id: generic_parameter,
        name: "T".to_owned(),
        span,
    });
    push_type(
        &mut tables.types,
        "T",
        HirTypeKind::GenericParameter(generic_parameter),
    );
    push_type(&mut tables.types, "never", HirTypeKind::Never);
    push_type(
        &mut tables.types,
        "fn(u64) -> u64",
        HirTypeKind::Function(HirFunctionType {
            parameters: vec![u64_type],
            return_type: u64_type,
            calling_convention: nera::HirCallingConvention::Nera,
        }),
    );

    let struct_layout =
        HirLayoutId::new(u32::try_from(tables.layouts.len()).expect("small test layout table"));
    tables.layouts.push(HirLayout {
        id: struct_layout,
        ty: struct_type,
        size_bytes: 8,
        alignment: 8,
        abi: HirAbiClass::Aggregate,
        fields: vec![HirFieldLayout {
            field: struct_field,
            offset_bytes: 0,
        }],
        variants: None,
    });
    tables.types[struct_type.index()].layout = Some(struct_layout);

    let enum_layout =
        HirLayoutId::new(u32::try_from(tables.layouts.len()).expect("small test layout table"));
    tables.layouts.push(HirLayout {
        id: enum_layout,
        ty: enum_type,
        size_bytes: 16,
        alignment: 8,
        abi: HirAbiClass::Aggregate,
        fields: Vec::new(),
        variants: Some(HirVariantLayout {
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
    });
    tables.types[enum_type.index()].layout = Some(enum_layout);

    tables.modules[0]
        .declarations
        .push(HirDeclaration::Type(struct_type));
    tables.modules[0]
        .declarations
        .push(HirDeclaration::Type(enum_type));
    let predicate = HirPredicateId::new(
        u32::try_from(tables.predicates.len()).expect("small test predicate table"),
    );
    tables.predicates.push(HirPredicate {
        id: predicate,
        module: HirModuleId::new(0),
        name: "is_word".to_owned(),
        binders: Vec::new(),
        body: None,
        span,
    });
    tables.modules[0]
        .declarations
        .push(HirDeclaration::Predicate(predicate));

    tables
        .assign_canonical_type_capabilities()
        .expect("complete type model has canonical capabilities");
    HirProgram::from_tables(tables).expect("the complete HIR type model is structurally valid")
}

#[test]
fn every_hir_type_kind_and_integer_family_is_accepted() {
    let program = program_covering_the_hir_type_model();

    for integer in [
        HirIntegerType::U8,
        HirIntegerType::U16,
        HirIntegerType::U32,
        HirIntegerType::U64,
        HirIntegerType::U128,
        HirIntegerType::Usize,
        HirIntegerType::I8,
        HirIntegerType::I16,
        HirIntegerType::I32,
        HirIntegerType::I64,
        HirIntegerType::I128,
        HirIntegerType::Isize,
    ] {
        assert!(
            program
                .types()
                .iter()
                .any(|definition| definition.kind == HirTypeKind::Integer(integer))
        );
    }
    assert!(
        program
            .types()
            .iter()
            .any(|definition| matches!(definition.kind, HirTypeKind::Reference { .. }))
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| matches!(definition.kind, HirTypeKind::Own { .. }))
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| matches!(definition.kind, HirTypeKind::RawPointer { .. }))
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| matches!(definition.kind, HirTypeKind::Array { .. }))
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| matches!(definition.kind, HirTypeKind::Slice { .. }))
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| matches!(definition.kind, HirTypeKind::Tuple(_)))
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| matches!(definition.kind, HirTypeKind::Struct { .. }))
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| matches!(definition.kind, HirTypeKind::Enum { .. }))
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| matches!(definition.kind, HirTypeKind::GenericParameter(_)))
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| matches!(definition.kind, HirTypeKind::Function(_)))
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| definition.kind == HirTypeKind::Unit)
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| definition.kind == HirTypeKind::Bool)
    );
    assert!(
        program
            .types()
            .iter()
            .any(|definition| definition.kind == HirTypeKind::Never)
    );
    assert!(program.layout_of(program.fields()[0].owner).is_some());
    assert!(program.predicate(HirPredicateId::new(0)).is_some());
}

#[test]
fn canonical_type_capabilities_cover_resources_and_reject_mutation() {
    let program = accepted_program(include_str!("../spec/cases/control-flow/owned-call.nera"));
    let find = |kind: &dyn Fn(&HirTypeKind) -> bool| {
        program
            .types()
            .iter()
            .find(|ty| kind(&ty.kind))
            .expect("requested core type")
    };
    let word = find(&|kind| matches!(kind, HirTypeKind::Integer(HirIntegerType::U64)));
    let own = find(&|kind| matches!(kind, HirTypeKind::Own { .. }));
    let raw = find(&|kind| matches!(kind, HirTypeKind::RawPointer { .. }));
    let function = find(&|kind| matches!(kind, HirTypeKind::Function(_)));

    let word_capability = program.type_capabilities(word.id).unwrap();
    assert_eq!(word_capability.value, ValueCapability::Copy);
    assert_eq!(word_capability.drop, DropCapability::TrivialDrop);
    assert!(!word_capability.contains_resource);
    assert_eq!(word_capability.size, SizeCapability::Sized);

    let own_capability = program.type_capabilities(own.id).unwrap();
    assert_eq!(own_capability.value, ValueCapability::MoveOnly);
    assert_eq!(own_capability.drop, DropCapability::BuiltinDrop);
    assert!(own_capability.contains_resource);

    let raw_capability = program.type_capabilities(raw.id).unwrap();
    assert_eq!(raw_capability.value, ValueCapability::Copy);
    assert_eq!(raw_capability.drop, DropCapability::TrivialDrop);
    assert!(raw_capability.contains_resource);

    assert_eq!(
        program.type_capabilities(function.id).unwrap().size,
        SizeCapability::Unsized
    );

    let mut mutated = tables(&program);
    mutated.type_capabilities[word.id.index()].value = ValueCapability::MoveOnly;
    let error = HirProgram::from_tables(mutated).expect_err("capability mutation must fail");
    assert_eq!(error.table(), "type capability");
    assert_eq!(error.index(), word.id.index());
}

#[test]
fn entity_ids_and_table_order_are_deterministic() {
    let source = "fn deterministic() { let memory = alloc<u64>(2); let next = memory + 8; free(memory); return; }";
    let expected = accepted_program(source);

    for _ in 0..32 {
        assert_eq!(accepted_program(source), expected);
    }
}

#[test]
fn entry_function_must_belong_to_the_entry_module() {
    let base = accepted_program("fn entry() { return; }");
    let mut tables = tables(&base);
    tables.functions[0].module = HirModuleId::new(1);

    let error = HirProgram::from_tables(tables).expect_err("foreign entry function must fail");
    assert_eq!(error.table(), "program");
    assert_eq!(
        error.problem(),
        "entry function is outside the entry module"
    );
}

#[test]
fn target_word_sizes_must_be_compatible_with_their_alignment() {
    let base = accepted_program("fn entry() { return; }");
    let mut tables = tables(&base);
    tables.data_layout = HirTargetDataLayout {
        endianness: HirEndianness::Little,
        pointer_size_bytes: 8,
        pointer_alignment: 8,
        usize_size_bytes: 6,
        usize_alignment: 4,
    };

    let error = HirProgram::from_tables(tables).expect_err("invalid target layout must fail");
    assert_eq!(error.table(), "data layout");
}

#[test]
fn every_layout_must_be_selected_by_exactly_its_source_type() {
    let base = accepted_program("fn entry() { return; }");
    let mut tables = tables(&base);
    let u64_layout = tables
        .layouts
        .iter()
        .find(|layout| {
            tables.types[layout.ty.index()].kind == HirTypeKind::Integer(HirIntegerType::U64)
        })
        .expect("Core0 u64 layout")
        .clone();
    let mut unselected = u64_layout;
    unselected.id =
        HirLayoutId::new(u32::try_from(tables.layouts.len()).expect("small test layout table"));
    tables.layouts.push(unselected);

    let error = HirProgram::from_tables(tables).expect_err("unselected layout must fail");
    assert_eq!(error.table(), "layout");
    assert_eq!(error.problem(), "source type does not select this layout");
}

#[test]
fn module_declarations_are_unique_and_owned() {
    let base = accepted_program("fn entry() { return; }");
    let mut tables = tables(&base);
    let duplicate = tables.modules[0].declarations[0];
    tables.modules[0].declarations.push(duplicate);

    let error = HirProgram::from_tables(tables).expect_err("duplicate declaration must fail");
    assert_eq!(error.table(), "module");
    assert_eq!(error.problem(), "duplicate declaration");
}

#[test]
fn module_paths_are_unique() {
    let base = accepted_program("fn entry() { return; }");
    let mut tables = tables(&base);
    let mut duplicate = tables.modules[0].clone();
    duplicate.id = HirModuleId::new(1);
    duplicate.declarations.clear();
    tables.modules.push(duplicate);

    let error = HirProgram::from_tables(tables).expect_err("duplicate module path must fail");
    assert_eq!(error.table(), "module");
    assert_eq!(error.problem(), "duplicate module path");
}

#[test]
fn body_references_cannot_bypass_the_program_boundary() {
    let base = accepted_program("fn entry() { let memory = alloc<u64>(1); return; }");
    let mut tables = tables(&base);
    let body = tables.functions[0].body.as_mut().expect("fixture body");
    let nera::HirStatementKind::Let { local, .. } = &mut body.root.statements[0].kind else {
        panic!("fixture let statement");
    };
    *local = nera::HirLocalId::new(99);

    let error = HirProgram::from_tables(tables).expect_err("dangling body ID must fail");
    assert_eq!(error.table(), "statement");
    assert_eq!(
        error.problem(),
        "let target is foreign, special, or initialized more than once"
    );
}

#[test]
fn field_and_variant_ownership_is_bidirectional() {
    let valid = program_covering_the_hir_type_model();
    let mut tables = tables(&valid);
    let enum_owner = tables.variants[0].owner;
    tables.fields[0].owner = enum_owner;

    let error = HirProgram::from_tables(tables).expect_err("foreign struct field must fail");
    assert!(matches!(error.table(), "type" | "layout" | "field"));
}

#[test]
fn aggregate_alignment_cannot_understate_a_field_requirement() {
    let valid = program_covering_the_hir_type_model();
    let mut tables = tables(&valid);
    let struct_layout = tables
        .layouts
        .iter_mut()
        .find(|layout| !layout.fields.is_empty())
        .expect("fixture struct layout");
    struct_layout.alignment = 4;

    let error = HirProgram::from_tables(tables).expect_err("under-aligned aggregate must fail");
    assert_eq!(error.table(), "layout");
    assert_eq!(
        error.problem(),
        "field layout exceeds aggregate size or is unresolved"
    );
}

#[test]
fn nonzero_struct_fields_cannot_overlap() {
    let valid = program_covering_the_hir_type_model();
    let mut tables = tables(&valid);
    let struct_layout_index = tables
        .layouts
        .iter()
        .position(|layout| !layout.fields.is_empty())
        .expect("fixture struct layout");
    let struct_type = tables.layouts[struct_layout_index].ty;
    let first_field = tables.layouts[struct_layout_index].fields[0].field;
    let overlapping_field =
        HirFieldId::new(u32::try_from(tables.fields.len()).expect("small test field table"));
    let mut field = tables.fields[first_field.index()].clone();
    field.id = overlapping_field;
    field.name = "overlapping".to_owned();
    tables.fields.push(field);
    let HirTypeKind::Struct { fields } = &mut tables.types[struct_type.index()].kind else {
        panic!("fixture struct type");
    };
    fields.push(overlapping_field);
    tables.layouts[struct_layout_index]
        .fields
        .push(HirFieldLayout {
            field: overlapping_field,
            offset_bytes: 0,
        });

    let error = HirProgram::from_tables(tables).expect_err("overlapping fields must fail");
    assert_eq!(error.table(), "layout");
    assert_eq!(error.problem(), "aggregate field layouts overlap");
}

#[test]
fn enum_payload_cannot_overlap_its_explicit_tag() {
    let valid = program_covering_the_hir_type_model();
    let mut tables = tables(&valid);
    let variant_layout = tables
        .layouts
        .iter_mut()
        .find_map(|layout| layout.variants.as_mut())
        .expect("fixture enum layout");
    variant_layout.cases[0].payload_offset_bytes = 0;

    let error = HirProgram::from_tables(tables).expect_err("tag/payload overlap must fail");
    assert_eq!(error.table(), "layout");
    assert_eq!(error.problem(), "invalid enum variant case");
}
