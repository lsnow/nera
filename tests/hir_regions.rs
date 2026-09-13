use nera::{
    ByteSpan, HirExpression, HirExpressionKind, HirFunctionId, HirFunctionType, HirMutability,
    HirNodeId, HirPlace, HirPlaceBase, HirProgram, HirProgramTables, HirRegion,
    HirRegionConstraint, HirRegionConstraintId, HirRegionId, HirRegionOrigin, HirScopeId,
    HirStatement, HirStatementKind, HirTypeDefinition, HirTypeId, HirTypeKind, HirVersion,
    SourceFile, analyze,
};

fn accepted_program(source: &str) -> HirProgram {
    analyze(&SourceFile::from_text("hir-regions.nera", source))
        .hir()
        .expect("fixture source is accepted")
        .clone()
}

fn program_tables(program: &HirProgram) -> HirProgramTables {
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
fn logical_borrow_results_validate_source_result_access_and_owner() {
    let base = accepted_program(
        "fn main()->u64{let x=42;let r=id(7,&x);return *r;} fn id(n:u64,r:&u64)->&u64{return r;}",
    );
    assert_eq!(
        base.functions()[1].signature.borrow_result,
        Some(nera::BorrowResultRelation::whole(
            1,
            nera::BorrowAccess::Shared
        ))
    );
    for mutation in 0..5 {
        let mut tables = program_tables(&base);
        match mutation {
            0 => tables.functions[1].signature.borrow_result = None,
            1 => {
                tables.functions[1]
                    .signature
                    .borrow_result
                    .as_mut()
                    .unwrap()
                    .parameter = 0
            }
            2 => {
                tables.functions[1]
                    .signature
                    .borrow_result
                    .as_mut()
                    .unwrap()
                    .result = 1
            }
            3 => {
                tables.functions[1]
                    .signature
                    .borrow_result
                    .as_mut()
                    .unwrap()
                    .access = nera::BorrowAccess::Mutable
            }
            _ => {
                let region = tables
                    .regions
                    .iter_mut()
                    .find(|r| r.owner == nera::HirRegionOwner::Function(HirFunctionId::new(1)))
                    .unwrap();
                region.owner = nera::HirRegionOwner::Function(HirFunctionId::new(0));
            }
        }
        assert!(
            HirProgram::from_tables(tables).is_err(),
            "mutation {mutation}"
        );
    }
}

fn validate(mut tables: HirProgramTables) -> Result<HirProgram, nera::HirProgramValidationError> {
    tables.assign_canonical_node_ids()?;
    tables.assign_canonical_type_capabilities()?;
    HirProgram::from_tables(tables)
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

fn signature_region_tables() -> HirProgramTables {
    let base = accepted_program("fn identity(value: u64) -> u64 { return value; }");
    let mut tables = program_tables(&base);
    let function = &tables.functions[0];
    let owner = function.id;
    let span = function.span;
    let signature_ty = function.signature.ty;
    let u64_ty = function.signature.parameters[0];
    let calling_convention = function.signature.calling_convention;

    let parameter_ty = push_type(
        &mut tables,
        "&'parameter u64",
        HirTypeKind::Reference {
            pointee: u64_ty,
            mutability: HirMutability::Const,
            region: HirRegionId::new(0),
        },
    );
    let result_ty = push_type(
        &mut tables,
        "&'result u64",
        HirTypeKind::Reference {
            pointee: u64_ty,
            mutability: HirMutability::Const,
            region: HirRegionId::new(1),
        },
    );
    tables.types[signature_ty.index()].kind = HirTypeKind::Function(HirFunctionType {
        parameters: vec![parameter_ty],
        return_type: result_ty,
        calling_convention,
    });
    tables.functions[0].signature.parameters = vec![parameter_ty];
    tables.functions[0].signature.return_type = result_ty;
    tables.functions[0].signature.borrow_result = Some(nera::BorrowResultRelation::whole(
        0,
        nera::BorrowAccess::Shared,
    ));
    tables.functions[0].body = None;
    tables.regions = vec![
        HirRegion {
            id: HirRegionId::new(0),
            owner: nera::HirRegionOwner::Function(owner),
            origin: HirRegionOrigin::Parameter { index: 0 },
            span,
        },
        HirRegion {
            id: HirRegionId::new(1),
            owner: nera::HirRegionOwner::Function(owner),
            origin: HirRegionOrigin::Result,
            span,
        },
    ];
    tables.region_constraints = vec![HirRegionConstraint {
        id: HirRegionConstraintId::new(0),
        owner,
        subregion: HirRegionId::new(1),
        superregion: HirRegionId::new(0),
        span,
    }];
    tables
}

fn local_borrow_tables() -> HirProgramTables {
    let base = accepted_program("fn local() -> u64 { let value = 1; return value; }");
    let mut tables = program_tables(&base);
    let body = tables.functions[0].body.as_ref().expect("fixture body");
    let owner = tables.functions[0].id;
    let local = body.locals[0].id;
    let pointee = body.locals[0].ty;
    let scope = body.root.scope;
    let span = body.root.statements[1].span;
    let region = HirRegionId::new(0);
    tables.regions.push(HirRegion {
        id: region,
        owner: nera::HirRegionOwner::Function(owner),
        origin: HirRegionOrigin::Inferred { scope },
        span,
    });
    let reference = push_type(
        &mut tables,
        "&u64",
        HirTypeKind::Reference {
            pointee,
            mutability: HirMutability::Const,
            region,
        },
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
                                ty: pointee,
                                span,
                            }),
                            mutability: HirMutability::Const,
                            region,
                        },
                        ty: reference,
                        span,
                    },
                },
                span,
            },
        );
    tables
}

#[test]
fn v5_preserves_signature_regions_and_canonical_outlives_constraints() {
    let program = validate(signature_region_tables()).expect("canonical signature regions");

    assert_eq!(program.version(), HirVersion::V16);
    assert!(HirVersion::V4.supports_borrow_regions());
    assert!(HirVersion::V5.supports_borrow_regions());
    assert!(HirVersion::V7.supports_borrow_regions());
    assert!(HirVersion::V7.supports_deferred_locals());
    assert!(!HirVersion::V5.supports_deferred_locals());
    for old in [HirVersion::V1, HirVersion::V2, HirVersion::V3] {
        assert!(!old.supports_borrow_regions());
    }
    assert_eq!(program.regions().len(), 2);
    assert_eq!(
        program
            .region(HirRegionId::new(0))
            .map(|region| region.origin),
        Some(HirRegionOrigin::Parameter { index: 0 })
    );
    assert_eq!(
        program
            .region(HirRegionId::new(1))
            .map(|region| region.origin),
        Some(HirRegionOrigin::Result)
    );
    let constraint = program
        .region_constraint(HirRegionConstraintId::new(0))
        .expect("canonical constraint");
    assert_eq!(constraint.subregion, HirRegionId::new(1));
    assert_eq!(constraint.superregion, HirRegionId::new(0));
}

#[test]
fn region_and_constraint_tables_reject_noncanonical_entries() {
    let mut nondense = signature_region_tables();
    nondense.regions[0].id = HirRegionId::new(2);
    let error = validate(nondense).expect_err("region identities must be dense");
    assert_eq!(error.table(), "region");
    assert_eq!(
        error.problem(),
        "table ID does not equal its deterministic index"
    );

    let mut dangling = signature_region_tables();
    dangling.region_constraints[0].superregion = HirRegionId::new(9);
    let error = validate(dangling).expect_err("constraint endpoints must exist");
    assert_eq!(error.table(), "region constraint");
    assert_eq!(
        error.problem(),
        "constraint is reflexive, duplicate, dangling, foreign, or outside its function"
    );

    let mut reflexive = signature_region_tables();
    reflexive.region_constraints[0].subregion = HirRegionId::new(0);
    let error = validate(reflexive).expect_err("canonical constraints are non-reflexive");
    assert_eq!(error.table(), "region constraint");

    let mut duplicate = signature_region_tables();
    let mut repeated = duplicate.region_constraints[0];
    repeated.id = HirRegionConstraintId::new(1);
    duplicate.region_constraints.push(repeated);
    let error = validate(duplicate).expect_err("canonical constraints are unique");
    assert_eq!(error.table(), "region constraint");
}

#[test]
fn signature_region_origins_must_be_anchored_and_visible() {
    let mut unanchored = signature_region_tables();
    unanchored.regions[0].origin = HirRegionOrigin::Parameter { index: 1 };
    let error = validate(unanchored).expect_err("parameter origin must name its signature slot");
    assert_eq!(error.table(), "region");
    assert_eq!(
        error.problem(),
        "missing owner, foreign span, or origin is not anchored by its owner"
    );

    let mut wrong_origin = signature_region_tables();
    wrong_origin.regions[0].origin = HirRegionOrigin::Result;
    let error = validate(wrong_origin).expect_err("parameter types require parameter regions");
    assert_eq!(error.table(), "region");
}

#[test]
fn lexical_region_must_be_visible_at_each_reference_expression() {
    validate(local_borrow_tables()).expect("root-scoped borrow region is visible");

    let mut outside_scope = local_borrow_tables();
    outside_scope.regions[0].origin = HirRegionOrigin::Inferred {
        scope: HirScopeId::new(1),
    };
    let error = validate(outside_scope).expect_err("unknown scope cannot make a region visible");
    assert_eq!(error.table(), "expression");
    assert_eq!(
        error.problem(),
        "type contains a borrow region that is not visible in this lexical scope"
    );
}

#[test]
fn foreign_function_region_cannot_be_used_by_a_borrow_expression() {
    let base = accepted_program(
        "fn owner() { return; }\nfn borrower() -> u64 { let value = 1; return value; }",
    );
    let mut tables = program_tables(&base);
    let owner_body = tables.functions[0].body.as_ref().expect("owner body");
    let owner_scope = owner_body.root.scope;
    let owner_span = owner_body.root.span;
    let borrower = &tables.functions[1];
    let borrower_body = borrower.body.as_ref().expect("borrower body");
    let local = borrower_body.locals[0].id;
    let pointee = borrower_body.locals[0].ty;
    let span = borrower_body.root.statements[1].span;
    let region = HirRegionId::new(0);
    tables.regions.push(HirRegion {
        id: region,
        owner: nera::HirRegionOwner::Function(HirFunctionId::new(0)),
        origin: HirRegionOrigin::LexicalScope { scope: owner_scope },
        span: owner_span,
    });
    let reference = push_type(
        &mut tables,
        "&foreign u64",
        HirTypeKind::Reference {
            pointee,
            mutability: HirMutability::Const,
            region,
        },
    );
    tables.functions[1]
        .body
        .as_mut()
        .expect("borrower body")
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
                                ty: pointee,
                                span,
                            }),
                            mutability: HirMutability::Const,
                            region,
                        },
                        ty: reference,
                        span,
                    },
                },
                span,
            },
        );

    let error = validate(tables).expect_err("a function cannot consume a foreign lexical region");
    assert_eq!(error.table(), "expression");
    assert_eq!(
        error.problem(),
        "type contains a borrow region that is not visible in this lexical scope"
    );
}

#[test]
fn region_and_constraint_spans_must_stay_inside_the_owner_function() {
    let outside = ByteSpan::new(0, u32::MAX as usize).expect("ordered span");

    let mut region_span = signature_region_tables();
    region_span.regions[0].span = outside;
    let error = validate(region_span).expect_err("region span must be owned");
    assert_eq!(error.table(), "region");

    let mut constraint_span = signature_region_tables();
    constraint_span.region_constraints[0].span = outside;
    let error = validate(constraint_span).expect_err("constraint span must be owned");
    assert_eq!(error.table(), "region constraint");
}
