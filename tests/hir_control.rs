use nera::{
    HirBlock, HirExpression, HirExpressionKind, HirForSource, HirIntegerPredicate, HirIntegerType,
    HirLocal, HirLocalId, HirLoopId, HirMatchArm, HirPattern, HirPatternKind, HirPlace,
    HirPlaceBase, HirProgram, HirProgramTables, HirScopeId, HirStatement, HirStatementKind,
    HirTypeId, HirTypeKind, HirUseMode, SourceFile, analyze,
};

fn base_tables() -> HirProgramTables {
    let program = analyze(&SourceFile::from_text(
        "hir-control.nera",
        "fn structured() { return; }",
    ))
    .hir()
    .expect("Core0 fixture is accepted")
    .clone();
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

fn from_tables(
    mut tables: HirProgramTables,
) -> Result<HirProgram, nera::HirProgramValidationError> {
    tables.assign_canonical_node_ids()?;
    tables.assign_canonical_type_capabilities()?;
    HirProgram::from_tables(tables)
}

fn type_id(tables: &HirProgramTables, kind: HirTypeKind) -> HirTypeId {
    tables
        .types
        .iter()
        .find(|definition| definition.kind == kind)
        .expect("Core0 type exists")
        .id
}

fn expression(kind: HirExpressionKind, ty: HirTypeId, span: nera::ByteSpan) -> HirExpression {
    HirExpression {
        id: nera::HirNodeId::new(0),
        kind,
        ty,
        span,
    }
}

fn block(scope: u32, span: nera::ByteSpan, statements: Vec<HirStatement>) -> HirBlock {
    HirBlock {
        scope: HirScopeId::new(scope),
        locals: Vec::new(),
        statements,
        span,
    }
}

fn statement(kind: HirStatementKind, span: nera::ByteSpan) -> HirStatement {
    HirStatement {
        id: nera::HirNodeId::new(0),
        kind,
        span,
    }
}

fn structured_tables() -> HirProgramTables {
    let mut tables = base_tables();
    let bool_type = type_id(&tables, HirTypeKind::Bool);
    let u64_type = type_id(&tables, HirTypeKind::Integer(HirIntegerType::U64));
    let u64_layout = tables.types[u64_type.index()]
        .layout
        .expect("u64 has a layout");
    let body = tables.functions[0].body.as_mut().expect("fixture body");
    let span = body.root.span;

    body.locals.push(HirLocal {
        id: HirLocalId::new(0),
        name: "item".to_owned(),
        ty: u64_type,
        layout: u64_layout,
        scope: HirScopeId::new(4),
        mutable: false,
        declaration_span: span,
    });
    let bool_expression = || expression(HirExpressionKind::Bool(true), bool_type, span);
    let word_expression = |value| expression(HirExpressionKind::Integer(value), u64_type, span);

    let then_block = block(1, span, Vec::new());
    let else_block = block(2, span, Vec::new());
    let while_body = block(
        3,
        span,
        vec![statement(
            HirStatementKind::Break {
                target: HirLoopId::new(0),
            },
            span,
        )],
    );
    let mut for_body = block(
        4,
        span,
        vec![statement(
            HirStatementKind::Continue {
                target: HirLoopId::new(1),
            },
            span,
        )],
    );
    for_body.locals.push(HirLocalId::new(0));
    let binding = HirPattern {
        id: nera::HirNodeId::new(0),
        kind: HirPatternKind::Binding {
            local: HirLocalId::new(0),
            mode: HirUseMode::Copy,
        },
        ty: u64_type,
        span,
    };
    let match_arms = [false, true]
        .into_iter()
        .enumerate()
        .map(|(index, value)| HirMatchArm {
            pattern: HirPattern {
                id: nera::HirNodeId::new(0),
                kind: HirPatternKind::Bool(value),
                ty: bool_type,
                span,
            },
            guard: None,
            body: block(
                u32::try_from(index + 5).expect("small scope"),
                span,
                Vec::new(),
            ),
            span,
        })
        .collect();

    body.root.statements = vec![
        statement(
            HirStatementKind::If {
                condition: bool_expression(),
                then_block,
                else_block: Some(else_block),
            },
            span,
        ),
        statement(
            HirStatementKind::While {
                loop_id: HirLoopId::new(0),
                condition: bool_expression(),
                body: while_body,
            },
            span,
        ),
        statement(
            HirStatementKind::For {
                loop_id: HirLoopId::new(1),
                pattern: binding,
                source: HirForSource::IntegerRange {
                    start: word_expression(0),
                    end: word_expression(4),
                    inclusive: false,
                    item_type: u64_type,
                },
                body: for_body,
            },
            span,
        ),
        statement(
            HirStatementKind::Match {
                scrutinee: bool_expression(),
                arms: match_arms,
            },
            span,
        ),
        statement(HirStatementKind::Return { value: None }, span),
    ];
    tables
}

#[test]
fn structured_hir_validates_scope_loop_pattern_and_exit_schema() {
    let program = from_tables(structured_tables()).expect("well-scoped structured HIR is accepted");
    let body = program.entry_function().body().expect("structured body");

    assert_eq!(body.root.scope, HirScopeId::new(0));
    assert!(body.parameters.is_empty());
    assert_eq!(body.locals[0].scope, HirScopeId::new(4));
}

#[test]
fn structured_hir_rejects_non_deterministic_scope_and_foreign_loop_target() {
    let mut wrong_scope = structured_tables();
    let body = wrong_scope.functions[0].body.as_mut().expect("body");
    let HirStatementKind::If { then_block, .. } = &mut body.root.statements[0].kind else {
        panic!("if fixture");
    };
    then_block.scope = HirScopeId::new(9);
    assert_eq!(
        from_tables(wrong_scope)
            .expect_err("non-deterministic scope must fail")
            .table(),
        "scope"
    );

    let mut wrong_target = structured_tables();
    let body = wrong_target.functions[0].body.as_mut().expect("body");
    let HirStatementKind::While { body, .. } = &mut body.root.statements[1].kind else {
        panic!("while fixture");
    };
    body.statements[0].kind = HirStatementKind::Break {
        target: HirLoopId::new(7),
    };
    assert_eq!(
        from_tables(wrong_target)
            .expect_err("foreign break target must fail")
            .problem(),
        "control-flow target is not an enclosing loop"
    );
}

#[test]
fn structured_hir_rejects_non_boolean_condition_and_wrong_return_type() {
    let mut wrong_condition = structured_tables();
    let u64_type = type_id(&wrong_condition, HirTypeKind::Integer(HirIntegerType::U64));
    let body = wrong_condition.functions[0].body.as_mut().expect("body");
    let span = body.root.span;
    let HirStatementKind::While { condition, .. } = &mut body.root.statements[1].kind else {
        panic!("while fixture");
    };
    *condition = expression(HirExpressionKind::Integer(1), u64_type, span);
    assert_eq!(
        from_tables(wrong_condition)
            .expect_err("integer loop condition must fail")
            .problem(),
        "control-flow condition is not boolean"
    );

    let mut wrong_return = structured_tables();
    let body = wrong_return.functions[0].body.as_mut().expect("body");
    let span = body.root.span;
    body.root.statements[4].kind = HirStatementKind::Return {
        value: Some(expression(HirExpressionKind::Integer(0), u64_type, span)),
    };
    assert_eq!(
        from_tables(wrong_return)
            .expect_err("unit return value must fail")
            .problem(),
        "return value does not match function return type"
    );
}

#[test]
fn structured_hir_rejects_non_exhaustive_match() {
    let mut tables = structured_tables();
    let body = tables.functions[0].body.as_mut().expect("body");
    let HirStatementKind::Match { arms, .. } = &mut body.root.statements[3].kind else {
        panic!("match fixture");
    };
    arms.pop();

    assert_eq!(
        from_tables(tables)
            .expect_err("non-exhaustive boolean match must fail")
            .problem(),
        "match coverage is non-exhaustive or has unreachable arms"
    );

    let mut tables = structured_tables();
    let body = tables.functions[0].body.as_mut().expect("body");
    let HirStatementKind::Match { arms, .. } = &mut body.root.statements[3].kind else {
        panic!("match fixture");
    };
    arms[0].pattern.kind = HirPatternKind::Wildcard;
    assert_eq!(
        from_tables(tables)
            .expect_err("an arm after an exhaustive prefix must fail")
            .problem(),
        "match coverage is non-exhaustive or has unreachable arms"
    );
}

#[test]
fn structured_hir_validates_comparison_types_and_spans() {
    let mut valid = structured_tables();
    let bool_type = type_id(&valid, HirTypeKind::Bool);
    let u64_type = type_id(&valid, HirTypeKind::Integer(HirIntegerType::U64));
    let body = valid.functions[0].body.as_mut().expect("body");
    let span = body.root.span;
    let comparison = expression(
        HirExpressionKind::Compare {
            predicate: HirIntegerPredicate::LessThan,
            left: Box::new(expression(HirExpressionKind::Integer(1), u64_type, span)),
            right: Box::new(expression(HirExpressionKind::Integer(2), u64_type, span)),
            operation_span: span,
        },
        bool_type,
        span,
    );
    let HirStatementKind::If { condition, .. } = &mut body.root.statements[0].kind else {
        panic!("if fixture");
    };
    *condition = comparison;
    from_tables(valid.clone()).expect("well-typed comparison is accepted");

    let body = valid.functions[0].body.as_mut().expect("body");
    let HirStatementKind::If { condition, .. } = &mut body.root.statements[0].kind else {
        panic!("if fixture");
    };
    condition.ty = u64_type;
    assert_eq!(
        from_tables(valid)
            .expect_err("comparison result type must be boolean")
            .problem(),
        "comparison operand types, result type, or spans are inconsistent"
    );
}

#[test]
fn structured_hir_rejects_local_use_from_a_sibling_scope() {
    let mut tables = structured_tables();
    let u64_type = type_id(&tables, HirTypeKind::Integer(HirIntegerType::U64));
    let body = tables.functions[0].body.as_mut().expect("body");
    let span = body.root.span;
    body.locals[0].scope = HirScopeId::new(1);

    let HirStatementKind::If {
        then_block,
        else_block: Some(else_block),
        ..
    } = &mut body.root.statements[0].kind
    else {
        panic!("if fixture");
    };
    then_block.locals.push(HirLocalId::new(0));
    else_block.statements.push(statement(
        HirStatementKind::Evaluate {
            expression: expression(
                HirExpressionKind::Read {
                    place: Box::new(HirPlace {
                        id: nera::HirNodeId::new(0),
                        base: HirPlaceBase::Local(HirLocalId::new(0)),
                        projections: Vec::new(),
                        ty: u64_type,
                        span,
                    }),
                    mode: HirUseMode::Copy,
                },
                u64_type,
                span,
            ),
        },
        span,
    ));
    let HirStatementKind::For { pattern, body, .. } = &mut body.root.statements[2].kind else {
        panic!("for fixture");
    };
    body.locals.clear();
    pattern.kind = HirPatternKind::Wildcard;

    assert_eq!(
        from_tables(tables)
            .expect_err("a sibling local must not be visible")
            .problem(),
        "place base local is outside its lexical scope"
    );
}
