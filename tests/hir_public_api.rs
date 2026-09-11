use nera::{
    HirContractId, HirFieldId, HirGenericParameterId, HirLayoutId, HirLoopId, HirModulePath,
    HirPredicateId, HirProgram, HirProgramTables, HirScopeId, HirTypeId, HirVariantId, SourceFile,
    analyze,
};

#[test]
fn hir_program_is_reconstructible_and_queryable_through_the_public_api() {
    let output = analyze(&SourceFile::from_text(
        "public-api.nera",
        "fn public_api() { let memory = alloc<u64>(1); free(memory); return; }",
    ));
    let program: &HirProgram = output.hir().expect("fixture is accepted");
    let entry_module = program.entry_module();
    let entry_function = program.entry_function();
    let body = entry_function.body().expect("fixture has a body");

    assert_eq!(program.module(entry_module.id), Some(entry_module));
    assert_eq!(
        program.function_by_id(entry_function.id),
        Some(entry_function)
    );
    assert_eq!(
        program
            .contract(entry_function.contract)
            .map(|item| item.id),
        Some(HirContractId::new(0))
    );
    assert!(program.type_definition(HirTypeId::new(0)).is_some());
    assert!(program.layout(HirLayoutId::new(0)).is_some());
    assert!(program.field(HirFieldId::new(0)).is_none());
    assert!(program.variant(HirVariantId::new(0)).is_none());
    assert!(
        program
            .generic_parameter(HirGenericParameterId::new(0))
            .is_none()
    );
    assert!(program.predicate(HirPredicateId::new(0)).is_none());
    assert_eq!(body.root.scope, HirScopeId::new(0));
    assert_eq!(
        body.root.locals,
        body.locals.iter().map(|local| local.id).collect::<Vec<_>>()
    );
    assert!(body.parameters.is_empty());
    assert_eq!(HirLoopId::new(3).get(), 3);

    let rebuilt = HirProgram::from_tables(HirProgramTables {
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
    })
    .expect("public tables reconstruct a valid immutable program");
    assert_eq!(&rebuilt, program);
}

#[test]
fn public_module_paths_reject_empty_segments() {
    assert_eq!(HirModulePath::root().segments(), &["crate".to_owned()]);
    assert!(HirModulePath::from_segments(Vec::new()).is_none());
    assert!(HirModulePath::from_segments(vec!["crate".to_owned(), String::new()]).is_none());
    assert_eq!(
        HirModulePath::from_segments(vec!["crate".to_owned(), "memory".to_owned()])
            .expect("valid path")
            .segments(),
        &["crate".to_owned(), "memory".to_owned()]
    );
}
