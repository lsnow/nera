use nera::{
    ByteSpan, SpannedVirTerminator, VirBasicBlock, VirBlockId, VirContractId, VirContractPosition,
    VirFunction, VirFunctionId, VirMemorySchema, VirOrigin, VirOriginId, VirOriginKind,
    VirSignature, VirSource, VirSourceId, VirSourceMap, VirSpecClauseKind, VirSpecClauseOrigin,
    VirSpecEnvironment, VirTerminator, VirType, VirUnit, VirValidationErrorKind, VirValue,
    VirValueId,
};

#[path = "support/contract_builder.rs"]
mod contract_builder;

use contract_builder::{add_u64_range, function_origin};

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(start, end).expect("fixture span")
}

fn function(id: u32, contract: u32, source_span: ByteSpan) -> VirFunction {
    VirFunction {
        id: VirFunctionId::new(id),
        name: format!("function_{id}"),
        signature: VirSignature {
            parameters: vec![VirType::U64],
            results: vec![VirType::U64],
        },
        contract: VirContractId::new(contract),
        entry: VirBlockId::new(0),
        blocks: vec![VirBasicBlock {
            id: VirBlockId::new(0),
            parameters: vec![VirValue {
                id: VirValueId::new(0),
                ty: VirType::U64,
            }],
            instructions: Vec::new(),
            terminator: SpannedVirTerminator {
                terminator: VirTerminator::Return {
                    values: vec![VirValueId::new(0)],
                },
                source_span,
            },
            source_span,
        }],
        source_span,
    }
}

fn raw_unit() -> VirUnit {
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![function(0, 0, span(0, 10))],
    )
}

#[test]
fn implicit_contract_has_canonical_binders_and_validates() {
    let unit = raw_unit();
    let contract = &unit.specs.contracts()[0];

    assert_eq!(contract.binders.len(), 2);
    assert_eq!(contract.binders[0].position, VirContractPosition::Requires);
    assert_eq!(contract.binders[1].position, VirContractPosition::Ensures);
    unit.into_validated()
        .expect("implicit contract is complete");
}

#[test]
fn every_function_requires_one_dense_owned_contract() {
    let mut missing = raw_unit();
    missing.specs = VirSpecEnvironment::empty();
    assert!(matches!(
        missing
            .into_validated()
            .expect_err("missing contract")
            .kind(),
        VirValidationErrorKind::MissingFunctionContract(function)
            if *function == VirFunctionId::new(0)
    ));

    let mut non_dense = raw_unit();
    let mut contract = non_dense.specs.contracts()[0].clone();
    contract.id = VirContractId::new(1);
    non_dense.specs = VirSpecEnvironment::from_contracts(vec![contract]);
    assert!(matches!(
        non_dense
            .into_validated()
            .expect_err("non-dense contract")
            .kind(),
        VirValidationErrorKind::NonDenseContractId { .. }
    ));
}

#[test]
fn binder_density_layout_and_clause_scope_fail_closed() {
    let mut non_dense = raw_unit();
    non_dense
        .specs
        .contract_mut(VirContractId::new(0))
        .unwrap()
        .binders[0]
        .id = nera::VirContractBinderId::new(9);
    assert!(matches!(
        non_dense
            .into_validated()
            .expect_err("non-dense binder")
            .kind(),
        VirValidationErrorKind::NonDenseContractBinderId { .. }
    ));

    let mut wrong_position = raw_unit();
    wrong_position
        .specs
        .contract_mut(VirContractId::new(0))
        .unwrap()
        .binders[0]
        .position = VirContractPosition::Ensures;
    assert!(matches!(
        wrong_position
            .into_validated()
            .expect_err("wrong binder layout")
            .kind(),
        VirValidationErrorKind::ContractBinderLayoutMismatch { .. }
    ));

    let mut cross_position = raw_unit();
    let origin = function_origin(&cross_position, VirFunctionId::new(0));
    let ensures_binder = cross_position
        .specs
        .contract(VirContractId::new(0))
        .unwrap()
        .binder(VirContractPosition::Ensures, 0)
        .unwrap();
    let _ = cross_position.specs.add_contract_clause(
        VirContractId::new(0),
        VirContractPosition::Requires,
        VirSpecClauseOrigin::Explicit { origin },
        VirSpecClauseKind::U64Range {
            binder: ensures_binder,
            lower: 0,
            upper: 1,
        },
    );
    assert!(matches!(
        cross_position
            .into_validated()
            .expect_err("cross-position binder")
            .kind(),
        VirValidationErrorKind::ContractBinderPositionMismatch(_)
    ));
}

#[test]
fn clause_ids_origins_and_inferred_kinds_are_checked() {
    let mut non_dense = raw_unit();
    let origin = function_origin(&non_dense, VirFunctionId::new(0));
    add_u64_range(
        &mut non_dense.specs,
        VirContractId::new(0),
        VirContractPosition::Requires,
        origin,
        0,
        0,
        1,
    );
    non_dense.specs.clauses_mut()[0].id = nera::VirSpecClauseId::new(3);
    assert!(matches!(
        non_dense
            .into_validated()
            .expect_err("non-dense clause")
            .kind(),
        VirValidationErrorKind::NonDenseSpecClauseId { .. }
    ));

    let mut unknown_origin = raw_unit();
    let binder = unknown_origin
        .specs
        .contract(VirContractId::new(0))
        .unwrap()
        .binder(VirContractPosition::Requires, 0)
        .unwrap();
    let _ = unknown_origin.specs.add_contract_clause(
        VirContractId::new(0),
        VirContractPosition::Requires,
        VirSpecClauseOrigin::Explicit {
            origin: nera::VirOriginId::new(99),
        },
        VirSpecClauseKind::U64Range {
            binder,
            lower: 0,
            upper: 1,
        },
    );
    assert!(matches!(
        unknown_origin
            .into_validated()
            .expect_err("unknown origin")
            .kind(),
        VirValidationErrorKind::UnknownSpecClauseOrigin(_)
    ));

    let mut invalid_inference = raw_unit();
    let origin = function_origin(&invalid_inference, VirFunctionId::new(0));
    let binder = invalid_inference
        .specs
        .contract(VirContractId::new(0))
        .unwrap()
        .binder(VirContractPosition::Requires, 0)
        .unwrap();
    let _ = invalid_inference.specs.add_contract_clause(
        VirContractId::new(0),
        VirContractPosition::Requires,
        VirSpecClauseOrigin::InferredType { origin },
        VirSpecClauseKind::U64Range {
            binder,
            lower: 0,
            upper: 1,
        },
    );
    assert!(matches!(
        invalid_inference
            .into_validated()
            .expect_err("scalar fact is not inferred from a safe type")
            .kind(),
        VirValidationErrorKind::InvalidInferredTypeClause(_)
    ));
}

#[test]
fn clause_origin_must_belong_to_the_owning_functions_source() {
    let mut unit = VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![function(0, 0, span(0, 10)), function(1, 1, span(0, 10))],
    );
    let mut sources = unit.source_map.sources().to_vec();
    sources.push(VirSource {
        id: VirSourceId::new(1),
        name: "second.nera".to_owned(),
        byte_len: 10,
    });
    let mut origins = unit.source_map.origins().to_vec();
    origins.push(VirOrigin {
        id: VirOriginId::new(1),
        kind: VirOriginKind::User {
            source: VirSourceId::new(1),
            span: span(0, 10),
        },
    });
    let mut locations = unit.source_map.locations().to_vec();
    for location in &mut locations {
        if location.location.function() == VirFunctionId::new(1) {
            location.origin = VirOriginId::new(1);
        }
    }
    unit.source_map = VirSourceMap::from_tables(sources, origins, locations);

    add_u64_range(
        &mut unit.specs,
        VirContractId::new(0),
        VirContractPosition::Requires,
        VirOriginId::new(1),
        0,
        0,
        1,
    );
    assert!(matches!(
        unit.into_validated()
            .expect_err("a same-coordinate span in a different source is foreign")
            .kind(),
        VirValidationErrorKind::SpecClauseOriginOutsideFunction(_)
    ));
}

#[test]
fn resources_must_be_dense_referenced_and_summarized() {
    let mut non_dense = raw_unit();
    let contract = non_dense.specs.contract_mut(VirContractId::new(0)).unwrap();
    let _ = contract.add_resource();
    contract.resources[0].id = nera::VirContractResourceId::new(4);
    assert!(matches!(
        non_dense
            .into_validated()
            .expect_err("non-dense resource")
            .kind(),
        VirValidationErrorKind::NonDenseContractResourceId { .. }
    ));

    let mut unused = raw_unit();
    let _ = unused
        .specs
        .contract_mut(VirContractId::new(0))
        .unwrap()
        .add_resource();
    assert!(matches!(
        unused.into_validated().expect_err("unused resource").kind(),
        VirValidationErrorKind::UnusedContractResource(_)
    ));
}
