use nera::{
    BorrowAccess, BorrowResultRelation, CfgAnalysisConfig, FrontendStatus, SourceFile,
    VirAbiErrorKind, VirAbiSignature, VirRuntimeValue, analyze, interpret, verify_program,
};

const SOURCE: &str = "fn main()->u64{let mut x=1;let r=outer(7,&mut x);*r=42;return x;}
    fn outer(n:u64,r:&mut u64)->&mut u64{return inner(r,n);}
    fn inner(r:&mut u64,n:u64)->&mut u64{if n==0{return r;}return inner(r,0);}";

#[test]
fn forward_and_recursive_calls_share_logical_relations_and_unchanged_slots() {
    let file = SourceFile::from_text("borrow-mapping.nera", SOURCE);
    let output = analyze(&file);
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:?}",
        output.issues()
    );
    assert_eq!(output, analyze(&file));
    let hir = output.hir().unwrap();
    let unit = output.vir().unwrap().resolve().unwrap();
    for (name, index, slots) in [("outer", 1, vec![1, 2]), ("inner", 0, vec![0, 1])] {
        let function = hir.functions().iter().find(|f| f.name == name).unwrap();
        let relation = BorrowResultRelation::whole(index, BorrowAccess::Mutable);
        assert_eq!(function.signature.borrow_result, Some(relation));
        let abi = &unit
            .runtime()
            .abis
            .function(nera::VirFunctionId::new(function.id.get()))
            .unwrap()
            .signature;
        assert_eq!(abi.borrow_result(), Some(relation));
        assert_eq!(abi.parameters()[index as usize].parameter_slots(), slots);
        assert!(abi.parameters()[index as usize].result_slots().is_empty());
        assert_eq!(abi.results()[0].result_slots(), [0, 1]);
    }
    assert!(
        verify_program(&unit, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.runtime())
        .unwrap();
    assert!(
        output
            .vir()
            .unwrap()
            .stable_dump()
            .contains("borrow-result0=param1/Whole/Mutable")
    );
}

#[test]
fn explicit_relation_checks_shape_indices_and_missing_mapping_at_the_unit_boundary() {
    let output = analyze(&SourceFile::from_text("mapping.nera", SOURCE));
    let original = output.vir().unwrap().as_unit();
    let abi = &original.runtime.abis.functions[1].signature;
    let parameters: Vec<_> = abi
        .parameters()
        .iter()
        .map(|p| p.value().access().unwrap())
        .collect();
    let results: Vec<_> = abi
        .results()
        .iter()
        .map(|p| p.value().access().unwrap())
        .collect();
    for (parameter, result, access) in [
        (0, 0, BorrowAccess::Mutable),
        (99, 0, BorrowAccess::Mutable),
        (1, 1, BorrowAccess::Mutable),
        (1, 0, BorrowAccess::Shared),
    ] {
        let mut relation = BorrowResultRelation::whole(parameter, access);
        relation.result = result;
        assert_eq!(
            VirAbiSignature::classify_with_borrow_result(
                &original.memory,
                &parameters,
                &results,
                Some(relation)
            )
            .unwrap_err()
            .kind(),
            &VirAbiErrorKind::InvalidBorrowResult
        );
    }
    // Classification alone is useful for isolated value shape checks. A
    // function returning a borrowed view cannot omit its source relation.
    let missing =
        VirAbiSignature::classify_with_borrow_result(&original.memory, &parameters, &results, None)
            .unwrap();
    let mut raw = original.clone();
    raw.runtime.functions[1].signature = missing.physical().clone();
    raw.runtime.abis.functions[1].signature = missing;
    assert!(raw.into_validated().is_err());
}

#[test]
fn explicit_mapping_selects_mutable_restoration_without_type_position_guessing() {
    let output = analyze(&SourceFile::from_text("mapping.nera", SOURCE));
    let unit = output.vir().unwrap().as_unit();
    let reference = unit.runtime.abis.functions[1].signature.parameters()[1]
        .value()
        .access()
        .unwrap();
    // Raw schema test only: source-level multi-input return remains gated.
    // Equal types do not select the first parameter implicitly.
    let abi = VirAbiSignature::classify_with_borrow_result(
        &unit.memory,
        &[reference, reference],
        &[reference],
        Some(BorrowResultRelation::whole(1, BorrowAccess::Mutable)),
    )
    .unwrap();
    assert_eq!(abi.borrow_result_parameter(), Some(1));
    assert_eq!(abi.parameters()[0].result_slots(), [2]);
    assert!(abi.parameters()[1].result_slots().is_empty());
    assert_eq!(abi.results()[0].result_slots(), [0, 1]);
}

#[test]
fn duplicate_parameter_regions_cannot_import_the_same_interface_loan_twice() {
    let output = analyze(&SourceFile::from_text(
        "duplicate-interface-region.nera",
        SOURCE,
    ));
    let mut unit = output.vir().unwrap().as_unit().clone();
    let mut regions = unit.borrows.regions().to_vec();
    let mut duplicate = regions
        .iter()
        .find(|r| matches!(r.origin, nera::VirBorrowRegionOrigin::Parameter { .. }))
        .unwrap()
        .clone();
    duplicate.id = nera::VirBorrowRegionId::new(regions.len() as u32);
    let id = duplicate.id;
    regions.push(duplicate);
    unit.borrows =
        nera::VirBorrowEnvironment::from_tables(regions, unit.borrows.constraints().to_vec());
    let error = unit
        .into_validated()
        .expect_err("duplicate logical parameter region must fail validation");
    assert!(
        matches!(error.kind(), nera::VirValidationErrorKind::InvalidBorrowRegion(found) if *found == id)
    );
}

#[test]
fn parameter_field_regions_cannot_claim_scalar_or_direct_reference_parameters() {
    let output = analyze(&SourceFile::from_text("field-region-boundary.nera", SOURCE));
    for (index, slot) in [(0, 0), (1, 0), (1, u32::MAX), (99, 0)] {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let mut regions = unit.borrows.regions().to_vec();
        let mut field = regions
            .iter()
            .find(|r| {
                r.owner == nera::VirFunctionId::new(1)
                    && matches!(r.origin, nera::VirBorrowRegionOrigin::Parameter { .. })
            })
            .unwrap()
            .clone();
        field.id = nera::VirBorrowRegionId::new(regions.len() as u32);
        field.origin = nera::VirBorrowRegionOrigin::ParameterField { index, slot };
        let id = field.id;
        regions.push(field);
        unit.borrows =
            nera::VirBorrowEnvironment::from_tables(regions, unit.borrows.constraints().to_vec());
        assert!(
            unit.stable_dump()
                .contains(&format!("parameter-field({index},{slot})"))
        );
        let error = unit
            .into_validated()
            .expect_err("a field binder requires a real indirect reference leaf");
        assert!(
            matches!(error.kind(), nera::VirValidationErrorKind::InvalidBorrowRegion(found) if *found == id)
        );
    }
}
