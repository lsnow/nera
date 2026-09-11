use nera::{
    BorrowAccess, BorrowProjection, BorrowResultRelation, BorrowSliceBound, CfgAnalysisConfig,
    FrontendStatus, SourceFile, VirAbiSignature, VirInstruction, VirRuntimeValue, analyze,
    interpret, verify_program,
};

fn checked(source: &str, expected: u64) -> nera::FrontendOutput {
    let output = analyze(&SourceFile::from_text("borrow-projection.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:#?}",
        output.issues()
    );
    let unit = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&unit, CfgAnalysisConfig::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:#?}",
        report.diagnostics()
    );
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(expected)]
    );
    nera::backend::X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(unit.runtime())
        .unwrap();
    output
}

#[test]
fn fixed_field_return_is_an_explicit_bounded_projection() {
    let output = checked(
        "struct Pair { left:u64, right:u64, }
         fn main()->u64 { let pair=Pair { left:10, right:32 }; let view=right(&pair); return *view; }
         fn right(pair:&Pair)->&u64 { return &pair.right; }",
        32,
    );
    assert!(matches!(
        output.hir().unwrap().functions()[1]
            .signature
            .borrow_result
            .unwrap()
            .projection,
        BorrowProjection::Fixed {
            offset_bytes: 8,
            size_bytes: 8,
            alignment: 8
        }
    ));
}

#[test]
fn constant_and_parameter_slice_returns_keep_range_equations() {
    let constant = checked(
        "fn main()->u64 { let values=[10,20,30,40]; let view=middle(&values[..]); return view[1]; }
         fn middle(values:&[u64])->&[u64] { return &values[1..3]; }",
        30,
    );
    assert!(matches!(
        constant.hir().unwrap().functions()[1]
            .signature
            .borrow_result
            .unwrap()
            .projection,
        BorrowProjection::Slice {
            start: BorrowSliceBound::Constant(1),
            end: BorrowSliceBound::Constant(3),
            stride_bytes: 8,
            alignment: 8,
        }
    ));

    let dynamic = checked(
        "fn main()->u64 { let values=[10,20,30,40]; let view=cut(&values[..],1usize,3usize); return view[0]+view[1]; }
         fn cut(values:&[u64],begin:usize,end:usize)->&[u64] { return &values[begin..end]; }",
        50,
    );
    assert!(matches!(
        dynamic.hir().unwrap().functions()[1]
            .signature
            .borrow_result
            .unwrap()
            .projection,
        BorrowProjection::Slice {
            start: BorrowSliceBound::Parameter(1),
            end: BorrowSliceBound::Parameter(2),
            ..
        }
    ));
}

#[test]
fn empty_subview_is_a_valid_non_dereferenced_value() {
    checked(
        "fn main()->u64 { let values=[10,20]; let view=empty(&values[..]); return 42; }
         fn empty(values:&[u64])->&[u64] { return &values[0..0]; }",
        42,
    );
}

#[test]
fn local_backing_and_stored_reference_payloads_remain_gated() {
    for source in [
        "fn main()->u64{return 0;} fn bad(source:&u64)->&u64{let local=42;return &local;}",
        "struct Holder { value:&u64, } fn main()->u64{return 0;} fn extract(holder:&Holder)->&u64{return holder.value;}",
        "fn main()->u64{return 0;} fn nonlinear(values:&[u64],begin:usize,end:usize)->&[u64]{return &values[begin+1usize..end];}",
    ] {
        let output = analyze(&SourceFile::from_text(
            "borrow-projection-gated.nera",
            source,
        ));
        assert!(matches!(
            output.status(),
            FrontendStatus::Invalid | FrontendStatus::Unsupported
        ));
    }
}

#[test]
fn mutable_fixed_field_projection_narrows_authority_and_restores_parent() {
    checked(
        "struct Pair { left:u64, right:u64, }
         fn main()->u64 { let mut pair=Pair { left:10, right:20 }; let view=right(&mut pair); *view=42; return 42; }
         fn right(pair:&mut Pair)->&mut u64 { return &mut pair.right; }",
        42,
    );
}

#[test]
fn fixed_projection_composes_through_multiple_wrappers() {
    let output = checked(
        "struct Pair { left:u64, right:u64, }
         fn main()->u64 { let pair=Pair { left:10, right:32 }; let view=outer(&pair); return *view; }
         fn outer(pair:&Pair)->&u64 { return right(pair); }
         fn right(pair:&Pair)->&u64 { return &pair.right; }",
        32,
    );
    for function in &output.hir().unwrap().functions()[1..] {
        assert!(matches!(
            function.signature.borrow_result.unwrap().projection,
            BorrowProjection::Fixed {
                offset_bytes: 8,
                size_bytes: 8,
                alignment: 8
            }
        ));
    }
}

#[test]
fn caller_must_prove_projected_slice_preconditions() {
    let source = "fn main()->u64 { let values=[10,20]; let view=middle(&values[..]); return 0; }
         fn middle(values:&[u64])->&[u64] { return &values[1..3]; }";
    let output = analyze(&SourceFile::from_text("borrow-projection-oob.nera", source));
    assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
    let unit = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&unit, CfgAnalysisConfig::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(report.diagnostics().iter().any(|diagnostic| {
        diagnostic
            .message()
            .contains("ends within the caller source view")
    }));
    assert!(interpret(unit.runtime()).is_err());
}

#[test]
fn empty_projected_slice_cannot_be_dereferenced() {
    let source =
        "fn main()->u64 { let values=[10,20]; let view=empty(&values[..]); return view[0]; }
         fn empty(values:&[u64])->&[u64] { return &values[0..0]; }";
    let output = analyze(&SourceFile::from_text(
        "borrow-projection-empty.nera",
        source,
    ));
    assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
    let unit = output.vir().unwrap().resolve().unwrap();
    assert!(
        !verify_program(&unit, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert!(interpret(unit.runtime()).is_err());
}

#[test]
fn raw_abi_or_ssa_projection_mutation_fails_closed() {
    let source = "struct Pair { left:u64, right:u64, }
        fn main()->u64 { let pair=Pair { left:10, right:32 }; let view=right(&pair); return *view; }
        fn right(pair:&Pair)->&u64 { return &pair.right; }";
    let output = analyze(&SourceFile::from_text(
        "borrow-projection-mutation.nera",
        source,
    ));
    let original = output.vir().unwrap().as_unit();
    let old = &original.runtime.abis.functions[1].signature;
    let parameters = old
        .parameters()
        .iter()
        .map(|binding| binding.value().access().unwrap())
        .collect::<Vec<_>>();
    let results = old
        .results()
        .iter()
        .map(|binding| binding.value().access().unwrap())
        .collect::<Vec<_>>();

    let wrong = VirAbiSignature::classify_with_borrow_result(
        &original.memory,
        &parameters,
        &results,
        Some(BorrowResultRelation {
            parameter: 0,
            result: 0,
            projection: BorrowProjection::Fixed {
                offset_bytes: 0,
                size_bytes: 8,
                alignment: 8,
            },
            access: BorrowAccess::Shared,
        }),
    )
    .unwrap();
    let mut corrupted_abi = original.clone();
    corrupted_abi.runtime.abis.functions[1].signature = wrong;
    assert!(corrupted_abi.into_validated().is_err());

    let mut corrupted_ssa = original.clone();
    let address = corrupted_ssa.runtime.functions[1].blocks[0]
        .instructions
        .iter_mut()
        .find_map(|instruction| match &mut instruction.instruction {
            VirInstruction::FieldAddress { offset_bytes, .. } => Some(offset_bytes),
            _ => None,
        })
        .unwrap();
    *address = 0;
    assert!(corrupted_ssa.into_validated().is_err());

    let widened = VirAbiSignature::classify_with_borrow_result(
        &original.memory,
        &parameters,
        &results,
        Some(BorrowResultRelation {
            parameter: 0,
            result: 0,
            projection: BorrowProjection::Fixed {
                offset_bytes: 8,
                size_bytes: 8,
                alignment: 8,
            },
            access: BorrowAccess::Mutable,
        }),
    );
    assert!(widened.is_err());

    let slice_source =
        "fn main()->u64 { let values=[10,20,30,40]; let view=middle(&values[..]); return view[0]; }
         fn middle(values:&[u64])->&[u64] { return &values[1..3]; }";
    let slice_output = analyze(&SourceFile::from_text(
        "borrow-projection-slice-mutation.nera",
        slice_source,
    ));
    let mut corrupted_slice = slice_output.vir().unwrap().as_unit().clone();
    let instruction = corrupted_slice.runtime.functions[1].blocks[0]
        .instructions
        .iter_mut()
        .find_map(|instruction| match &mut instruction.instruction {
            VirInstruction::SliceAddress { start, end, .. } => Some((*start, end)),
            _ => None,
        })
        .unwrap();
    *instruction.1 = instruction.0;
    assert!(corrupted_slice.into_validated().is_err());
}
