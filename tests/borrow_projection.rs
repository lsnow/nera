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
fn local_backing_escape_and_nonlinear_slice_interfaces_remain_rejected() {
    for source in [
        "fn main()->u64{return 0;} fn bad(source:&u64)->&u64{let local=42;return &local;}",
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
fn stored_shared_reference_field_can_be_returned_through_its_container() {
    checked(
        "struct Holder { value:&u64, }
         fn main()->u64 { let value=42; let holder=Holder { value:&value };
             let view=extract(&holder); return *view; }
         fn extract(holder:&Holder)->&u64 { return holder.value; }",
        42,
    );
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
            parameter_field: None,
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
            parameter_field: None,
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

#[test]
fn last_use_named_parent_ends_after_its_projected_result() {
    checked(
        "struct Pair { left:u64, right:u64, }
         fn main()->u64 { let pair=alloc<Pair>(1); pair.left=10; pair.right=20;
             let parent=&mut *pair; let view=right(parent); *view=42;
             let answer=*view; free(pair); return answer; }
         fn right(pair:&mut Pair)->&mut u64 { return &mut pair.right; }",
        42,
    );
    checked(
        "struct Pair { left:u64, right:u64, }
         fn main()->u64 { let mut pair=Pair { left:10, right:20 };
             let parent=&mut pair; let view=right(parent); *view=42;
             let answer=*view; parent.left=7; return answer+parent.left; }
         fn right(pair:&mut Pair)->&mut u64 { return &mut pair.right; }",
        49,
    );
}

const ARRAY_FIELD: &str = "struct Buffer { header:u64, data:[u64;4], }
    fn main()->u64 { let p=alloc<Buffer>(1); p.header=0; p.data=[10,20,30,40];
        let parent=&mut *p; let view=cut(parent,1usize,3usize); view[0]=42;
        let answer=view[0]; free(p); return answer; }
    fn cut(p:&mut Buffer, start:usize, end:usize)->&mut [u64] { return &mut p.data[start..end]; }";

#[test]
fn array_fields_return_slices_with_layout_offsets_and_entry_bounds() {
    let output = checked(ARRAY_FIELD, 42);
    assert!(matches!(
        output.hir().unwrap().functions()[1]
            .signature
            .borrow_result
            .unwrap()
            .projection,
        BorrowProjection::ArraySlice {
            offset_bytes: 8,
            length: 4,
            start: BorrowSliceBound::Parameter(1),
            end: BorrowSliceBound::Parameter(2),
            stride_bytes: 8,
        }
    ));
    checked(
        "fn main()->u64 { let a=[10,20,30,40]; let v=cut(&a); return v[1]; }
        fn cut(a:&[u64;4])->&[u64] { return &a[1usize..3usize]; }",
        30,
    );
    checked(
        "struct Inner { pad:u64, data:[u64;4], } struct Outer { tag:u64, inner:Inner, }
        fn main()->u64 { let p=alloc<Outer>(1); p.tag=0; p.inner.pad=0; p.inner.data=[10,20,30,40];
            let view=cut(&mut *p); let answer=view[0]; free(p); return answer; }
        fn cut(p:&mut Outer)->&mut [u64] { return &mut p.inner.data[1usize..]; }",
        20,
    );
    checked(
        &ARRAY_FIELD
            .replace("1usize,3usize", "4usize,4usize")
            .replace("view[0]=42;", "")
            .replace("let answer=view[0];", "let answer=42;"),
        42,
    );
}

#[test]
fn array_slice_range_and_abi_mutations_fail_closed() {
    for source in [
        ARRAY_FIELD.replace("1usize,3usize", "1usize,5usize"),
        ARRAY_FIELD.replace("1usize,3usize", "3usize,1usize"),
        ARRAY_FIELD.replace("1usize,3usize", "4usize,4usize"),
        ARRAY_FIELD.replace("let answer=view[0];", "free(p); let answer=view[0];"),
    ] {
        let output = analyze(&SourceFile::from_text("array-negative.nera", source));
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .unwrap();
        assert!(!report.is_memory_checked_core0());
    }
    let output = checked(ARRAY_FIELD, 42);
    let original = output.vir().unwrap().as_unit();
    let old = &original.runtime.abis.functions[1].signature;
    let params = old
        .parameters()
        .iter()
        .map(|b| b.value().access().unwrap())
        .collect::<Vec<_>>();
    let results = old
        .results()
        .iter()
        .map(|b| b.value().access().unwrap())
        .collect::<Vec<_>>();
    for mutation in 0..4 {
        let mut relation = old.borrow_result().unwrap();
        let BorrowProjection::ArraySlice {
            offset_bytes,
            length,
            end,
            stride_bytes,
            ..
        } = &mut relation.projection
        else {
            unreachable!();
        };
        match mutation {
            0 => *offset_bytes = 0,
            1 => *length = 5,
            2 => *end = BorrowSliceBound::Constant(2),
            3 => *stride_bytes = 16,
            _ => unreachable!(),
        }
        if let Ok(wrong) = VirAbiSignature::classify_with_borrow_result(
            &original.memory,
            &params,
            &results,
            Some(relation),
        ) {
            let mut corrupted = original.clone();
            corrupted.runtime.abis.functions[1].signature = wrong;
            assert!(corrupted.into_validated().is_err(), "mutation {mutation}");
        }
    }
}

const BRANCH_ARRAY_VIEW: &str = "struct Buffer { tag:u64, data:[u64;4], }
    fn main()->u64 { let p=alloc<Buffer>(1); p.tag=0; p.data=[10,42,30,40];
        let view=choose(&mut *p,1usize); let answer=view[0]; free(p); return answer; }
    fn choose(p:&mut Buffer, count:usize)->&mut [u64] {
        if count>0usize { return &mut p.data[1usize..3usize]; }
        return &mut p.data[0usize..0usize];
    }";

#[test]
fn same_array_branch_returns_keep_actual_pointer_and_length() {
    let output = checked(BRANCH_ARRAY_VIEW, 42);
    assert!(matches!(
        output.hir().unwrap().functions()[1]
            .signature
            .borrow_result
            .unwrap()
            .projection,
        BorrowProjection::ArraySlice {
            offset_bytes: 8,
            length: 4,
            stride_bytes: 8,
            start: BorrowSliceBound::ReturnedOffset,
            end: BorrowSliceBound::ReturnedLength,
        }
    ));
    checked(
        &BRANCH_ARRAY_VIEW.replace("*p,1usize", "*p,0usize").replace(
            "let answer=view[0];",
            "let answer=42; assert len(view)==0usize;",
        ),
        42,
    );
    let negative = BRANCH_ARRAY_VIEW.replace("*p,1usize", "*p,0usize");
    let output = analyze(&SourceFile::from_text("empty-branch.nera", negative));
    assert_eq!(output.status(), FrontendStatus::AcceptedProposal);
    assert!(
        !verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default()
        )
        .unwrap()
        .is_memory_checked_core0()
    );
}

#[test]
fn projected_result_deferred_cleanup_crosses_nested_branch_edges() {
    for (first, second) in [(true, true), (true, false), (false, true)] {
        let source = BRANCH_ARRAY_VIEW.replace(
            "let answer=view[0];",
            &format!("let mut answer=0; if {first} {{ if {second} {{ answer=view[0]; }} }}"),
        );
        checked(&source, if first && second { 42 } else { 0 });
    }
}

#[test]
fn returned_array_view_keeps_cleanup_on_every_branch() {
    let source = include_str!("../spec/cases/verify/borrow-array-branches.nera");
    checked(source, 42);
    for arguments in ["0usize,true,true", "1usize,false,true", "1usize,true,false"] {
        checked(&source.replace("1usize,true,true", arguments), 0);
    }
}

#[test]
fn dynamic_return_offset_preserves_alignment_in_child_slices() {
    checked(
        "struct Buffer { cursor:usize, data:[u64;4], }
        fn main()->u64 { return client(2usize); }
        fn client(start:usize)->u64 {
            let mut buffer=Buffer{cursor:start,data:[10,20,42,40]};
            if start<4usize {
                let view=one(&mut buffer);
                let child=&mut view[..];
                let answer=child[0];
                view[0]=answer;
                return view[0];
            }
            return 0;
        }
        fn one(p:&mut Buffer)->&mut [u64]
            requires p.cursor<4usize;
            ensures len(result)==1usize;
        {
            let start=p.cursor;
            let end=start+1usize;
            return &mut p.data[start..end];
        }",
        42,
    );
}
