use super::*;

#[test]
fn independently_rejects_forged_length_snapshot_scope_and_type() {
    let output = crate::analyze(&crate::SourceFile::from_text(
        "length-hir.nera",
        "fn main()->u64 {let a=[1,2]; f(&a[0..2]); return 0;} fn f(p:&[u64]) requires len(p)==2usize; {return;}",
    ));
    let program = output.hir().unwrap();
    let term = program
        .specs()
        .terms
        .iter()
        .find(|t| {
            matches!(
                t.kind,
                HirSpecTermKind::Snapshot(HirSpecSnapshot::Length { .. })
            )
        })
        .unwrap();
    let HirSpecTermKind::Snapshot(snapshot @ HirSpecSnapshot::Length { function, .. }) = term.kind
    else {
        unreachable!()
    };
    assert!(validate_spec_snapshot(program, term, snapshot));
    for forged in [
        HirSpecSnapshot::Length {
            function,
            parameter: None,
            entry: false,
        },
        HirSpecSnapshot::Length {
            function,
            parameter: Some(99),
            entry: false,
        },
        HirSpecSnapshot::Length {
            function,
            parameter: Some(0),
            entry: true,
        },
        HirSpecSnapshot::Length {
            function,
            parameter: None,
            entry: true,
        },
    ] {
        assert!(!validate_spec_snapshot(program, term, forged));
    }
    let mut term = term.clone();
    term.ty = program
        .types()
        .iter()
        .find(|ty| matches!(ty.kind, HirTypeKind::Bool))
        .unwrap()
        .id;
    assert!(!validate_spec_snapshot(program, &term, snapshot));
}

#[test]
fn independently_rejects_forged_memory_snapshot_visibility_and_type() {
    let output = crate::analyze(&crate::SourceFile::from_text(
        "memory-hir.nera",
        "fn main()->u64 {let mut n=41; f(&mut n); return 0;} fn f(p:&mut u64) requires *p==41; {*p=42; return;}",
    ));
    let program = output.hir().unwrap();
    let term = program
        .specs()
        .terms
        .iter()
        .find(|t| {
            matches!(
                t.kind,
                HirSpecTermKind::Snapshot(HirSpecSnapshot::Memory { .. })
            )
        })
        .unwrap();
    let HirSpecTermKind::Snapshot(snapshot) = term.kind else {
        unreachable!()
    };
    assert!(validate_spec_snapshot(program, term, snapshot));
    let HirSpecSnapshot::Memory { function, .. } = snapshot else {
        unreachable!()
    };
    for forged in [
        HirSpecSnapshot::Memory {
            function,
            parameter: Some(0),
            old: true,
            projection: crate::SpecMemoryProjection::Cell,
        },
        HirSpecSnapshot::Memory {
            function,
            parameter: Some(99),
            old: false,
            projection: crate::SpecMemoryProjection::Cell,
        },
        HirSpecSnapshot::Memory {
            function,
            parameter: None,
            old: false,
            projection: crate::SpecMemoryProjection::Cell,
        },
        HirSpecSnapshot::Memory {
            function,
            parameter: Some(0),
            old: false,
            projection: crate::SpecMemoryProjection::Field(crate::HirFieldId::new(99)),
        },
    ] {
        assert!(!validate_spec_snapshot(program, term, forged));
    }
    let mut term = term.clone();
    term.ty = program
        .types()
        .iter()
        .find(|ty| matches!(ty.kind, HirTypeKind::Bool))
        .unwrap()
        .id;
    assert!(!validate_spec_snapshot(program, &term, snapshot));
}
