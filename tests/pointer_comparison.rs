#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{CfgAnalysisConfig, VirExecutionErrorKind, interpret, verify_program};

#[test]
fn same_array_interior_and_one_past_relations() {
    frontend_checks::checked(
        "pointer-comparison.nera",
        include_str!("../spec/cases/verify/pointer-comparison.nera"),
        42,
    );
}

#[test]
fn offsets_are_compared_as_offsets_not_tags_or_permissions() {
    for source in [
        "fn main() -> u64 { let mut a: u64; let x = &raw mut a; let y = &raw a; let d = ptr_byte_distance(x,x+8); if x == y { if d == 8usize { return 42; } } return 0; }",
        "fn main() -> u64 { let a = alloc<u64>(2); let x = &raw *a; let d = ptr_byte_distance(x,x+16); free(a); if d == 16usize { return 42; } return 0; }",
        "struct Pair { a: u64, b: u64, } fn main() -> u64 { let p = Pair { a: 20, b: 22 }; let x = &raw p.a; let y = &raw p.a; if x == y { return 42; } return 0; }",
        "fn main() -> u64 { let a = [[1,2],[3,4]]; let x = &raw a[1][0]; let y = &raw a[1][1]; if ptr_byte_distance(x,y) == 8usize { return 42; } return 0; }",
        "fn main() -> u64 { let a = [1,2]; let s = &a[..]; let x = &raw s[0]; let y = &raw s[1]; if x < y { return 42; } return 0; }",
        "fn main() -> u64 { return check(1usize); } fn check(i: usize) -> u64 { let a = [1,2,3]; if i < len(a) { let x = &raw a[i]; if ptr_byte_distance(x,x+8) == 8usize { return 42; } } return 0; }",
        "fn main() -> u64 { return check(0usize,1usize); } fn check(i: usize,j: usize) -> u64 { let a=[1,2]; if i<len(a) { if j<len(a) { let x=&raw a[i]; let y=&raw a[j]; if x<y { return 42; } } } return 0; }",
    ] {
        frontend_checks::checked("offsets.nera", source, 42);
    }
}

#[test]
fn builtin_checks_types_arity_and_shadowing() {
    frontend_checks::checked(
        "shadow.nera",
        "fn main() -> u64 { return ptr_byte_distance(41); } fn ptr_byte_distance(n: u64) -> u64 { return n+1; }",
        42,
    );
    for body in [
        "let a = 1; let d = ptr_byte_distance(a,a);",
        "let a = 1; let d = ptr_byte_distance(&a,&a);",
        "let a = alloc<u64>(1); let d = ptr_byte_distance(a,a);",
        "let a = 1; let x = &raw a; let d = ptr_byte_distance(x);",
        "let a = 1; let x = &raw a; let ptr_byte_distance = 0; let d = ptr_byte_distance(x,x);",
        "let a = 1; let b = [1,2]; let c = &raw a == &raw b;",
    ] {
        let output = nera::analyze(&nera::SourceFile::from_text(
            "bad-types.nera",
            format!("fn main() -> u64 {{ {body} return 0; }}"),
        ));
        assert_ne!(
            output.status(),
            nera::FrontendStatus::AcceptedProposal,
            "{body}"
        );
    }
}

#[test]
fn independent_parameters_do_not_gain_an_alias_or_domain_promise() {
    let source = "fn main() -> u64 { let a = 1; return compare(&a,&a); } fn compare(a: &u64, b: &u64) -> u64 { let x = &raw *a; let y = &raw *b; if x == y { return 42; } return 0; }";
    let output = frontend_checks::accepted("parameter-alias.nera", source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| matches!(
                o.obligation().kind(),
                nera::ResourceObligationKind::PointerSameInstance { .. }
            ) && o.obligation().status() == nera::ObligationStatus::Unknown)
    );
    // Concrete arguments alias. Callee parameter IDs alone cannot infer this.
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [nera::VirRuntimeValue::U64(42)]
    );
}

#[test]
fn distance_operands_evaluate_once_in_source_order() {
    let output = frontend_checks::accepted(
        "distance-evaluation.nera",
        "fn main() -> u64 { let mut n=0usize; let a=[1,2]; let d=ptr_byte_distance(&raw a[next(&mut n)], &raw a[next(&mut n)]); if n==2usize { if d==8usize { return 42; } } return 0; } fn next(n: &mut usize) -> usize { let index=*n; *n=*n+1usize; return index; }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [nera::VirRuntimeValue::U64(42)]
    );
    // Opaque scalar call results do not prove an index bound in the caller.
    assert!(
        !verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn malformed_pointer_relation_operands_results_and_old_schema_are_rejected() {
    let output = frontend_checks::accepted(
        "relations.nera",
        include_str!("../spec/cases/verify/pointer-comparison.nera"),
    );
    for mutation in 0..4 {
        let mut unit = output.vir().unwrap().as_unit().clone();
        let body = &mut unit.runtime.functions[0].blocks[0];
        let word = body
            .instructions
            .iter()
            .find_map(|i| match i.instruction {
                nera::VirInstruction::Constant {
                    result,
                    value: nera::VirConstant::U64(_),
                } => Some(result.id),
                _ => None,
            })
            .unwrap();
        let op = body
            .instructions
            .iter_mut()
            .find_map(|i| match &mut i.instruction {
                op @ nera::VirInstruction::PointerDistance { .. } => Some(op),
                _ => None,
            })
            .unwrap();
        let nera::VirInstruction::PointerDistance { result, begin, end } = op else {
            unreachable!()
        };
        match mutation {
            0 => *begin = word,
            1 => *end = nera::VirValueId::new(u32::MAX),
            2 => result.ty = nera::VirType::Bool,
            _ => unit.version = nera::VirUnitVersion::V14,
        }
        assert!(unit.into_validated().is_err(), "mutation {mutation}");
    }
}

#[test]
fn canonical_paths_are_exact_bounded_and_missing_paths_do_not_prove_compatibility() {
    use nera::*;
    let access = VirMemoryAccess::core_u64();
    let root = VirNominalPath::root(access);
    let field = root
        .extend(&[VirObjectPathSegment::Field(VirFieldId::new(0))])
        .unwrap();
    let tuple = root
        .extend(&[VirObjectPathSegment::TupleElement(0)])
        .unwrap();
    assert_ne!(field, tuple);
    assert_ne!(field, root);
    assert!(
        root.extend(&[VirObjectPathSegment::ArrayElement(0); 9])
            .is_none()
    );
    assert!(
        root.extend(&[VirObjectPathSegment::TupleElement(u64::MAX)])
            .is_none()
    );
    let output = frontend_checks::accepted(
        "domain-identity.nera",
        "fn main() -> u64 { let a=alloc<u64>(1); let x=&raw *a; let y=&raw *a; let same=x==y; free(a); return 0; }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let instructions = &resolved.runtime().functions[0].blocks[0].instructions;
    let at = instructions
        .iter()
        .position(|i| matches!(i.instruction, VirInstruction::PointerCompare { .. }))
        .unwrap();
    let VirInstruction::PointerCompare {
        result,
        left,
        right,
        ..
    } = instructions[at].instruction
    else {
        unreachable!()
    };
    let before = transfer_instruction_sequence_with_memory(
        &ResourceState::new(),
        &instructions[..at],
        resolved.runtime().memory,
    )
    .unwrap();
    let AbstractValue::Pointer(original) = *before.state().value(right).unwrap() else {
        unreachable!()
    };
    let actual_root = original.paths().domain.unwrap();
    for domain in [
        None,
        actual_root.extend(&[VirObjectPathSegment::Field(VirFieldId::new(0))]),
        actual_root.extend(&[VirObjectPathSegment::TupleElement(0)]),
    ] {
        let mut state = before.state().clone();
        let AbstractValue::Pointer(pointer) = *state.value(right).unwrap() else {
            unreachable!()
        };
        *state.value_mut(right).unwrap() =
            AbstractValue::Pointer(pointer.with_paths(VirPointerPaths {
                object: domain,
                domain,
            }));
        let transfer = transfer_instruction_sequence_with_memory(
            &state,
            &instructions[at..at + 1],
            resolved.runtime().memory,
        )
        .unwrap();
        assert_eq!(
            transfer.state().value(result.id),
            Some(&AbstractValue::Bool(AbstractBool::Unknown))
        );
        assert!(transfer.obligations().iter().any(|o| matches!(o.kind(), ResourceObligationKind::PointerCompatibleDomain { left: a, right: b } if a == left && b == right) && o.status() == ObligationStatus::Unknown));
    }
}

#[test]
fn unsafe_relations_are_not_checked_and_fault_independently() {
    for (source, kind) in [
        (
            "fn main() -> u64 { let a=[[1,2],[3,4]]; let x=&raw a[0][0]; let y=&raw a[1][0]; let c=x<y; return 0; }",
            0,
        ),
        (
            "fn main() -> u64 { let a=[1,2,3]; let s=&a[0..2]; let x=&raw a[0]; let y=&raw s[0]; let c=x==y; return 0; }",
            0,
        ),
        (
            "fn main() -> u64 { let a = alloc<u64>(1); let b = alloc<u64>(1); let x = &raw *a; let y = &raw *b; let c = x == y; free(a); free(b); return 0; }",
            0,
        ),
        (
            "fn main() -> u64 { let a = alloc<u64>(1); let x = &raw *a; free(a); let c = x == x; return 0; }",
            1,
        ),
        (
            "fn main() -> u64 { let a = [1,2]; let x = &raw a[0]; let y = &raw a[1]; let d = ptr_byte_distance(y,x); return 0; }",
            2,
        ),
        (
            "struct Pair { a: u64, b: u64, } fn main() -> u64 { let p = Pair { a: 1, b: 2 }; let x = &raw p.a; let y = &raw p.b; let c = x + 8 == y; return 0; }",
            0,
        ),
    ] {
        let output = frontend_checks::accepted("bad-relation.nera", source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(!report.is_memory_checked_core0(), "{source}");
        let fault = interpret(resolved.runtime()).unwrap_err();
        assert!(
            match kind {
                0 => matches!(
                    fault.kind(),
                    VirExecutionErrorKind::PointerRelationIncompatible
                ),
                1 => matches!(fault.kind(), VirExecutionErrorKind::UseAfterFree { .. }),
                _ => matches!(fault.kind(), VirExecutionErrorKind::PointerDistanceNegative),
            },
            "{source}: {fault:?}"
        );
    }
}
