#[path = "support/frontend_checks.rs"]
mod frontend_checks;

#[test]
fn checked_slice_reads_writes_and_empty_arguments_compose() {
    frontend_checks::checked(
        "relation-bounds.nera",
        include_str!("../spec/cases/verify/relation-bounds.nera"),
        42,
    );
}

#[test]
fn slice_parameter_must_restore_initialized_valid_elements_before_export() {
    let output = frontend_checks::accepted(
        "slice-restore.nera",
        include_str!("../spec/cases/verify/relation-bounds.nera"),
    );
    let mut unit = output.vir().unwrap().as_unit().clone();
    let mut mutations = 0;
    for instruction in unit.runtime.functions[1]
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.instructions)
    {
        if let nera::VirInstruction::Write {
            pointer,
            permission,
            access,
            ..
        } = instruction.instruction
        {
            instruction.instruction = nera::VirInstruction::ObjectDeinitialize {
                pointer,
                permission,
                access,
            };
            mutations += 1;
        }
    }
    assert_eq!(mutations, 1);
    let unit = unit.into_validated().unwrap();
    let verification =
        nera::verify_program(&unit.resolve().unwrap(), nera::CfgAnalysisConfig::default()).unwrap();
    assert!(!verification.is_memory_checked_core0());
    assert!(
        verification
            .functions()
            .get(&nera::VirFunctionId::new(1))
            .unwrap()
            .cfg()
            .obligations()
            .iter()
            .any(|o| matches!(
                o.obligation().kind(),
                nera::ResourceObligationKind::ObjectValueBytesInitialized { .. }
            ) && !o.obligation().status().is_proven())
    );
}

#[test]
fn querying_an_owner_array_length_does_not_move_or_duplicate_owners() {
    frontend_checks::checked(
        "owner-length.nera",
        "fn main() -> usize { let p=alloc<u64>(1); *p=42;
        let owners=[p]; return len(owners); }",
        1,
    );
}

#[test]
fn metadata_lengths_do_not_copy_or_move_elements() {
    frontend_checks::checked(
        "lengths.nera",
        "fn main() -> u64 { let mut values: [u64; 3];
        let count = len(values); values = [10,20,30]; { let view = &mut values[1..];
        if len(view) == 2usize { view[0] = 42; } } return values[1]; }",
        42,
    );
    // Metadata-only does not mean unevaluated: place projections still execute
    // exactly once. No interprocedural scalar-result precision is assumed here.
    let output = frontend_checks::accepted(
        "length-projection.nera",
        "fn main() -> u64 { let mut count=0; let rows=[[1,2],[3,4]];
        let size=len(rows[next(&mut count)]); return count; }
        fn next(count: &mut u64) -> usize { *count=*count+1; return 0usize; }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        nera::interpret(resolved.runtime()).unwrap().values(),
        [nera::VirRuntimeValue::U64(1)]
    );
}

#[test]
fn slice_callee_proves_its_own_bound() {
    frontend_checks::checked(
        "slice-bound.nera",
        "fn main() -> u64 { let a = [1,42,3]; return read(&a[..],1usize); }
        fn read(view: &[u64], index: usize) -> u64 {
            if index < len(view) { return view[index]; } return 0;
        }",
        42,
    );
    // 7.4.7 resolves the actual parent from parameter authority.
    frontend_checks::checked(
        "callee-prefix.nera",
        "fn main() -> u64 { let a=[42,1,2]; return prefix(&a[..],2usize); }
        fn prefix(view: &[u64], end: usize) -> u64 {
            if end > 0usize { if end <= len(view) {
                let part=&view[..end]; return part[0];
            } } return 0;
        }",
        42,
    );
}

#[test]
fn symbolic_containment_has_context_bound_replayable_evidence() {
    use nera::verifier::relation::{RelationRule, replay_relation_evidence};
    use nera::{CfgAnalysisConfig, verify_program};
    let output = frontend_checks::accepted(
        "evidence.nera",
        include_str!("../spec/cases/verify/relation-bounds.nera"),
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let config = CfgAnalysisConfig::default();
    let result = verify_program(&resolved, config).unwrap();
    assert!(result.is_memory_checked_core0());
    let evidence = result
        .functions()
        .values()
        .flat_map(|f| f.cfg().relation_evidence())
        .find(|e| {
            e.rule == RelationRule::SymbolicPermissionContainment
                && matches!(e.instruction, nera::VirInstruction::Write { .. })
                && e.bounds.iter().any(|b| b.difference.is_some())
        })
        .unwrap();
    assert!(replay_relation_evidence(&resolved, config, evidence).unwrap());
    let mut forged = evidence.clone();
    forged.bounds[1].threshold = Some(123);
    assert!(!replay_relation_evidence(&resolved, config, &forged).unwrap());
    let no_relations = CfgAnalysisConfig {
        relation_limits: nera::verifier::relation::difference::DifferenceLimits {
            max_variables: 0,
            ..config.relation_limits
        },
        ..config
    };
    assert!(
        !verify_program(&resolved, no_relations)
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn absent_wrong_and_wrapping_bounds_never_grant_slice_access() {
    for condition in ["true", "index <= len(view)", "index + 1usize < len(view)"] {
        let source = format!("fn main() -> u64 {{ let a=[1,2]; return read(&a[..],18446744073709551615usize); }}
            fn read(view: &[u64], index: usize) -> u64 {{ if {condition} {{ return view[index]; }} return 0; }}");
        let output = frontend_checks::accepted("bad-bound.nera", &source);
        let result = nera::verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            nera::CfgAnalysisConfig::default(),
        )
        .unwrap();
        assert!(!result.is_memory_checked_core0(), "{condition}");
    }
}

#[test]
fn evaluated_unit_view_has_exact_length_and_empty_views_are_not_elements() {
    frontend_checks::checked(
        "unit-view.nera",
        "fn main() -> u64 { return read(1usize); }
        fn read(i: usize) -> u64 { let a=[1,42,3]; if i < len(a) {
            let view = &a[i..i+1usize]; let count = len(view); return view[0];
        } return 0; }",
        42,
    );
    frontend_checks::checked(
        "empty-callee.nera",
        "fn main() -> u64 { let a=[1,2]; return read(&a[2..2],0usize); }
        fn read(view: &[u64], i:usize) -> u64 { if i < len(view) { return view[i]; } return 7; }",
        7,
    );
}

#[test]
fn length_name_resolution_and_types_do_not_introduce_implicit_pointer_access() {
    frontend_checks::checked(
        "user-len.nera",
        "fn main() -> u64 { return len(41); } fn len(n:u64) -> u64 { return n+1; }",
        42,
    );
    for source in [
        "fn main()->usize { let p=alloc<u64>(1); return len(p); }",
        "fn main()->usize { let a=[1,2]; let len=3; return len(a); }",
        "fn main()->usize { return len(1); }",
        "fn main()->usize { return len(); }",
    ] {
        let output = nera::analyze(&nera::SourceFile::from_text("bad-length.nera", source));
        assert_ne!(output.status(), nera::FrontendStatus::AcceptedProposal);
    }
}
