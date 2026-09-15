use nera::*;
#[path = "support/loop_arena.rs"]
mod fixture;
#[path = "support/runtime_origins.rs"]
mod runtime_origins;
use fixture::INITIALIZE;

fn checked(source: &str) -> FrontendOutput {
    let output = analyze(&SourceFile::from_text("loop-arena.nera", source));
    let unit = output
        .vir()
        .unwrap_or_else(|| panic!("{:?}", output.issues()));
    let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    output
}

#[test]
fn raw_fragment_initialization_preserves_adjacent_initialized_storage() {
    for original in [INITIALIZE.to_owned(), fixture::initialized_update()] {
        for end in [1, 2, 6, 7] {
            let source =
                original.replacen("initialize(6usize)", &format!("initialize({end}usize)"), 1);
            let explicit = checked(&source);
            let automatic = checked(&fixture::erase_invariants(&source));
            let automatic_report = verify_program(
                &automatic.vir().unwrap().resolve().unwrap(),
                Default::default(),
            )
            .unwrap();
            assert!(
                automatic_report
                    .functions()
                    .values()
                    .flat_map(|f| f.cfg().loop_candidate_attempts())
                    .any(|a| !a.selected.is_empty() && a.rejected.is_empty())
            );
            assert_eq!(
                runtime_origins::runtime_with_resolved_origins(explicit.vir().unwrap()),
                runtime_origins::runtime_with_resolved_origins(automatic.vir().unwrap())
            );
            assert_eq!(
                interpret(explicit.vir().unwrap().resolve().unwrap().runtime())
                    .unwrap()
                    .values(),
                [VirRuntimeValue::U64(if end == 1 { 16 } else { 58 })]
            );
            let unit = explicit.vir().unwrap();
            assert!(unit.as_unit().specs.trust_entries().is_empty());
            let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
            assert!(
                report
                    .functions()
                    .values()
                    .flat_map(|f| f.cfg().obligations())
                    .any(|o| matches!(
                        o.obligation().kind(),
                        ResourceObligationKind::LoopResourcesPreserved { .. }
                    ) && o.obligation().is_proven())
            );
        }
    }
}

fn unproved(source: &str) {
    let output = analyze(&SourceFile::from_text("bad-loop-arena.nera", source));
    let unit = output
        .vir()
        .unwrap_or_else(|| panic!("expected verifier rejection: {:?}", output.issues()));
    let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
    assert!(!report.is_memory_checked_core0(), "{source}");
    assert!(
        report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| !o.obligation().is_proven())
    );
}

#[test]
fn uninitialized_holes_remaining_storage_and_empty_fragment_are_not_readable() {
    for source in [
        INITIALIZE
            .replace("p[i] = 42;", "if i != 2usize { p[i] = 42; }")
            .replace("let value = p[1];", "let value = p[2];"),
        INITIALIZE.replace("let value = p[1];", "let value = p[6];"),
        INITIALIZE.replace("if end == 1usize { free(p); return left + right; }", ""),
        INITIALIZE.replace("i = i + 1usize;", "i = i + 2usize;"),
        INITIALIZE.replace("p[i] = 42;", "if i == 1usize { break; } p[i] = 42;"),
        INITIALIZE.replace("p[i] = 42;", "p[i + 1usize] = 42;"),
    ] {
        unproved(&source);
        unproved(&fixture::erase_invariants(&source));
    }
}

#[test]
fn invalid_capacity_cannot_satisfy_the_core_interface() {
    for end in [0, 8] {
        unproved(&INITIALIZE.replacen("initialize(6usize)", &format!("initialize({end}usize)"), 1));
    }
    let output = checked(&fixture::capacity_failure());
    assert_eq!(
        interpret(output.vir().unwrap().resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(0)]
    );
}

#[test]
fn outstanding_adjacent_views_exclude_neighbor_writes() {
    let source = fixture::ADJACENT_VIEWS;
    checked(source);
    let bad = source.replace("p[i]=42;", "p[0]=99; p[i]=42;");
    let output = analyze(&SourceFile::from_text("neighbor-write.nera", &bad));
    let report = verify_program(
        &output.vir().unwrap().resolve().unwrap(),
        Default::default(),
    )
    .unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|p| !p.obligation().is_proven())
    );
}

#[test]
fn partial_exit_reads_only_the_completed_prefix_and_releases_storage() {
    let source = INITIALIZE.replace("p[i] = 42;", "if i == 3usize { break; } p[i] = 42;");
    checked(&source);
    unproved(&source.replace("let value = p[1];", "let value = p[3];"));
}

#[test]
fn allocation_abort_has_no_normal_initialized_result() {
    let output = checked(INITIALIZE);
    let error = interpret_with_config(
        output.vir().unwrap().resolve().unwrap().runtime(),
        VirInterpreterConfig {
            max_allocation_bytes: 0,
            ..Default::default()
        },
    )
    .unwrap_err();
    assert!(matches!(
        error.kind(),
        VirExecutionErrorKind::AllocationFailure { .. }
    ));
}

#[test]
fn early_free_and_duplicate_return_do_not_restore_authority() {
    for source in [
        INITIALIZE.replace("p[i] = 42;", "free(p); p[i] = 42;"),
        INITIALIZE.replace("let value = p[1];", "free(p); let value = p[1];"),
        INITIALIZE.replace("free(p);", "free(p); free(p);"),
        fixture::ADJACENT_VIEWS.replace("p[i]=42;", "free(p); p[i]=42;"),
    ] {
        let output = analyze(&SourceFile::from_text("arena-lifetime.nera", &source));
        if let Some(unit) = output.vir() {
            assert!(
                !verify_program(&unit.resolve().unwrap(), Default::default())
                    .is_ok_and(|r| r.is_memory_checked_core0())
            );
        } else {
            assert!(!output.issues().is_empty());
        }
    }
}
