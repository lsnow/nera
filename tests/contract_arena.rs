use nera::*;
const SOURCE: &str = include_str!("../spec/cases/verify/contract-arena.nera");

fn check(source: &str) -> (frontend::FrontendOutput, bool) {
    let output = analyze(&SourceFile::from_text("contract-arena.nera", source));
    let unit = output
        .vir()
        .unwrap_or_else(|| panic!("{:?}", output.issues()));
    let report = verify_program(&unit.resolve().unwrap(), Default::default());
    let checked = match report {
        Ok(report) => {
            if !report.is_memory_checked_core0() {
                for diagnostic in report.diagnostics() {
                    eprintln!("{}", diagnostic.message());
                }
            }
            report.is_memory_checked_core0()
        }
        Err(error) => {
            eprintln!("{error:?}");
            false
        }
    };
    (output, checked)
}

#[test]
fn two_reservations_preserve_earlier_views_and_capacity_failure() {
    let (output, checked) = check(SOURCE);
    assert!(checked);
    let unit = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        interpret(unit.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(49)]
    );
}

#[test]
fn reservation_checks_real_parameters_including_empty_full_and_reverse_ranges() {
    let reserve = &SOURCE[SOURCE.find("fn reserve(").unwrap()..SOURCE.find("fn take(").unwrap()];
    for (cursor, capacity, end, allowed) in [
        (0u64, 6u64, 0u64, true),
        (4, 6, 3, false),
        (4, 6, 6, true),
        (6, 6, 7, false),
        (u64::MAX, u64::MAX, u64::MAX, true),
    ] {
        let expected = if allowed { end } else { cursor };
        let source = format!(
            "fn main()->u64 {{let mut cursor={cursor}usize; if reserve(cursor,{capacity}usize,{end}usize) {{cursor={end}usize;}} if cursor=={expected}usize {{return 42;}} return 99;}} {reserve}"
        );
        let (output, checked) = check(&source);
        assert!(checked, "{source}");
        assert_eq!(
            interpret(output.vir().unwrap().resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [VirRuntimeValue::U64(42)]
        );
    }
}

#[test]
fn invalid_reservation_or_hidden_write_cannot_publish_a_summary() {
    for bad in [
        SOURCE.replace("return false;", "return true;"),
        SOURCE.replace("return storage;", "storage[0]=9; return storage;"),
    ] {
        let (output, checked) = check(&bad);
        assert!(!checked);
        let report = verify_program(
            &output.vir().unwrap().resolve().unwrap(),
            Default::default(),
        )
        .unwrap();
        assert!(
            report
                .functions()
                .values()
                .flat_map(|f| f.postconditions())
                .any(|c| !c.check().status.is_proven())
        );
    }
}

#[test]
fn overlapping_live_views_and_early_parent_reset_fail() {
    for bad in [
        SOURCE.replace("parent[next..cursor]", "parent[0usize..cursor]"),
        SOURCE.replace("middle[0] = 30;", "middle[0] = 30; parent[0]=99;"),
    ] {
        let output = analyze(&SourceFile::from_text("arena-overlap.nera", &bad));
        if let Some(unit) = output.vir() {
            assert!(
                !verify_program(&unit.resolve().unwrap(), Default::default())
                    .unwrap()
                    .is_memory_checked_core0()
            );
        } else {
            assert!(!output.issues().is_empty());
        }
    }
}

#[test]
fn mutable_inputs_cannot_be_substituted_for_historical_parameters() {
    let reserve = "fn reserve(cursor:usize,capacity:usize,end:usize)->bool
        ensures !result || (cursor<=end && end<=capacity);
        {let mut current=cursor; if end<=capacity {current=0usize; if current<=end {return true;}} return false;}";
    let (_, checked) = check(&format!(
        "fn main()->u64 {{if reserve(0usize,6usize,2usize) {{return 42;}} return 0;}} {reserve}"
    ));
    assert!(!checked); // The body must prove the postcondition for all entry cursors.
}

#[test]
fn raw_duplicate_return_of_a_loan_is_not_resource_creation() {
    // Two sequential loans from the same backing, independently of source
    // arena contracts and inferred call-return cleanup.
    let (output, checked) = check(
        "fn main()->u64 {let mut value=1; {let a=&mut value; *a=2;} {let b=&mut value; *b=3;} return value;}",
    );
    assert!(checked);
    let mut raw = output.vir().unwrap().as_unit().clone();
    let function = raw
        .runtime
        .functions
        .iter_mut()
        .find(|f| {
            f.blocks
                .iter()
                .flat_map(|b| &b.instructions)
                .filter(|i| matches!(i.instruction, VirInstruction::LoanEnd { .. }))
                .count()
                >= 2
        })
        .unwrap();
    let mut ends = function
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.instructions)
        .filter_map(|i| {
            if let VirInstruction::LoanEnd { effect } = &mut i.instruction {
                Some(effect)
            } else {
                None
            }
        });
    let first = *ends.next().unwrap();
    *ends.next().unwrap() = first;
    // Structural linearity or canonical transfer must reject the duplicated end.
    if let Ok(unit) = raw.into_validated() {
        assert!(
            !verify_program(&unit.resolve().unwrap(), Default::default())
                .is_ok_and(|r| r.is_memory_checked_core0())
        );
    }
}

#[test]
fn active_returned_reference_does_not_allow_freeing_its_owner() {
    let source = "fn main()->u64 {let p=alloc<u64>(1); *p=7; let view=hold(&mut *p); free(p); return *view;}
        fn hold(p:&mut u64)->&mut u64 ensures readable(result,0..1); reads (); writes (); {return p;}";
    let output = analyze(&SourceFile::from_text("arena-free.nera", source));
    if let Some(unit) = output.vir() {
        assert!(
            !verify_program(&unit.resolve().unwrap(), Default::default())
                .unwrap()
                .is_memory_checked_core0()
        );
    } else {
        assert!(!output.issues().is_empty());
    }
}

#[test]
fn allocation_abort_does_not_produce_normal_return_guarantees() {
    let source = "fn main()->u64 {let p=make(); free(p); return 42;}
        fn make()->Own<u64> ensures readable(result,0..1); {let p=alloc<u64>(1); *p=7; return p;}";
    let (output, checked) = check(source);
    assert!(checked);
    let unit = output.vir().unwrap().resolve().unwrap();
    let error = interpret_with_config(
        unit.runtime(),
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
