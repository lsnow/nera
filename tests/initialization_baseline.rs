use nera::{
    CfgAnalysisConfig, FrontendStatus, ObligationStatus, ResourceObligationKind, SourceFile,
    VirInstruction, VirRuntimeValue, analyze, interpret, verify_program,
};

fn accepted(source: &str) -> nera::FrontendOutput {
    let file = SourceFile::from_text("initialization-baseline.nera", source);
    let output = analyze(&file);
    assert_eq!(output, analyze(&file), "baseline lowering replays");
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:#?}",
        output.issues()
    );
    output
}

#[test]
fn initialized_sibling_survives_partial_resource_move() {
    let output = accepted(
        "struct Pair { left: Own<u64>, right: u64, }
        fn main() -> u64 { let owner = alloc<u64>(1); *owner = 40;
        let pair = Pair { left: owner, right: 2 }; let moved = pair.left;
        return pair.right + *moved; }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        result.is_memory_checked_core0(),
        "{:#?}",
        result.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(42)]
    );
}

#[test]
fn allocation_storage_does_not_establish_a_readable_value() {
    let output = accepted("fn main() -> u64 { let owner = alloc<u64>(1); return *owner; }");
    let resolved = output.vir().unwrap().resolve().unwrap();
    let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!result.is_memory_checked_core0());
    assert!(interpret(resolved.runtime()).is_err());
    assert_eq!(
        result,
        verify_program(&resolved, CfgAnalysisConfig::default()).unwrap()
    );
}

#[test]
fn whole_value_move_cannot_read_a_missing_resource_field() {
    let output = accepted(
        "struct Pair { left: Own<u64>, right: u64, }
        fn main() -> u64 { let owner = alloc<u64>(1); *owner = 40;
        let pair = Pair { left: owner, right: 2 }; let moved = pair.left;
        let whole = pair; return whole.right + *moved; }",
    );
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert!(
        !verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert!(interpret(resolved.runtime()).is_err());
}

#[test]
fn borrow_does_not_initialize_the_referent_for_read_or_call() {
    for source in [
        "fn main() -> u64 { let owner = alloc<u64>(1); let r = &*owner; return *r; }",
        "fn main() -> u64 { let owner = alloc<u64>(1); return read(&*owner); }
         fn read(r: &u64) -> u64 { return *r; }",
    ] {
        let output = accepted(source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        assert!(
            !verify_program(&resolved, CfgAnalysisConfig::default())
                .unwrap()
                .is_memory_checked_core0()
        );
        assert!(interpret(resolved.runtime()).is_err());
    }
}

#[test]
fn removing_cleanup_cannot_be_justified_by_value_initialization() {
    let source = "fn main() -> u64 { let owner = alloc<u64>(1); *owner = 42; return 0; }";
    let output = accepted(source);
    let mut unit = output.vir().unwrap().as_unit().clone();
    let mut removed = 0;
    for block in &mut unit.runtime.functions[0].blocks {
        block.instructions.retain(|instruction| {
            let drop = matches!(instruction.instruction, VirInstruction::DropOwn { .. });
            removed += usize::from(drop);
            !drop
        });
    }
    assert_eq!(removed, 1);
    unit.rebuild_source_map_from_runtime("initialization-baseline.nera", source.len());
    let unit = unit.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!result.is_memory_checked_core0());
    assert!(
        result
            .functions()
            .values()
            .any(
                |function| function.cfg().obligations().iter().any(|record| {
                    matches!(
                        record.obligation().kind(),
                        ResourceObligationKind::OwnershipConserved { .. }
                    ) && record.obligation().status() == ObligationStatus::Refuted
                })
            )
    );
}

#[test]
fn bare_loan_requires_a_complete_value_at_formation() {
    for source in [
        "fn main() -> u64 { let owner = alloc<u64>(1); let r = &*owner; return 0; }",
        "struct Pair { owner: Own<u64>, value: u64, }
         fn main() -> u64 { let owner = alloc<u64>(1); *owner = 42;
         let pair = Pair { owner: owner, value: 1 }; let moved = pair.owner;
         let whole = &pair; return 0; }",
    ] {
        let output = accepted(source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        // No dereference executes: formation itself must reject these values.
        assert!(
            !result.is_memory_checked_core0(),
            "{:#?}",
            result.diagnostics()
        );
        assert!(interpret(resolved.runtime()).is_err());
    }
}

#[test]
fn initialized_bytes_do_not_invent_validity_or_a_resource_payload() {
    let mut allocation = nera::AbstractAllocation::new_local(8, 8).unwrap();
    let bytes = nera::ByteRange::new(0, 8).unwrap();
    let key = nera::ResourcePayloadKey::new(
        0,
        nera::VirMemoryAccess::new(nera::VirTypeId::new(0), nera::VirLayoutId::new(0)),
    );
    allocation.mark_initialized(bytes).unwrap();
    assert_eq!(
        allocation.initialization().classify(bytes),
        nera::InitializationClass::Initialized
    );
    assert!(!allocation.valid_value_bytes().contains(bytes));
    assert_eq!(
        allocation.resource_payload(key),
        nera::MovePathState::Unknown
    );
    allocation.mark_valid(bytes).unwrap();
    assert_eq!(
        allocation.resource_payload(key),
        nera::MovePathState::Unknown
    );
    // Knowing a path is absent differs from lacking knowledge of that path.
    assert_eq!(
        nera::MovePathState::Moved.join(&nera::MovePathState::Moved),
        nera::MovePathState::Moved
    );
    assert_eq!(
        nera::MovePathState::Moved.join(&nera::MovePathState::Unknown),
        nera::MovePathState::Unknown
    );
}

#[test]
fn resource_drop_cannot_be_replaced_with_deinitialization() {
    let source = "struct Holder { owner: Own<u64>, }
        fn main() -> u64 { let owner = alloc<u64>(1); *owner = 42;
        let holder = Holder { owner: owner }; return 0; }";
    let output = accepted(source);
    let mut unit = output.vir().unwrap().as_unit().clone();
    let effect = unit.runtime.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
        .rev()
        .find(|instruction| matches!(instruction.instruction, VirInstruction::ObjectDrop { .. }))
        .unwrap();
    let VirInstruction::ObjectDrop {
        pointer,
        permission,
        access,
        ..
    } = effect.instruction
    else {
        unreachable!()
    };
    effect.instruction = VirInstruction::ObjectDeinitialize {
        pointer,
        permission,
        access,
    };
    unit.rebuild_source_map_from_runtime("initialization-baseline.nera", source.len());
    let unit = unit.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let result = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!result.is_memory_checked_core0());
    assert!(
        result
            .functions()
            .values()
            .any(
                |function| function.cfg().obligations().iter().any(|record| {
                    matches!(
                        record.obligation().kind(),
                        ResourceObligationKind::ObjectTriviallyDroppable { .. }
                    ) && record.obligation().status() != ObligationStatus::Proven
                })
            )
    );
}
