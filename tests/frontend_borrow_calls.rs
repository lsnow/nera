use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, VirRuntimeValue, analyze, interpret,
    verify_program,
};

fn checked(source: &str, expected: u64) {
    let output = analyze(&SourceFile::from_text("borrow-call.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{:#?}",
        output.issues()
    );
    let unit = output.vir().unwrap();
    let resolved = unit.resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        verification.is_memory_checked_core0(),
        "{:#?}",
        verification.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(expected)]
    );
}

#[test]
fn shared_parameter_preserves_caller_authority() {
    checked(
        "fn main() -> u64 { let value = 42; let r = &value; let answer = read(r); return answer + *r; } fn read(r: &u64) -> u64 { return *r; }",
        84,
    );
}

#[test]
fn mutable_parameter_restores_caller_authority() {
    checked(
        "fn main() -> u64 { let mut value = 1; let r = &mut value; write(r); return *r; } fn write(r: &mut u64) { *r = 42; return; }",
        42,
    );
}

#[test]
fn moved_parameter_endpoint_can_be_restored() {
    checked(
        "fn main() -> u64 { let mut value = 1; write(&mut value); return value; } fn write(r: &mut u64) { let moved = r; *moved = 42; return; }",
        42,
    );
}

#[test]
fn returned_shared_reference_keeps_source_region() {
    checked(
        "fn main() -> u64 { let value = 42; let r = identity(&value); return *r; } fn identity(r: &u64) -> &u64 { return r; }",
        42,
    );
}

#[test]
fn returned_mutable_reference_transfers_authority() {
    checked(
        "fn main() -> u64 { let mut value = 1; let r = identity(&mut value); *r = 42; return *r; } fn identity(r: &mut u64) -> &mut u64 { return r; }",
        42,
    );
}

#[test]
fn direct_place_borrow_ends_after_call() {
    checked(
        "fn main() -> u64 { let mut value = 1; write(&mut value); return value; } fn write(r: &mut u64) { *r = 42; return; }",
        42,
    );
}

#[test]
fn recursive_borrow_calls_use_the_signature_skeleton() {
    checked(
        "fn main() -> u64 { let value = 42; return recurse(&value, 0); } fn recurse(r: &u64, n: u64) -> u64 { if n == 3 { return *r; } return recurse(r, n + 1); }",
        42,
    );
}

#[test]
fn overlapping_shared_arguments_are_valid() {
    checked(
        "fn main() -> u64 { let value = 21; let r = &value; return sum(r, r); } fn sum(a: &u64, b: &u64) -> u64 { return *a + *b; }",
        42,
    );
}

#[test]
fn slice_identity_preserves_length() {
    checked(
        "fn main() -> u64 { let values = [10, 20, 30]; let view = identity(&values[1..]); return view[1]; } fn identity(view: &[u64]) -> &[u64] { return view; }",
        30,
    );
}

#[test]
fn local_results_fail_closed() {
    for source in [
        "fn bad() -> &u64 { let value = 42; return &value; }",
        "fn bad(r: &u64) -> &u64 { let value = 42; return &value; }",
    ] {
        let output = analyze(&SourceFile::from_text("escape.nera", source));
        assert_ne!(
            output.status(),
            FrontendStatus::AcceptedProposal,
            "{source}"
        );
    }
}

#[test]
fn returned_reference_still_excludes_owner_writes() {
    let output = analyze(&SourceFile::from_text(
        "escape-use.nera",
        "fn main() -> u64 { let mut value = 1; let r = identity(&value); value = 2; return *r; } fn identity(r: &u64) -> &u64 { return r; }",
    ));
    let unit = output.vir().expect("unsafe use remains verifier input");
    assert!(
        !verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn returned_view_identity_is_rechecked_independently_of_hir() {
    let output = analyze(&SourceFile::from_text(
        "mutated-view.nera",
        "fn main() -> u64 { let value = 42; let r = identity(&value); return *r; } fn identity(r: &u64) -> &u64 { let value = 9; let other = &value; return r; }",
    ));
    let mut unit = output.vir().unwrap().as_unit().clone();
    let body = &mut unit.runtime.functions[1];
    let other = body
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match instruction.instruction {
            nera::VirInstruction::LoanBegin {
                reference_result, ..
            } => Some(reference_result.id),
            _ => None,
        })
        .unwrap();
    for block in &mut body.blocks {
        if let nera::VirTerminator::Return { values } = &mut block.terminator.terminator {
            values[0] = other;
        }
    }
    assert!(
        unit.into_validated().is_err(),
        "a locally allocated pointer cannot satisfy the parameter-view skeleton"
    );
}

#[test]
fn missing_parameter_region_cannot_admit_loan_authority() {
    let output = analyze(&SourceFile::from_text(
        "missing-region.nera",
        "fn main() -> u64 { let value = 42; return read(&value); } fn read(r: &u64) -> u64 { return *r; }",
    ));
    let mut unit = output.vir().unwrap().as_unit().clone();
    // Preserve the caller's inferred region while removing the callee binder.
    let regions = unit
        .borrows
        .regions()
        .iter()
        .filter(|region| region.owner == nera::VirFunctionId::new(0))
        .cloned()
        .collect::<Vec<_>>();
    unit.borrows = nera::VirBorrowEnvironment::from_tables(regions, Vec::new());
    match unit.into_validated() {
        Err(_) => {}
        Ok(unit) => {
            let resolved = unit.resolve().unwrap();
            assert!(
                !verify_program(&resolved, CfgAnalysisConfig::default())
                    .unwrap()
                    .is_memory_checked_core0()
            );
            assert!(interpret(resolved.runtime()).is_err());
        }
    }
}

#[test]
fn interface_loans_obey_analysis_budgets() {
    let output = analyze(&SourceFile::from_text(
        "budget.nera",
        "fn main() -> u64 { let value = 42; return read(&value); } fn read(r: &u64) -> u64 { return *r; }",
    ));
    let unit = output.vir().unwrap();
    let config = CfgAnalysisConfig {
        max_active_loans_per_case: 0,
        ..CfgAnalysisConfig::default()
    };
    assert!(
        !verify_program(&unit.resolve().unwrap(), config)
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn recursive_returned_reference_and_mutable_slice_preserve_the_view() {
    checked(
        "fn main() -> u64 { let mut values = [10, 20, 30]; let view = identity(&mut values[1..]); view[0] = 12; let r = recurse(&values[1], 0); return *r; } fn identity(view: &mut [u64]) -> &mut [u64] { return view; } fn recurse(r: &u64, n: u64) -> &u64 { if n == 3 { return r; } return recurse(r, n + 1); }",
        12,
    );
}

#[test]
fn offset_and_dynamic_envelope_survive_nested_calls() {
    checked(
        "fn main() -> u64 { let mut values = [1, 2, 3]; let index = 1usize; let r = &mut values[index]; write(r); return *r; } fn write(r: &mut u64) { nested(r); return; } fn nested(r: &mut u64) { *r = 42; return; }",
        42,
    );
}

#[test]
fn callee_cannot_deinitialize_the_exported_referent() {
    let output = analyze(&SourceFile::from_text(
        "deinitialize.nera",
        "fn main() -> u64 { let mut value = 1; write(&mut value); return value; } fn write(r: &mut u64) { *r = 42; return; }",
    ));
    let mut unit = output.vir().unwrap().as_unit().clone();
    let mut mutated = false;
    for instruction in unit.runtime.functions[1]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
    {
        if let nera::VirInstruction::Store {
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
            mutated = true;
        }
    }
    assert!(mutated);
    let validated = unit
        .into_validated()
        .expect("deinitialization is structurally valid VIR");
    assert!(
        !verify_program(&validated.resolve().unwrap(), CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn mutable_authority_cannot_be_aliased_by_a_shared_call_signature() {
    let output = analyze(&SourceFile::from_text(
        "kind-mutation.nera",
        "fn main() -> u64 { let mut value = 1; let r = &mut value; return write(r); } fn write(r: &mut u64) -> u64 { return *r; } fn read(r: &u64) -> u64 { return *r; }",
    ));
    let mut unit = output.vir().unwrap().as_unit().clone();
    let callee = unit.runtime.functions[2].clone();
    let abi = unit
        .runtime
        .abis
        .function(callee.id)
        .unwrap()
        .signature
        .clone();
    for instruction in unit.runtime.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.instructions)
    {
        if let nera::VirInstruction::Call { target, .. } = &mut instruction.instruction {
            target.symbol = callee.name.clone();
            target.contract = callee.contract;
            target.signature = callee.signature.clone();
            target.abi = Some(abi.clone());
        }
    }
    let validated = unit.into_validated().expect("physical call shapes match");
    let resolved = validated.resolve().unwrap();
    assert!(
        !verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert!(interpret(resolved.runtime()).is_err());
}

#[test]
fn owner_permission_does_not_satisfy_a_safe_reference_parameter() {
    use nera::{
        AbstractAllocationId, AbstractByteRange, AbstractPermission, AbstractPointer,
        AbstractProvenance, AbstractValue, AccessPermission, ByteRange, FreeCapability,
        GuaranteedAlignment, ObligationStatus, ResourceObligationKind, ResourceState, U64Interval,
        VirInstruction,
    };
    let output = analyze(&SourceFile::from_text(
        "owner-as-borrow.nera",
        "fn main() -> u64 { let value = 42; return read(&value); } fn read(r: &u64) -> u64 { return *r; }",
    ));
    let unit = output.vir().unwrap();
    let instruction = unit.runtime().functions[0]
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .find(|instruction| matches!(instruction.instruction, VirInstruction::Call { .. }))
        .unwrap();
    let VirInstruction::Call {
        arguments, target, ..
    } = &instruction.instruction
    else {
        unreachable!()
    };
    let nera::VirType::Pointer { access } = target.signature.parameters[0] else {
        unreachable!()
    };
    let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
    let mut state = ResourceState::new();
    state
        .define_value(
            arguments[0],
            AbstractValue::Pointer(
                AbstractPointer::new(
                    provenance,
                    U64Interval::exact(0),
                    GuaranteedAlignment::new(8).unwrap(),
                )
                .with_memory_access(Some(access)),
            ),
        )
        .unwrap();
    state
        .define_value(
            arguments[1],
            AbstractValue::Permission(AbstractPermission::new(
                provenance,
                AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap()),
                AccessPermission::Write,
                FreeCapability::Yes,
            )),
        )
        .unwrap();
    let transferred =
        nera::transfer_instruction_with_memory(&state, instruction, unit.runtime().memory).unwrap();
    assert!(transferred.obligations().iter().any(|obligation| matches!(obligation.kind(), ResourceObligationKind::LoanCompatible { loan: None, permission, .. } if permission == arguments[1]) && obligation.status() == ObligationStatus::Refuted));
}
