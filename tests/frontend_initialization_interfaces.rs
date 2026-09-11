#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{
    CfgAnalysisConfig, FrontendStatus, SourceFile, VirInstruction, VirUnit, analyze, interpret,
    verify_program,
};

fn checked(source: &str) {
    frontend_checks::checked("initialization-interface.nera", source, 42);
}

fn accepted(source: &str) -> nera::FrontendOutput {
    frontend_checks::accepted("initialization-interface.nera", source)
}

fn rejected(unit: VirUnit, runtime_fault: bool) -> nera::ProgramVerification {
    let validated = unit
        .into_validated()
        .expect("mutation must reach semantic checking");
    let resolved = validated.resolve().unwrap();
    let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        !verification.is_memory_checked_core0(),
        "{:?}",
        verification
    );
    if runtime_fault {
        assert!(interpret(resolved.runtime()).is_err());
    }
    verification
}

const BORROW_REPAIR: &str = "struct Pair { left: u64, right: u64, }
    fn main() -> u64 { let mut p: Pair; p.left = 1; p.right = 2; repair(&mut p, true); return 42; }
    fn repair(p: &mut Pair, branch: bool) { if branch { p.left = 20; return; } p.right = 22; return; }";

#[test]
fn initialized_sibling_borrow_and_whole_borrow_have_distinct_entry_requirements() {
    checked(
        "struct Pair { left: u64, right: u64, } fn main() -> u64 {
      let mut p: Pair; p.left = 40; let a = read(&p.left); p.right = 2; return a + p.right; }
      fn read(p: &u64) -> u64 { return *p; }",
    );
    checked("struct Pair { left: u64, right: u64, } fn main() -> u64 {
      let mut p: Pair; p.left = 1; update(&mut p.left); p.right = 0; return read(&p); }
      fn update(p: &mut u64) { *p = 42; return; } fn read(p: &Pair) -> u64 { return p.left + p.right; }");
    for body in [
        "let r = &p; return 42;",
        "read(&p); return 42;",
        "update(&mut p.right); return 42;",
    ] {
        let source = format!("struct Pair {{ left: u64, right: u64, }} fn main() -> u64 {{ let mut p: Pair; p.left = 42; {body} }}
            fn read(p: &Pair) {{ return; }} fn update(p: &mut u64) {{ *p = 42; return; }}");
        rejected(accepted(&source).vir().unwrap().as_unit().clone(), true);
    }
}

#[test]
fn deferred_heap_loop_and_recursive_values_cross_complete_interfaces() {
    checked("struct Pair { left: u64, right: u64, } fn main() -> u64 { let p = make(true);
      return recurse(p, false); } fn make(b: bool) -> Pair { let mut p: Pair;
      if b { p.left = 20; p.right = 22; return p; } p.left = 1; p.right = 41; return p; }
      fn recurse(p: Pair, stop: bool) -> u64 { if stop { return p.left + p.right; } return recurse(p, true); }");
    checked("fn main() -> u64 { let p = alloc<[u64; 4]>(1); for i in 0usize..4usize { p[i] = 42; }
      let value = pass(*p); free(p); return value[3]; } fn pass(a: [u64; 4]) -> [u64; 4] { return a; }");
    checked(
        "struct Padded { flag: bool, word: u64, } fn main() -> u64 { let mut p: Padded;
      p.flag = true; p.word = 1; repair(&mut p); return p.word; }
      fn repair(p: &mut Padded) { p.word = 42; return; }",
    );
    checked(BORROW_REPAIR);
    checked(
        "struct Padded { flag: bool, left: u64, right: u64, } fn main() -> u64 {
      let p = make(); return consume(p); } fn make() -> Padded { let mut p: Padded;
      p.flag = true; p.left = 20; p.right = 22; return p; }
      fn consume(p: Padded) -> u64 { return p.left + p.right; }",
    );
}

#[test]
fn owned_aggregate_partial_move_and_refill_precedes_return_transfer() {
    checked(
        "struct Package { owner: Own<u64>, word: u64, } fn main() -> u64 {
      let a = alloc<u64>(1); *a = 40; let mut p: Package; p.owner = a; p.word = 2;
      let returned = repair(p, true); let owner = returned.owner; return *owner + returned.word; }
      fn repair(p: Package, branch: bool) -> Package { let mut v = p; let moved = v.owner;
      if branch { v.owner = moved; return v; } v.owner = moved; return v; }",
    );
}

#[test]
fn every_return_must_restore_borrowed_value_even_when_caller_ignores_it() {
    for take_bad_arm in [true, false] {
        let source = BORROW_REPAIR.replace(
            "repair(&mut p, true)",
            &format!("repair(&mut p, {take_bad_arm})"),
        );
        let mut unit = accepted(&source).vir().unwrap().as_unit().clone();
        let mut changed = false;
        for block in &mut unit.runtime.functions[1].blocks {
            for item in &mut block.instructions {
                if !changed
                    && let VirInstruction::Store {
                        pointer,
                        permission,
                        access,
                        ..
                    } = item.instruction
                {
                    item.instruction = VirInstruction::ObjectDeinitialize {
                        pointer,
                        permission,
                        access,
                    };
                    changed = true;
                }
            }
        }
        assert!(changed);
        unit.rebuild_source_map_from_runtime("borrow-exit-mutation.vir", 10000);
        let verification = rejected(unit, take_bad_arm);
        let obligations = verification.functions()[&nera::VirFunctionId::new(1)]
            .cfg()
            .obligations();
        assert!(obligations.iter().any(|record| matches!(
            record.obligation().kind(),
            nera::ResourceObligationKind::ObjectValueBytesInitialized { .. }
        ) && !record.obligation().is_proven()));
        assert!(
            obligations
                .iter()
                .filter(|record| matches!(
                    record.obligation().kind(),
                    nera::ResourceObligationKind::LoanEndedExactlyOnce { .. }
                ))
                .all(|record| record.obligation().is_proven())
        );
    }
}

#[test]
fn temporary_retirement_is_allowed_only_with_restoration_before_export() {
    let mut unit = accepted(BORROW_REPAIR).vir().unwrap().as_unit().clone();
    let mut changed = 0;
    for block in &mut unit.runtime.functions[1].blocks {
        let mut rewritten = Vec::new();
        for item in &block.instructions {
            if let VirInstruction::Store {
                pointer,
                permission,
                access,
                value,
            } = item.instruction
            {
                rewritten.push(nera::SpannedVirInstruction {
                    instruction: VirInstruction::ObjectDeinitialize {
                        pointer,
                        permission,
                        access,
                    },
                    source_span: item.source_span,
                });
                rewritten.push(nera::SpannedVirInstruction {
                    instruction: VirInstruction::Write {
                        pointer,
                        permission,
                        access,
                        value,
                    },
                    source_span: item.source_span,
                });
                changed += 1;
            } else {
                rewritten.push(item.clone());
            }
        }
        block.instructions = rewritten;
    }
    assert_eq!(changed, 2);
    unit.rebuild_source_map_from_runtime("restored-export.vir", 10000);
    let unit = unit.into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    assert!(
        verify_program(&resolved, CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [nera::VirRuntimeValue::U64(42)]
    );
}

#[test]
fn live_borrow_prevents_owner_reconstruction_and_ignoring_a_call_argument_is_not_an_escape() {
    let source = "struct Pair { left: u64, right: u64, } fn main() -> u64 { let mut p: Pair;
      p.left = 42; let r = &p.left; p.left = 1; ignore(r); return 42; } fn ignore(p: &u64) { return; }";
    rejected(accepted(source).vir().unwrap().as_unit().clone(), true);
    let source = "fn main() -> u64 { let mut p = 42; let r = &mut p; ignore(r); return 42; } fn ignore(p: &mut u64) { return; }";
    let mut unit = accepted(source).vir().unwrap().as_unit().clone();
    // Retire through the valid mutable authority after formation, before an
    // otherwise empty callee. Only a call-boundary value check catches this.
    let mut changed = false;
    for block in &mut unit.runtime.functions[0].blocks {
        let mut rewritten = Vec::new();
        for item in &block.instructions {
            if let VirInstruction::Call {
                arguments, target, ..
            } = &item.instruction
            {
                let nera::VirType::Pointer { access } = target.signature.parameters[0] else {
                    panic!("pointer parameter");
                };
                rewritten.push(nera::SpannedVirInstruction {
                    instruction: VirInstruction::ObjectDeinitialize {
                        pointer: arguments[0],
                        permission: arguments[1],
                        access,
                    },
                    source_span: item.source_span,
                });
                changed = true;
            }
            rewritten.push(item.clone());
        }
        block.instructions = rewritten;
    }
    assert!(changed);
    unit.rebuild_source_map_from_runtime("call-entry-retirement.vir", 10000);
    let validated = unit.clone().into_validated().unwrap();
    let fault = interpret(validated.resolve().unwrap().runtime()).unwrap_err();
    assert!(matches!(
        fault.kind(),
        nera::VirExecutionErrorKind::UninitializedObjectLeaf { .. }
    ));
    rejected(unit, false);
}

#[test]
fn caller_result_buffer_requires_a_complete_value_even_if_unused() {
    let source = "fn main() -> u64 { let p = make(); return 42; }
      fn make() -> [u64; 3] { let mut p: [u64; 3]; p[0] = 20; p[1] = 22; p[2] = 0; return p; }";
    checked(source);
    let mut unit = accepted(source).vir().unwrap().as_unit().clone();
    let mut removed = 0;
    for block in &mut unit.runtime.functions[1].blocks {
        block.instructions.retain(|item| {
            if matches!(item.instruction, VirInstruction::ObjectTransfer { .. }) {
                removed += 1;
                false
            } else {
                true
            }
        });
    }
    assert!(removed > 0);
    for block in &mut unit.runtime.functions[0].blocks {
        block
            .instructions
            .retain(|item| !matches!(item.instruction, VirInstruction::ObjectTransfer { .. }));
    }
    unit.rebuild_source_map_from_runtime("result-buffer-mutation.vir", 10000);
    rejected(unit, true);

    // A different initialized allocation with an available permission is not
    // the result buffer supplied by this invocation's caller.
    let mut unit = accepted(source).vir().unwrap().as_unit().clone();
    let body = &mut unit.runtime.functions[1].blocks[0];
    let local_permission = body
        .instructions
        .iter()
        .find_map(|item| match item.instruction {
            VirInstruction::LocalStorage {
                permission_result, ..
            } => Some(permission_result.id),
            _ => None,
        })
        .unwrap();
    let nera::VirTerminator::Return { values } = &mut body.terminator.terminator else {
        panic!("single-block return");
    };
    values[0] = local_permission;
    unit.rebuild_source_map_from_runtime("wrong-result-buffer.vir", 10000);
    let validated = unit.clone().into_validated().unwrap();
    let fault = interpret(validated.resolve().unwrap().runtime()).unwrap_err();
    assert!(matches!(
        fault.kind(),
        nera::VirExecutionErrorKind::PermissionMismatch { .. }
    ));
    rejected(unit, false);
}

#[test]
fn missing_or_weakened_indirect_skeleton_cannot_supply_a_complete_value() {
    let source = include_str!("../spec/cases/verify/initialization-interfaces.nera");
    let original = accepted(source).vir().unwrap().as_unit().clone();
    for remove in [true, false] {
        let mut unit = original.clone();
        if remove {
            unit.rebuild_implicit_contracts_from_runtime();
        } else {
            let mut changed = false;
            for clause in unit.specs.clauses_mut() {
                if let nera::VirSpecClauseKind::Resource(summary) = &mut clause.kind {
                    summary.initialization = nera::VirContractInitialization::Unknown;
                    changed = true;
                }
            }
            assert!(changed);
        }
        let unit = unit
            .into_validated()
            .expect("structural validation does not prove value restoration");
        assert!(verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).is_err());
    }
}

#[test]
fn incomplete_returns_escape_and_unimplemented_interfaces_fail_closed() {
    for source in [
        "struct Pair { left: u64, right: u64, } fn make(b: bool) -> Pair { let mut p: Pair; p.left = 42; if b { p.right = 0; } return p; } fn main() -> u64 { let p = make(true); return 42; }",
        "struct Package { owner: Own<u64>, word: u64, } fn bad(p: Package) -> Package { let moved = p.owner; return p; } fn main() -> u64 { return 42; }",
    ] {
        rejected(accepted(source).vir().unwrap().as_unit().clone(), false);
    }
    for source in [
        "fn escape(p: &u64) -> &u64 { let mut value: u64; value = 42; return &value; }",
        "struct Pair { left: u64, right: u64, } fn escape(p: &Pair) -> &Pair { return &Pair { left: 20, right: 22 }; }",
        "struct Package { owner: Own<u64>, } fn unsupported(p: &mut Package) { return; }",
        "enum Package { Empty, Full(Own<u64>), } fn unsupported(p: Package) -> Package { return p; }",
    ] {
        let output = analyze(&SourceFile::from_text("interface-gated.nera", source));
        assert_ne!(
            output.status(),
            FrontendStatus::AcceptedProposal,
            "{source}"
        );
        assert!(output.vir().is_none());
        assert!(!output.issues().is_empty());
    }
}
