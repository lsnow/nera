#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{VirInstruction, VirType};

const SOURCE: &str = include_str!("../spec/cases/verify/raw-address.nera");

#[test]
fn raw_formation_does_not_read_uninitialized_storage_or_create_authority() {
    frontend_checks::checked("raw-address.nera", SOURCE, 42);
    let output = frontend_checks::accepted("raw-address.nera", SOURCE);
    let unit = output.vir().unwrap();
    let mut formations = 0;
    for f in unit.runtime().functions {
        for block in &f.blocks {
            for i in &block.instructions {
                if let VirInstruction::RawAddress { result, .. } = i.instruction {
                    formations += 1;
                    assert!(matches!(result.ty, VirType::Pointer { .. }));
                }
            }
        }
    }
    assert_eq!(formations, 5);
    assert_eq!(
        unit.provenance_catalog()
            .entries()
            .values()
            .filter(|d| matches!(
                d.source,
                nera::VirPointerSource::Derived {
                    step: nera::VirAddressStep::RawAddress { .. },
                    ..
                }
            ))
            .count(),
        formations
    );
}

#[test]
fn raw_aliases_neither_move_the_owner_nor_extend_a_reference_loan() {
    for source in [
        "fn main() -> u64 { let p = alloc<u64>(1); let address = &raw *p; let moved = p; *moved = 42; free(moved); let copy = address; return 42; }",
        "fn main() -> u64 { let mut x = 0; let r = &mut x; let address = &raw mut *r; x = 42; let copy = address; return x; }",
        "fn main() -> u64 { let x = 42; let address: ptr<u64> = &raw x; let copy: ptr<u64> = address; return x; }",
        "fn main() -> u64 { let mut x = 42; let p = &mut x; let c = &mut *p; let value = *c; let address = &raw *p; return value; }",
    ] {
        frontend_checks::checked("raw-lifecycle.nera", source, 42);
    }
}

#[test]
fn dynamic_index_and_slice_endpoints_are_evaluated_once() {
    let source = "fn main() -> u64 {
        let mut calls = 0; let values = [20, 22];
        let start = first(&mut calls);
        let end = limit(&mut calls);
        if start == 0usize {
            if end == 2usize {
                let view = &values[start..end];
                let index = first(&mut calls);
                if index < len(view) {
                    let address = &raw view[index];
                    return calls + 39;
                }
            }
        }
        return 42;
    }
    fn first(c: &mut u64) -> usize { *c = *c + 1; return 0usize; }
    fn limit(c: &mut u64) -> usize { *c = *c + 1; return 2usize; }";
    frontend_checks::checked("raw-evaluation.nera", source, 42);
    let output = frontend_checks::accepted("raw-evaluation.nera", source);
    assert_eq!(
        output.vir().unwrap().runtime().functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.instruction, VirInstruction::Call { .. }))
            .count(),
        3
    );
}

#[test]
fn readonly_recovery_and_authority_free_access_fail_at_explicit_gates() {
    use nera::{SourceFile, analyze};
    for (body, message) in [
        ("let x = 42; let r = &raw mut x;", "not mutable"),
        (
            "let mut x = 42; let s = &x; let r = &raw mut *s;",
            "not writable",
        ),
        (
            "let x = 42; let r: ptr<u64> = &raw x; *r = 7;",
            "writable pointer",
        ),
        ("let x = 42; let r = &raw x; let s = &*r;", "10.1/10.3"),
        (
            "let x = 42; let r = &raw x; let value = *r;",
            "no access permission",
        ),
        (
            "let mut x = 42; let r = &raw mut x; *r = 7;",
            "no access permission",
        ),
        (
            "let values = [20, 22]; let address = &raw values[0..2];",
            "slice",
        ),
    ] {
        let source = format!("fn main() -> u64 {{ {body} return 42; }}");
        let output = analyze(&SourceFile::from_text("raw-gate.nera", &source));
        assert!(output.vir().is_none(), "{source}");
        assert!(
            output
                .issues()
                .iter()
                .any(|issue| issue.diagnostic().message().contains(message)),
            "{source}: {:?}",
            output.issues()
        );
    }
}

#[test]
fn raw_call_and_return_cannot_fill_the_legacy_authority_slot() {
    for source in [
        "fn f() -> ptr<u64> { let mut x = 42; return &raw mut x; }",
        "fn main() -> u64 { let mut x = 42; consume(&raw mut x); return x; } fn consume(p: ptr<u64>) { return; }",
    ] {
        let output = nera::analyze(&nera::SourceFile::from_text("raw-abi.nera", source));
        assert!(output.vir().is_none());
        assert!(
            output
                .issues()
                .iter()
                .any(|i| i.diagnostic().message().contains("7.5.7")),
            "{:?}",
            output.issues()
        );
    }
}

#[test]
fn effectful_raw_index_is_evaluated_once_and_uses_a_closed_body_result() {
    // Body closure proves the scalar return, without changing runtime def-use
    // or evaluating the side-effecting index expression a second time.
    let source = "fn main() -> u64 {
        let mut calls = 0; let values = [20, 22];
        let address = &raw values[next(&mut calls)];
        return calls + 41;
    } fn next(c: &mut u64) -> usize { *c = *c + 1; return 0usize; }";
    let output = frontend_checks::accepted("raw-effectful-index.nera", source);
    let resolved = output.vir().unwrap().resolve().unwrap();
    assert_eq!(
        nera::interpret(resolved.runtime()).unwrap().values(),
        [nera::VirRuntimeValue::U64(42)]
    );
    assert_eq!(
        resolved.runtime().functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.instruction, VirInstruction::Call { .. }))
            .count(),
        1
    );
    assert!(
        nera::verify_program(&resolved, nera::CfgAnalysisConfig::default())
            .unwrap()
            .is_memory_checked_core0()
    );
}

#[test]
fn dead_storage_and_suspended_parent_cannot_form_a_new_raw_address() {
    use nera::{CfgAnalysisConfig, interpret, verify_program};
    for source in [
        "fn main() -> u64 { let p = alloc<u64>(1); free(p); let address = &raw *p; return 42; }",
        "fn main() -> u64 { let mut x = 42; let p = &mut x; let c = &mut *p; let address = &raw *p; return *c; }",
    ] {
        let output = frontend_checks::accepted("raw-lifetime.nera", source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let verification = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(!verification.is_memory_checked_core0());
        assert!(
            verification
                .functions()
                .values()
                .flat_map(|f| f.cfg().obligations())
                .any(|o| {
                    matches!(
                        o.obligation().kind(),
                        nera::ResourceObligationKind::ObjectAllocationLive { .. }
                            | nera::ResourceObligationKind::LoanCompatible { .. }
                    ) && o.obligation().status() == nera::ObligationStatus::Refuted
                }),
            "{:?}",
            verification.diagnostics()
        );
        let fault = interpret(resolved.runtime()).unwrap_err();
        assert!(
            matches!(
                fault.kind(),
                nera::VirExecutionErrorKind::UseAfterFree { .. }
                    | nera::VirExecutionErrorKind::PermissionAlreadyConsumed(_)
                    | nera::VirExecutionErrorKind::LoanAccessConflict { .. }
            ),
            "{fault:?}"
        );
    }
}

#[test]
fn raw_schema_mutations_cannot_replace_types_or_permissions() {
    use nera::{VirMemoryTypeKind, VirMutability, VirPointerKind, VirValidationErrorKind};
    let output = frontend_checks::accepted("raw-schema.nera", SOURCE);
    let original = output.vir().unwrap().as_unit();
    for bad_layout in [false, true] {
        let mut unit = original.clone();
        let operation = unit.runtime.functions[0].blocks[0]
            .instructions
            .iter_mut()
            .find(|i| matches!(i.instruction, VirInstruction::RawAddress { .. }))
            .unwrap();
        let VirInstruction::RawAddress {
            raw_type, result, ..
        } = &mut operation.instruction
        else {
            unreachable!()
        };
        if bad_layout {
            raw_type.layout = nera::VirLayoutId::new(u32::MAX);
        } else {
            let VirType::Pointer { access } = result.ty else {
                unreachable!()
            };
            *raw_type = access;
        }
        assert!(matches!(
            unit.into_validated().unwrap_err().kind(),
            VirValidationErrorKind::InvalidMemoryAccess(_)
        ));
    }

    // A raw-mut result cannot be proposed using a shared reference's authority.
    let mut unit = original.clone();
    let raw_mut = unit
        .memory
        .types
        .iter()
        .find(|t| {
            matches!(
                t.kind,
                VirMemoryTypeKind::Pointer {
                    kind: VirPointerKind::Raw,
                    mutability: VirMutability::Mutable,
                    ..
                }
            )
        })
        .and_then(|t| unit.memory.access(t.id))
        .unwrap();
    let operation = unit.runtime.functions[0].blocks[0]
        .instructions
        .iter_mut()
        .rev()
        .find(|i| matches!(i.instruction, VirInstruction::RawAddress { .. }))
        .unwrap();
    let VirInstruction::RawAddress { raw_type, .. } = &mut operation.instruction else {
        unreachable!()
    };
    *raw_type = raw_mut;
    let validated = unit.into_validated().unwrap();
    let resolved = validated.resolve().unwrap();
    let verification = nera::verify_program(&resolved, nera::CfgAnalysisConfig::default()).unwrap();
    assert!(!verification.is_memory_checked_core0());
    assert!(
        verification
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| {
                matches!(
                    o.obligation().kind(),
                    nera::ResourceObligationKind::PermissionWritable { .. }
                ) && o.obligation().status() == nera::ObligationStatus::Refuted
            })
    );
    assert!(matches!(
        nera::interpret(resolved.runtime()).unwrap_err().kind(),
        nera::VirExecutionErrorKind::LoanAccessConflict { .. }
    ));
}
