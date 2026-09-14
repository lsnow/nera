use super::*;
use crate::{VirContractPosition, VirLocation, VirSpecTermId};

fn fixture() -> HirProgramTables {
    let base = accepted_program(
        "fn main()->u64 {let p=0; let x=f(&p,20); return x+f(&p,22);} fn f(p:&u64,value:u64)->u64{return value;}",
    );
    let mut t = program_tables(&base);
    let f = &t.functions[1];
    let function = f.id;
    let span = f.span;
    let u64_ty = f.signature.return_type;
    let bool_ty = t
        .types
        .iter()
        .find(|t| t.kind == HirTypeKind::Bool)
        .unwrap()
        .id;
    let clause = HirSpecClauseId::new(0);
    for (index, ty, kind) in [
        (
            0,
            u64_ty,
            HirSpecTermKind::Snapshot(HirSpecSnapshot::EntryParameter {
                function,
                parameter: 1,
            }),
        ),
        (
            1,
            u64_ty,
            HirSpecTermKind::Snapshot(HirSpecSnapshot::Result { function }),
        ),
        (
            2,
            bool_ty,
            HirSpecTermKind::Equal {
                left: HirSpecTermId::new(0),
                right: HirSpecTermId::new(1),
            },
        ),
    ] {
        t.specs.terms.push(HirSpecTerm {
            id: HirSpecTermId::new(index),
            clause,
            ty,
            kind,
            span,
        });
    }
    t.specs.clauses.push(HirSpecClause {
        id: clause,
        owner: HirSpecClauseOwner::Contract {
            contract: f.contract,
            position: HirSpecContractPosition::Ensures,
        },
        location: HirSpecLocation::FunctionResult { function },
        root: HirSpecTermId::new(2).into(),
        span,
    });
    t.contracts[f.contract.index()].clauses.push(clause);
    t
}

#[test]
fn entry_snapshot_lowering_respects_logical_to_physical_abi_and_erasure() {
    let tables = fixture();
    let mut erased = tables.clone();
    erased.specs = Default::default();
    erased.contracts[1].clauses.clear();
    let erased = lower_test(&hir_from_tables(erased).unwrap()).unwrap();
    let unit = lower_test(&hir_from_tables(tables).unwrap()).unwrap();
    assert!(matches!(
        unit.as_unit().specs.terms()[0].kind,
        VirSpecTermKind::Snapshot(VirSpecSnapshot::EntryParameter { slot: 2, .. })
    ));
    assert_eq!(unit.runtime().stable_dump(), erased.runtime().stable_dump());
    let resolved = unit.resolve().unwrap();
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        &[crate::VirRuntimeValue::U64(42)]
    );
    assert!(
        verify_program(&resolved, Default::default())
            .unwrap()
            .is_memory_checked_core0()
    );
    X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .unwrap();
    assert!(unit.as_unit().specs.trust_entries().is_empty());

    let mut bindings = vec![];
    for block in &resolved.runtime().functions[0].blocks {
        for (ordinal, instruction) in block.instructions.iter().enumerate() {
            if let VirInstruction::Call {
                arguments, results, ..
            } = &instruction.instruction
            {
                let location = VirLocation::Instruction {
                    function: crate::VirFunctionId::new(0),
                    block: block.id,
                    ordinal: ordinal as u64,
                };
                let binding = resolved.contract_call_binding(location).unwrap();
                assert_eq!(binding.location(), location);
                assert_eq!(
                    binding.snapshot(VirSpecTermId::new(0)),
                    Some((VirContractPosition::Requires, arguments[2]))
                );
                assert_eq!(
                    binding.snapshot(VirSpecTermId::new(1)),
                    Some((VirContractPosition::Ensures, results[0].id))
                );
                assert_eq!(binding.snapshot(VirSpecTermId::new(2)), None);
                assert_eq!(binding.snapshot(VirSpecTermId::new(99)), None);
                bindings.push((location, results[0].id));
            }
        }
    }
    assert_eq!(bindings.len(), 2);
    assert_ne!(bindings[0], bindings[1]);
    assert!(
        resolved
            .contract_call_binding(VirLocation::FunctionEntry {
                function: crate::VirFunctionId::new(0)
            })
            .is_none()
    );
}

#[test]
fn entry_snapshot_hir_rejects_wrong_function_parameter_type_and_epoch() {
    for snapshot in [
        HirSpecSnapshot::EntryParameter {
            function: HirFunctionId::new(0),
            parameter: 1,
        },
        HirSpecSnapshot::EntryParameter {
            function: HirFunctionId::new(1),
            parameter: 99,
        },
        HirSpecSnapshot::EntryParameter {
            function: HirFunctionId::new(1),
            parameter: 0,
        },
        HirSpecSnapshot::Local {
            function: HirFunctionId::new(1),
            local: crate::HirLocalId::new(1),
        },
    ] {
        let mut t = fixture();
        t.specs.terms[0].kind = HirSpecTermKind::Snapshot(snapshot);
        assert!(hir_from_tables(t).is_err());
    }
    let mut t = fixture();
    t.specs.clauses[0].owner = HirSpecClauseOwner::Contract {
        contract: t.functions[1].contract,
        position: HirSpecContractPosition::Requires,
    };
    t.specs.clauses[0].location = HirSpecLocation::FunctionEntry {
        function: HirFunctionId::new(1),
    };
    assert!(hir_from_tables(t).is_err());
}

#[test]
fn entry_snapshot_vir_rejects_physical_permission_foreign_owner_and_missing_slot() {
    let unit = lower_test(&hir_from_tables(fixture()).unwrap()).unwrap();
    for snapshot in [
        VirSpecSnapshot::EntryParameter {
            function: crate::VirFunctionId::new(1),
            slot: 1,
        },
        VirSpecSnapshot::EntryParameter {
            function: crate::VirFunctionId::new(1),
            slot: 99,
        },
        VirSpecSnapshot::EntryParameter {
            function: crate::VirFunctionId::new(0),
            slot: 2,
        },
        VirSpecSnapshot::Result {
            function: crate::VirFunctionId::new(1),
            slot: 1,
        },
        VirSpecSnapshot::Parameter {
            function: crate::VirFunctionId::new(1),
            slot: 2,
        },
    ] {
        let mut raw = unit.as_unit().clone();
        raw.specs.terms_mut()[0].kind = VirSpecTermKind::Snapshot(snapshot);
        assert!(raw.into_validated().is_err());
    }
}
