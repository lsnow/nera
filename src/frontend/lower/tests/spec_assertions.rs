use super::*;
use crate::{
    HirSpecAssertion, HirSpecAssertionId as AId, HirSpecBinder, HirSpecBinderId as BId,
    HirSpecBinderOwner, HirSpecRoot, SpecAccess, SpecAssertionKind as A, SpecMemoryClaim,
    VirSpecAssertionId as VAId, VirSpecTermId as VTId,
};

pub(super) fn fixture() -> HirProgramTables {
    let base = accepted_program(
        "fn main() -> u64 { let mut x = 42; return inspect(&mut x); } fn inspect(p: &mut u64) -> u64 { return *p; } fn discard(owner: Own<u64>) { return; }",
    );
    let mut tables = program_tables(&base);
    let function = base
        .functions()
        .iter()
        .find(|f| f.name == "inspect")
        .unwrap();
    let span = function.span;
    let clause = HirSpecClauseId::new(0);
    let ty = base
        .types()
        .iter()
        .find(|t| t.kind == HirTypeKind::Integer(HirIntegerType::U64))
        .unwrap()
        .id;
    let bool_ty = base
        .types()
        .iter()
        .find(|t| t.kind == HirTypeKind::Bool)
        .unwrap()
        .id;
    let location = HirSpecLocation::FunctionEntry {
        function: function.id,
    };
    let snapshot = HirSpecSnapshot::Local {
        function: function.id,
        local: function.body().unwrap().parameters[0],
    };
    let term = HirSpecTermId::new;
    tables.specs.binders.push(HirSpecBinder {
        id: BId::new(0),
        owner: HirSpecBinderOwner::Clause(clause),
        name: "stored".into(),
        ty,
        span,
    });
    for (i, (ty, kind)) in [
        (ty, HirSpecTermKind::U64(0)),
        (ty, HirSpecTermKind::U64(8)),
        (ty, HirSpecTermKind::U64(42)),
        (ty, HirSpecTermKind::Binder(BId::new(0))),
        (bool_ty, HirSpecTermKind::Bool(true)),
        (
            bool_ty,
            HirSpecTermKind::Equal {
                left: term(3),
                right: term(2),
            },
        ),
    ]
    .into_iter()
    .enumerate()
    {
        tables.specs.terms.push(HirSpecTerm {
            id: term(i as u32),
            clause,
            ty,
            kind,
            span,
        });
    }
    let memory = SpecMemoryClaim {
        pointer: snapshot,
        authority: snapshot,
        start_bytes: term(0),
        end_bytes: term(1),
        layout: ty,
        access: SpecAccess::Write,
    };
    for (i, kind) in [
        A::PointsTo {
            memory: memory.clone(),
            value: Some(term(3)),
        },
        A::Permission(memory),
        A::Pure(term(5)),
        A::Separation(vec![AId::new(0), AId::new(1), AId::new(2), AId::new(0)]),
        A::Exists {
            binder: BId::new(0),
            body: AId::new(3),
            witness: Some(term(2)),
        },
    ]
    .into_iter()
    .enumerate()
    {
        tables.specs.assertions.push(HirSpecAssertion {
            id: AId::new(i as u32),
            clause,
            kind,
            span,
        });
    }
    tables.specs.clauses.push(HirSpecClause {
        id: clause,
        owner: HirSpecClauseOwner::Prove(HirSpecProveId::new(0)),
        location,
        root: HirSpecRoot::Assertion(AId::new(4)),
        span,
    });
    tables.specs.proves.push(HirSpecProve {
        id: HirSpecProveId::new(0),
        function: function.id,
        location,
        clause,
        span,
    });
    tables
}

#[test]
fn resource_schema_lowering_preserves_occurrences_origins_and_runtime() {
    let tables = fixture();
    let mut plain = tables.clone();
    plain.specs = HirSpecEnvironment::empty();
    let plain = lower_test(&hir_from_tables(plain).unwrap()).unwrap();
    let hir = hir_from_tables(tables).unwrap();
    let unit = lower_test(&hir).unwrap();
    assert_eq!(hir.version(), crate::HirVersion::V23);
    assert_eq!(unit.as_unit().version, crate::VirUnitVersion::V28);
    assert_eq!(unit.runtime().stable_dump(), plain.runtime().stable_dump());
    assert_eq!(unit.as_unit().memory, plain.as_unit().memory);
    let specs = &unit.as_unit().specs;
    assert_eq!(specs.assertions().len(), 5);
    assert_eq!(
        specs.assertions()[3].kind,
        A::Separation(vec![VAId::new(0), VAId::new(1), VAId::new(2), VAId::new(0)])
    );
    let clause = specs.assertions()[0].clause;
    assert!(clause.get() > 0, "type-inferred clauses require rebasing");
    assert!(specs.assertions().iter().all(|a| a.clause == clause));
    for (h, v) in hir.specs().assertions.iter().zip(specs.assertions()) {
        assert_eq!(
            unit.as_unit()
                .source_map
                .source_span_for_origin(v.origin)
                .unwrap()
                .span,
            h.span
        );
    }
    assert!(unit.stable_dump().contains("assertion assertion3"));
    let resolved = unit.resolve().unwrap();
    let verification = verify_program(&resolved, crate::CfgAnalysisConfig::default()).unwrap();
    assert!(!verification.is_memory_checked_core0());
    assert!(verification.diagnostics().iter().any(|d| {
        d.message()
            .contains("cannot prove specification obligation")
    }));
    assert!(
        verification
            .functions()
            .values()
            .flat_map(|f| f.proofs())
            .all(|p| p.status() == crate::ObligationStatus::Unknown)
    );
    assert!(unit.as_unit().specs.trust_entries().is_empty());
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [crate::VirRuntimeValue::U64(42)]
    );
    let machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(resolved.runtime())
        .unwrap();
    let plain_resolved = plain.resolve().unwrap();
    let plain_machine = X86_64_UNKNOWN_LINUX_GNU
        .codegen_program(plain_resolved.runtime())
        .unwrap();
    assert_eq!(
        X86_64_UNKNOWN_LINUX_GNU.emit_assembly(&machine).unwrap(),
        X86_64_UNKNOWN_LINUX_GNU
            .emit_assembly(&plain_machine)
            .unwrap()
    );
}

#[test]
fn hir_resource_schema_rejects_cross_table_type_scope_and_snapshot_mutations() {
    for mutation in 0..15 {
        let mut t = fixture();
        match mutation {
            0 => t.specs.assertions[0].id = AId::new(9),
            1 => t.specs.assertions[0].clause = HirSpecClauseId::new(99),
            2 => t.specs.assertions[3].kind = A::Separation(vec![AId::new(3), AId::new(0)]),
            3 => t.specs.assertions[3].kind = A::Separation(vec![AId::new(99), AId::new(0)]),
            4 => t.specs.assertions[2].kind = A::Pure(HirSpecTermId::new(0)),
            5 => t.specs.assertions[2].kind = A::Pure(HirSpecTermId::new(99)),
            6 => t.specs.clauses[0].root = HirSpecRoot::Pure(HirSpecTermId::new(0)),
            7 => {
                t.specs.assertions[4].kind = A::Exists {
                    binder: BId::new(0),
                    body: AId::new(3),
                    witness: Some(HirSpecTermId::new(4)),
                }
            }
            8 => {
                t.specs.assertions[4].kind = A::Exists {
                    binder: BId::new(0),
                    body: AId::new(3),
                    witness: Some(HirSpecTermId::new(3)),
                }
            }
            9 => t.specs.clauses[0].root = HirSpecRoot::Assertion(AId::new(3)),
            10 => t.specs.binders[0].owner = HirSpecBinderOwner::Clause(HirSpecClauseId::new(99)),
            11 => t.specs.assertions[0].span = ByteSpan::new(0, 1).unwrap(),
            12..=14 => {
                if let A::PointsTo { memory, value } = &mut t.specs.assertions[0].kind {
                    match mutation {
                        12 => {
                            memory.authority = HirSpecSnapshot::Local {
                                function: HirFunctionId::new(2),
                                local: crate::HirLocalId::new(0),
                            }
                        }
                        13 => memory.end_bytes = HirSpecTermId::new(4),
                        _ => *value = Some(HirSpecTermId::new(4)),
                    }
                }
            }
            _ => unreachable!(),
        }
        assert!(hir_from_tables(t).is_err(), "mutation {mutation}");
    }
}

#[test]
fn vir_resource_schema_independently_rejects_mutations() {
    let unit = lower_test(&hir_from_tables(fixture()).unwrap()).unwrap();
    for mutation in 0..16 {
        let mut t = unit.as_unit().clone();
        let clause = t.specs.assertions()[0].clause;
        match mutation {
            0 => t.specs.assertions_mut()[0].id = VAId::new(9),
            1 => t.specs.assertions_mut()[0].clause = crate::VirSpecClauseId::new(999),
            2 => t.specs.assertions_mut()[3].kind = A::Separation(vec![VAId::new(3), VAId::new(0)]),
            3 => {
                t.specs.assertions_mut()[3].kind = A::Separation(vec![VAId::new(99), VAId::new(0)])
            }
            4 => t.specs.assertions_mut()[2].kind = A::Pure(VTId::new(0)),
            5 => t.specs.assertions_mut()[2].kind = A::Pure(VTId::new(99)),
            6 => {
                t.specs.clauses_mut()[clause.get() as usize].kind =
                    VirSpecClauseKind::Logic { root: VTId::new(0) }
            }
            7 => {
                t.specs.assertions_mut()[4].kind = A::Exists {
                    binder: crate::VirSpecBinderId::new(0),
                    body: VAId::new(3),
                    witness: Some(VTId::new(4)),
                }
            }
            8 => {
                t.specs.assertions_mut()[4].kind = A::Exists {
                    binder: crate::VirSpecBinderId::new(0),
                    body: VAId::new(3),
                    witness: Some(VTId::new(3)),
                }
            }
            9 => {
                t.specs.clauses_mut()[clause.get() as usize].kind =
                    VirSpecClauseKind::Assertion { root: VAId::new(3) }
            }
            10 => {
                t.specs.binders_mut()[0].owner =
                    crate::VirSpecBinderOwner::Clause(crate::VirSpecClauseId::new(999))
            }
            11 => t.specs.assertions_mut()[0].origin = crate::VirOriginId::new(999),
            12..=15 => {
                if let A::PointsTo { memory, value } = &mut t.specs.assertions_mut()[0].kind {
                    match mutation {
                        12 => {
                            memory.authority = VirSpecSnapshot::Parameter {
                                function: crate::VirFunctionId::new(2),
                                slot: 0,
                            }
                        }
                        13 => memory.end_bytes = VTId::new(4),
                        14 => *value = Some(VTId::new(4)),
                        _ => memory.layout.layout = crate::VirLayoutId::new(999),
                    }
                }
            }
            _ => unreachable!(),
        }
        assert!(t.validate().is_err(), "mutation {mutation}");
    }
}

#[test]
fn resource_contracts_are_representable_but_trust_is_not_forged() {
    let mut t = fixture();
    let function = t.specs.proves[0].function;
    let contract = t.functions[function.index()].contract;
    t.specs.clauses[0].owner = HirSpecClauseOwner::Contract {
        contract,
        position: HirSpecContractPosition::Requires,
    };
    t.contracts[contract.index()]
        .clauses
        .push(HirSpecClauseId::new(0));
    t.specs.proves.clear();
    // 8.2 opens typed resource clauses; representation is not a proof that
    // any caller satisfies the requirement.
    assert!(hir_from_tables(t).is_ok());
    let unit = lower_test(&hir_from_tables(fixture()).unwrap()).unwrap();
    let mut t = unit.as_unit().clone();
    let clause = t.specs.assertions()[0].clause;
    let function = t.specs.proves()[0].function;
    let contract = t
        .runtime
        .functions
        .iter()
        .find(|f| f.id == function)
        .unwrap()
        .contract;
    t.specs.clauses_mut()[clause.get() as usize].owner = VirSpecClauseOwner::Contract {
        contract,
        position: crate::VirContractPosition::Requires,
    };
    t.specs.contract_mut(contract).unwrap().clauses.push(clause);
    t.specs.proves_mut().clear();
    assert!(t.validate().is_ok());

    let mut t = fixture();
    let prove = t.specs.proves.remove(0);
    t.specs.clauses[0].owner = HirSpecClauseOwner::TrustEntry(crate::HirTrustEntryId::new(0));
    t.specs.trust_entries.push(crate::HirTrustEntry {
        id: crate::HirTrustEntryId::new(0),
        scope: crate::HirTrustScope::FunctionEntry {
            function: prove.function,
        },
        policy: crate::HirTrustPolicyKind::EntryPointAssumption,
        clause: prove.clause,
        span: prove.span,
    });
    assert!(hir_from_tables(t).is_err());
    let mut t = unit.as_unit().clone();
    let prove = t.specs.proves_mut().remove(0);
    t.specs.clauses_mut()[prove.clause.get() as usize].owner =
        VirSpecClauseOwner::TrustEntry(crate::VirTrustEntryId::new(0));
    t.specs.trust_entries_mut().push(crate::VirTrustEntry {
        id: crate::VirTrustEntryId::new(0),
        scope: crate::VirTrustScope::FunctionEntry {
            function: prove.function,
        },
        policy: crate::VirTrustPolicyKind::EntryPointAssumption,
        clause: prove.clause,
        origin: prove.origin,
    });
    assert!(t.validate().is_err());
}

#[test]
fn existential_schema_checks_duplicate_binders_depth_and_optional_witness() {
    let mut no_witness = fixture();
    if let A::Exists { witness, .. } = &mut no_witness.specs.assertions[4].kind {
        *witness = None;
    }
    lower_test(&hir_from_tables(no_witness).unwrap()).unwrap();
    let unit = lower_test(&hir_from_tables(fixture()).unwrap()).unwrap();
    for duplicate in [true, false] {
        let mut hir = fixture();
        let mut vir = unit.as_unit().clone();
        let clause = vir.specs.assertions()[0].clause;
        for _ in 0..if duplicate { 1 } else { 256 } {
            let index = hir.specs.assertions.len() as u32;
            let mut next = hir.specs.assertions[4].clone();
            next.id = AId::new(index);
            next.kind = if duplicate {
                A::Exists {
                    binder: BId::new(0),
                    body: AId::new(index - 1),
                    witness: Some(HirSpecTermId::new(2)),
                }
            } else {
                A::Separation(vec![AId::new(index - 1); 2])
            };
            hir.specs.assertions.push(next);
            hir.specs.clauses[0].root = HirSpecRoot::Assertion(AId::new(index));
            let mut next = vir.specs.assertions()[4].clone();
            next.id = VAId::new(index);
            next.kind = if duplicate {
                A::Exists {
                    binder: crate::VirSpecBinderId::new(0),
                    body: VAId::new(index - 1),
                    witness: Some(VTId::new(2)),
                }
            } else {
                A::Separation(vec![VAId::new(index - 1); 2])
            };
            vir.specs.assertions_mut().push(next);
            vir.specs.clauses_mut()[clause.get() as usize].kind = VirSpecClauseKind::Assertion {
                root: VAId::new(index),
            };
        }
        assert!(hir_from_tables(hir).is_err());
        assert!(vir.validate().is_err());
    }
}

#[test]
fn resource_schema_rejects_valid_terms_owned_by_another_clause() {
    let mut t = fixture();
    let mut word = t.specs.terms[0].clone();
    word.id = HirSpecTermId::new(6);
    word.clause = HirSpecClauseId::new(1);
    let mut truth = t.specs.terms[4].clone();
    truth.id = HirSpecTermId::new(7);
    truth.clause = word.clause;
    let mut prove = t.specs.proves[0].clone();
    prove.id = HirSpecProveId::new(1);
    prove.clause = word.clause;
    let mut clause = t.specs.clauses[0].clone();
    clause.id = word.clause;
    clause.owner = HirSpecClauseOwner::Prove(prove.id);
    clause.root = HirSpecRoot::Pure(truth.id);
    t.specs.terms.extend([word, truth]);
    t.specs.proves.push(prove);
    t.specs.clauses.push(clause);
    let unit = lower_test(&hir_from_tables(t.clone()).unwrap()).unwrap();
    if let A::PointsTo { memory, .. } = &mut t.specs.assertions[0].kind {
        memory.start_bytes = HirSpecTermId::new(6);
    }
    assert!(hir_from_tables(t).is_err());
    let mut vir = unit.as_unit().clone();
    if let A::PointsTo { memory, .. } = &mut vir.specs.assertions_mut()[0].kind {
        memory.start_bytes = VTId::new(6);
    }
    assert!(vir.validate().is_err());
}
