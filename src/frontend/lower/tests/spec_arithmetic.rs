use super::*;
use crate::{HirSpecRoot, ObligationStatus};

fn fixture() -> HirProgramTables {
    let base = accepted_program("fn main() -> u64 { return 2; }");
    let mut t = program_tables(&base);
    let f = base.entry_function();
    let span = f.span;
    let u64_ty = f.signature.return_type;
    let bool_ty = base
        .types()
        .iter()
        .find(|t| t.kind == HirTypeKind::Bool)
        .unwrap()
        .id;
    let id = HirSpecTermId::new;
    let clause = HirSpecClauseId::new(0);
    let location = HirSpecLocation::FunctionResult { function: f.id };
    for (i, (ty, kind)) in [
        (
            u64_ty,
            HirSpecTermKind::Snapshot(HirSpecSnapshot::Result { function: f.id }),
        ),
        (u64_ty, HirSpecTermKind::U64(8)),
        (u64_ty, HirSpecTermKind::U64(0)),
        (u64_ty, HirSpecTermKind::U64(48)),
        (
            u64_ty,
            HirSpecTermKind::CheckedScale {
                operand: id(0),
                stride: 8,
            },
        ),
        (
            u64_ty,
            HirSpecTermKind::CheckedAdd {
                left: id(4),
                right: id(1),
            },
        ),
        (
            u64_ty,
            HirSpecTermKind::CheckedSub {
                left: id(5),
                right: id(4),
            },
        ),
        (
            bool_ty,
            HirSpecTermKind::Equal {
                left: id(6),
                right: id(1),
            },
        ),
        (
            bool_ty,
            HirSpecTermKind::RangeContains {
                outer_start: id(2),
                outer_end: id(3),
                inner_start: id(4),
                inner_end: id(5),
            },
        ),
        (
            bool_ty,
            HirSpecTermKind::RangeDisjoint {
                left_start: id(2),
                left_end: id(4),
                right_start: id(5),
                right_end: id(3),
            },
        ),
        (bool_ty, HirSpecTermKind::And(vec![id(7), id(8), id(9)])),
    ]
    .into_iter()
    .enumerate()
    {
        t.specs.terms.push(HirSpecTerm {
            id: id(i as u32),
            clause,
            ty,
            kind,
            span,
        });
    }
    t.specs.clauses.push(HirSpecClause {
        id: clause,
        owner: HirSpecClauseOwner::Prove(HirSpecProveId::new(0)),
        location,
        root: HirSpecRoot::Pure(id(10)),
        span,
    });
    t.specs.proves.push(HirSpecProve {
        id: HirSpecProveId::new(0),
        function: f.id,
        location,
        clause,
        span,
    });
    t
}

#[test]
fn checked_numeric_hir_lowers_with_types_origins_and_no_runtime_changes() {
    let t = fixture();
    let mut plain = t.clone();
    plain.specs = HirSpecEnvironment::empty();
    let plain = lower_test(&hir_from_tables(plain).unwrap()).unwrap();
    let hir = hir_from_tables(t).unwrap();
    let unit = lower_test(&hir).unwrap();
    assert_eq!(unit.runtime().stable_dump(), plain.runtime().stable_dump());
    for (h, v) in hir.specs().terms.iter().zip(unit.as_unit().specs.terms()) {
        assert_eq!(
            unit.as_unit()
                .source_map
                .source_span_for_origin(v.origin)
                .unwrap()
                .span,
            h.span
        );
    }
    let resolved = unit.resolve().unwrap();
    let report = verify_program(&resolved, crate::CfgAnalysisConfig::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    assert_eq!(
        report.functions()[&crate::VirFunctionId::new(0)].proofs()[0].status(),
        ObligationStatus::Proven
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [crate::VirRuntimeValue::U64(2)]
    );
}

#[test]
fn checked_numeric_hir_rejects_type_forward_reference_and_foreign_clause_mutations() {
    for mutation in 0..5 {
        let mut t = fixture();
        match mutation {
            0 => t.specs.terms[4].ty = t.specs.terms[7].ty,
            1 => {
                t.specs.terms[4].kind = HirSpecTermKind::CheckedScale {
                    operand: HirSpecTermId::new(99),
                    stride: 8,
                }
            }
            2 => {
                t.specs.terms[5].kind = HirSpecTermKind::CheckedAdd {
                    left: HirSpecTermId::new(5),
                    right: HirSpecTermId::new(1),
                }
            }
            3 => {
                t.specs.terms[8].kind = HirSpecTermKind::RangeContains {
                    outer_start: HirSpecTermId::new(2),
                    outer_end: HirSpecTermId::new(3),
                    inner_start: HirSpecTermId::new(7),
                    inner_end: HirSpecTermId::new(5),
                }
            }
            _ => t.specs.terms[4].clause = HirSpecClauseId::new(99),
        }
        assert!(hir_from_tables(t).is_err(), "{mutation}");
    }
}

#[test]
fn numeric_terms_preserve_existential_scope_checks_in_both_arenas() {
    let mut t = super::spec_assertions::fixture();
    let mut arithmetic = t.specs.terms[3].clone();
    arithmetic.id = HirSpecTermId::new(6);
    arithmetic.kind = HirSpecTermKind::CheckedAdd {
        left: HirSpecTermId::new(3),
        right: HirSpecTermId::new(2),
    };
    let mut comparison = t.specs.terms[5].clone();
    comparison.id = HirSpecTermId::new(7);
    comparison.kind = HirSpecTermKind::Equal {
        left: arithmetic.id,
        right: HirSpecTermId::new(2),
    };
    t.specs.terms.extend([arithmetic, comparison]);
    let unit = lower_test(&hir_from_tables(t.clone()).unwrap()).unwrap();
    t.specs.clauses[0].root = HirSpecRoot::Pure(HirSpecTermId::new(7));
    assert!(hir_from_tables(t).is_err());
    let mut unit = unit.as_unit().clone();
    let clause = unit.specs.assertions()[0].clause;
    unit.specs.clauses_mut()[clause.get() as usize].kind = VirSpecClauseKind::Logic {
        root: crate::VirSpecTermId::new(7),
    };
    assert!(unit.validate().is_err());
}

#[test]
fn checked_numeric_schema_does_not_expand_the_trust_policy() {
    let mut t = fixture();
    t.specs.terms[0].kind = HirSpecTermKind::U64(0);
    let unit = lower_test(&hir_from_tables(t.clone()).unwrap()).unwrap();
    let prove = t.specs.proves.remove(0);
    let location = HirSpecLocation::FunctionEntry {
        function: prove.function,
    };
    t.specs.clauses[0].location = location;
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
    let mut unit = unit.as_unit().clone();
    let prove = unit.specs.proves_mut().remove(0);
    let c = &mut unit.specs.clauses_mut()[prove.clause.get() as usize];
    c.location = crate::VirSpecLocation::FunctionEntry {
        function: prove.function,
    };
    c.owner = VirSpecClauseOwner::TrustEntry(crate::VirTrustEntryId::new(0));
    unit.specs.trust_entries_mut().push(crate::VirTrustEntry {
        id: crate::VirTrustEntryId::new(0),
        scope: crate::VirTrustScope::FunctionEntry {
            function: prove.function,
        },
        policy: crate::VirTrustPolicyKind::EntryPointAssumption,
        clause: prove.clause,
        origin: prove.origin,
    });
    assert!(unit.validate().is_err());
}
