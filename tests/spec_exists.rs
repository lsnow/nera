use nera::*;
#[path = "support/spec_exists.rs"]
mod fixture;
#[path = "support/spec_memory.rs"]
#[allow(dead_code)]
mod spec_memory;
use ObligationStatus::{Proven as P, Unknown as U};
use SpecAssertionKind as A;
use VirSpecTermKind as T;
use fixture::{binder, node, range, term};

fn statuses(unit: &VirUnit) -> Vec<ObligationStatus> {
    let valid = unit.clone().into_validated().unwrap();
    let report = verify_program(&valid.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    report
        .functions()
        .values()
        .flat_map(|f| f.proofs().iter().map(SpecProof::status))
        .collect()
}

#[test]
fn range_witnesses_check_bounds_current_liveness_and_do_not_change_runtime() {
    let mut unit = fixture::checked_unit();
    range(&mut unit, 2, 16);
    range(&mut unit, 2, 24);
    range(&mut unit, 2, 7);
    range(&mut unit, 10, 8); // freed allocation
    range(&mut unit, 10, 0); // empty still requires live authority
    range(&mut unit, 2, 8); // no successful-match cache from another clause
    assert_eq!(statuses(&unit), [P, P, U, U, U, U, P]);
    let valid = unit.into_validated().unwrap();
    let plain = spec_memory::unit().into_validated().unwrap();
    assert_eq!(valid.runtime().stable_dump(), plain.runtime().stable_dump());
    assert_eq!(
        interpret(valid.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(7)]
    );
    assert!(valid.as_unit().specs.trust_entries().is_empty());
}

#[test]
fn absent_free_or_undefined_witness_is_unknown_even_if_body_ignores_it() {
    for mutation in 0..5 {
        let mut unit = fixture::checked_unit();
        let clause = VirSpecClauseId::new(0);
        let truth = term(&mut unit, clause, VirSpecType::Bool, T::Bool(true));
        unit.specs.assertions_mut()[0].kind = A::Pure(truth);
        let witness = match mutation {
            0 => None,
            1 => {
                // free ghost symbol is not a supplied value
                let b = binder(&mut unit, clause, VirSpecType::U64);
                Some(term(&mut unit, clause, VirSpecType::U64, T::Binder(b)))
            }
            2 => {
                let max = term(&mut unit, clause, VirSpecType::U64, T::U64(u64::MAX));
                Some(term(
                    &mut unit,
                    clause,
                    VirSpecType::U64,
                    T::CheckedAdd {
                        left: max,
                        right: VirSpecTermId::new(1),
                    },
                ))
            }
            3 => Some(term(
                &mut unit,
                clause,
                VirSpecType::U64,
                T::CheckedSub {
                    left: VirSpecTermId::new(0),
                    right: VirSpecTermId::new(1),
                },
            )),
            _ => Some(term(
                &mut unit,
                clause,
                VirSpecType::U64,
                T::CheckedScale {
                    operand: VirSpecTermId::new(2),
                    stride: u64::MAX,
                },
            )),
        };
        if let A::Exists { witness: w, .. } = &mut unit.specs.assertions_mut()[1].kind {
            *w = witness;
        }
        assert_eq!(statuses(&unit), [U], "mutation {mutation}");
    }
}

#[test]
fn failed_candidate_is_not_a_counterexample_to_an_existential() {
    let mut unit = fixture::checked_unit();
    let clause = VirSpecClauseId::new(0);
    let false_term = term(&mut unit, clause, VirSpecType::Bool, T::Bool(false));
    unit.specs.assertions_mut()[0].kind = A::Pure(false_term);
    assert_eq!(statuses(&unit), [U]);
}

#[test]
fn symbolic_runtime_and_result_values_can_witness_without_becoming_constants() {
    for result in [false, true] {
        let mut unit = spec_memory::unit();
        let clause = VirSpecClauseId::new(0);
        let function = VirFunctionId::new(0);
        let location = if result {
            VirSpecLocation::FunctionResult { function }
        } else {
            // A real, unconstrained parameter denotes a value even though its
            // interval is not exact. It cannot be guessed as a range endpoint.
            let runtime = &mut unit.runtime.functions[0];
            runtime.signature.parameters.push(VirType::U64);
            runtime.blocks[0].parameters.push(VirValue {
                id: VirValueId::new(6),
                ty: VirType::U64,
            });
            VirSpecLocation::FunctionEntry { function }
        };
        // Rebuild ABI/source metadata after changing the physical signature.
        let mut unit = VirUnit::from_runtime(unit.memory, function, unit.runtime.functions);
        range(&mut unit, 2, 8);
        unit.specs.clauses_mut()[0].location = location;
        unit.specs.proves_mut()[0].location = location;
        unit.specs.terms_mut()[1].kind = T::Snapshot(if result {
            VirSpecSnapshot::Result { function, slot: 0 }
        } else {
            VirSpecSnapshot::Parameter { function, slot: 0 }
        });
        let equality = term(
            &mut unit,
            clause,
            VirSpecType::Bool,
            T::Equal {
                left: VirSpecTermId::new(3),
                right: VirSpecTermId::new(1),
            },
        );
        unit.specs.assertions_mut()[0].kind = A::Pure(equality);
        assert_eq!(statuses(&unit), [P]);
    }
}

#[test]
fn nested_witness_uses_outer_scope_and_alpha_renaming_preserves_proof() {
    let mut unit = fixture::checked_unit();
    let clause = VirSpecClauseId::new(0);
    let outer = binder(&mut unit, clause, VirSpecType::U64);
    let outer_term = term(&mut unit, clause, VirSpecType::U64, T::Binder(outer));
    if let A::Exists { witness, .. } = &mut unit.specs.assertions_mut()[1].kind {
        *witness = Some(outer_term);
    }
    node(
        &mut unit,
        clause,
        A::Exists {
            binder: outer,
            body: VirSpecAssertionId::new(1),
            witness: Some(VirSpecTermId::new(1)),
        },
    );
    assert_eq!(statuses(&unit), [P]);
    // Swap dense binder IDs and names consistently, not just display spelling.
    unit.specs.binders_mut().swap(0, 1);
    for (index, b) in unit.specs.binders_mut().iter_mut().enumerate() {
        b.id = VirSpecBinderId::new(index as u32);
        b.name = format!("renamed{index}");
    }
    for t in unit.specs.terms_mut() {
        if let T::Binder(b) = &mut t.kind {
            *b = VirSpecBinderId::new(1 - b.get());
        }
    }
    for a in unit.specs.assertions_mut() {
        if let A::Exists { binder, .. } = &mut a.kind {
            *binder = VirSpecBinderId::new(1 - binder.get());
        }
    }
    assert_eq!(statuses(&unit), [P]);
}

#[test]
fn existential_wrapping_never_duplicates_write_authority() {
    for mode in 0..3 {
        let mut unit = fixture::checked_unit();
        let clause = VirSpecClauseId::new(0);
        let exists = VirSpecAssertionId::new(1);
        if mode == 1 {
            // repeat one Exists occurrence, sharing only read observations
            if let A::Permission(m) = &mut unit.specs.assertions_mut()[0].kind {
                m.access = SpecAccess::Read;
            }
        }
        let second = if mode == 2 {
            // conflict encountered AFTER leaving binder scope
            let A::Permission(mut m) = unit.specs.assertions()[0].kind.clone() else {
                unreachable!()
            };
            m.end_bytes = VirSpecTermId::new(1);
            node(&mut unit, clause, A::Permission(m))
        } else {
            exists
        };
        node(&mut unit, clause, A::Separation(vec![exists, second]));
        assert_eq!(statuses(&unit), [if mode == 1 { P } else { U }]);
    }
}

#[test]
fn witness_type_scope_and_clause_ownership_are_validated_before_proving() {
    for mutation in 0..5 {
        let mut unit = fixture::checked_unit();
        let clause = VirSpecClauseId::new(0);
        match mutation {
            0 => unit.specs.binders_mut()[0].ty = VirSpecType::Bool,
            1 => {
                // cannot witness itself
                if let A::Exists { witness, .. } = &mut unit.specs.assertions_mut()[1].kind {
                    *witness = Some(VirSpecTermId::new(3));
                }
            }
            2 => {
                // body variable escapes to sibling
                node(
                    &mut unit,
                    clause,
                    A::Separation(vec![VirSpecAssertionId::new(1), VirSpecAssertionId::new(0)]),
                );
            }
            3 => {
                range(&mut unit, 2, 8);
                if let A::Exists { witness, .. } = &mut unit.specs.assertions_mut()[3].kind {
                    *witness = Some(VirSpecTermId::new(1));
                }
            }
            _ => {
                unit.specs.terms_mut()[1].kind = T::Snapshot(VirSpecSnapshot::Value {
                    function: VirFunctionId::new(1),
                    value: VirValueId::new(0),
                });
            }
        }
        assert!(unit.validate().is_err(), "mutation {mutation}");
    }
}

#[test]
fn nested_existential_occurrence_expansion_stops_at_budget() {
    let mut unit = fixture::checked_unit();
    let clause = VirSpecClauseId::new(0);
    let truth = term(&mut unit, clause, VirSpecType::Bool, T::Bool(true));
    unit.specs.assertions_mut()[0].kind = A::Pure(truth);
    let mut root = VirSpecAssertionId::new(1);
    for _ in 0..20 {
        root = node(&mut unit, clause, A::Separation(vec![root, root]));
    }
    assert_eq!(statuses(&unit), [U]);
}
