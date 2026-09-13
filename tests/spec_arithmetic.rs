use nera::*;
#[path = "support/spec_arithmetic.rs"]
mod fixture;
#[path = "support/spec_arena.rs"]
#[allow(dead_code)]
mod spec_arena;

#[test]
fn checked_arena_queries_are_context_bound_replayable_and_runtime_erased() {
    let unit = fixture::unit(8).into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let proof = &report.functions()[&VirFunctionId::new(1)].proofs()[0];
    assert_eq!(proof.status(), ObligationStatus::Proven);
    assert!(!proof.relation_queries().is_empty());
    let cache = nera::verifier::relation::audit::RelationReplayCache::new(
        &resolved,
        CfgAnalysisConfig::default(),
    )
    .unwrap();
    for query in proof.relation_queries() {
        assert!(cache.accepts_query(query));
        let mut changed = query.clone();
        changed.query.status = ObligationStatus::Unknown;
        if changed != *query {
            assert!(!cache.accepts_query(&changed));
        }
        let mut changed = query.clone();
        changed.config.max_block_visits += 1;
        assert!(!cache.accepts_query(&changed));
        let mut changed = query.clone();
        changed.query_ordinal += 1000;
        assert!(!cache.accepts_query(&changed));
        let mut changed = query.clone();
        changed.query.witness = nera::verifier::relation::audit::QueryWitness::Bounds(vec![]);
        assert!(!cache.accepts_query(&changed));
    }
    assert!(cache.accepts_spec_trace(proof.function(), proof.prove(), proof.relation_queries()));
    assert!(!cache.accepts_spec_trace(proof.function(), proof.prove(), &[]));
    let mut reversed = proof.relation_queries().to_vec();
    reversed.reverse();
    assert!(!cache.accepts_spec_trace(proof.function(), proof.prove(), &reversed));
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(49)]
    );
    let overflow = fixture::unit(u64::MAX).into_validated().unwrap();
    assert_eq!(
        unit.runtime().stable_dump(),
        overflow.runtime().stable_dump()
    );
    let overflow = overflow.resolve().unwrap();
    let report = verify_program(&overflow, CfgAnalysisConfig::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert_eq!(
        report.functions()[&VirFunctionId::new(1)].proofs()[0].status(),
        ObligationStatus::Unknown
    );
    let changed = nera::verifier::relation::audit::RelationReplayCache::new(
        &overflow,
        CfgAnalysisConfig::default(),
    )
    .unwrap();
    assert!(
        proof
            .relation_queries()
            .iter()
            .all(|q| !changed.accepts_query(q))
    );
    let dump = unit.stable_dump();
    for operator in [
        "checked-add",
        "checked-sub",
        "checked-scale",
        "range-contains bytes",
        "range-disjoint bytes",
    ] {
        assert!(dump.contains(operator));
    }
}

#[test]
fn numeric_schema_rejects_foreign_terms_wrong_types_and_forward_edges() {
    for mutation in 0..6 {
        let mut unit = fixture::unit(8);
        match mutation {
            0 => unit.specs.terms_mut()[7].ty = VirSpecType::Bool,
            1 => {
                unit.specs.terms_mut()[7].kind = VirSpecTermKind::CheckedAdd {
                    left: VirSpecTermId::new(7),
                    right: VirSpecTermId::new(6),
                }
            }
            2 => {
                unit.specs.terms_mut()[8].kind = VirSpecTermKind::CheckedSub {
                    left: VirSpecTermId::new(99),
                    right: VirSpecTermId::new(2),
                }
            }
            3 => {
                unit.specs.terms_mut()[10].kind = VirSpecTermKind::RangeContains {
                    outer_start: VirSpecTermId::new(4),
                    outer_end: VirSpecTermId::new(5),
                    inner_start: VirSpecTermId::new(9),
                    inner_end: VirSpecTermId::new(3),
                }
            }
            4 => unit.specs.terms_mut()[2].clause = VirSpecClauseId::new(0),
            _ => {
                unit.specs.terms_mut()[2].kind = VirSpecTermKind::CheckedScale {
                    operand: VirSpecTermId::new(99),
                    stride: 8,
                }
            }
        }
        assert!(unit.validate().is_err(), "{mutation}");
    }
}
