use super::*;
use crate::{
    HirSpecAssertion, HirSpecAssertionId, HirSpecRoot, ObligationStatus, SpecAccess,
    SpecAssertionKind as A,
};

#[test]
fn separation_lowering_preserves_resources_and_checks_shared_exclusive_and_empty_claims() {
    for mode in 0..3 {
        let mut tables = super::spec_assertions::fixture();
        let mut plain = tables.clone();
        plain.specs = HirSpecEnvironment::empty();
        let plain = lower_test(&hir_from_tables(plain).unwrap()).unwrap();
        tables.specs.assertions.truncate(3);
        if let A::PointsTo { memory, value } = &mut tables.specs.assertions[0].kind {
            *value = None;
            if mode == 0 {
                memory.access = SpecAccess::Read;
            }
        }
        if let A::Permission(memory) = &mut tables.specs.assertions[1].kind {
            if mode == 0 {
                memory.access = SpecAccess::Read;
            }
            if mode == 2 {
                memory.start_bytes = memory.end_bytes;
            }
        }
        tables.specs.assertions[2].kind =
            A::Separation(vec![HirSpecAssertionId::new(0), HirSpecAssertionId::new(1)]);
        tables.specs.clauses[0].root = HirSpecRoot::Assertion(HirSpecAssertionId::new(2));
        let unit = lower_test(&hir_from_tables(tables).unwrap()).unwrap();
        assert_eq!(unit.runtime().stable_dump(), plain.runtime().stable_dump());
        let report = verify_program(
            &unit.resolve().unwrap(),
            crate::CfgAnalysisConfig::default(),
        )
        .unwrap();
        let proof = report
            .functions()
            .values()
            .flat_map(|f| f.proofs())
            .next()
            .unwrap();
        assert_eq!(
            proof.status(),
            if mode == 1 {
                ObligationStatus::Refuted
            } else {
                ObligationStatus::Proven
            },
            "mode {mode}: {:?}",
            report.diagnostics()
        );
        assert_eq!(
            interpret(unit.resolve().unwrap().runtime())
                .unwrap()
                .values(),
            [crate::VirRuntimeValue::U64(42)]
        );
    }
}

#[test]
fn failed_matching_does_not_refute_an_existential_goal() {
    let mut tables = super::spec_assertions::fixture();
    tables.specs.terms[4].kind = HirSpecTermKind::Bool(false);
    tables.specs.assertions[2].kind = A::Pure(HirSpecTermId::new(4));
    let template = tables.specs.assertions[4].clone();
    tables.specs.assertions.push(HirSpecAssertion {
        id: HirSpecAssertionId::new(5),
        kind: A::Separation(vec![HirSpecAssertionId::new(2), HirSpecAssertionId::new(4)]),
        ..template
    });
    tables.specs.clauses[0].root = HirSpecRoot::Assertion(HirSpecAssertionId::new(5));
    let unit = lower_test(&hir_from_tables(tables).unwrap()).unwrap();
    let report = verify_program(
        &unit.resolve().unwrap(),
        crate::CfgAnalysisConfig::default(),
    )
    .unwrap();
    let proof = report
        .functions()
        .values()
        .flat_map(|f| f.proofs())
        .next()
        .unwrap();
    assert_eq!(proof.status(), ObligationStatus::Unknown);
}
