use super::*;
use crate::{
    HirSpecAssertionId, HirSpecBinderId, HirSpecRoot, ObligationStatus, SpecAssertionKind as A,
};

#[test]
fn explicit_witness_is_lowered_proved_and_erased() {
    for boolean in [false, true] {
        let mut tables = super::spec_assertions::fixture();
        tables.specs.assertions.truncate(1);
        tables.specs.assertions[0].kind = A::Pure(HirSpecTermId::new(5));
        if boolean {
            let ty = tables.specs.terms[4].ty;
            tables.specs.binders[0].ty = ty;
            tables.specs.terms[2].ty = ty;
            tables.specs.terms[2].kind = HirSpecTermKind::Bool(true);
            tables.specs.terms[3].ty = ty;
        }
        let mut exists = tables.specs.assertions[0].clone();
        exists.id = HirSpecAssertionId::new(1);
        exists.kind = A::Exists {
            binder: HirSpecBinderId::new(0),
            body: HirSpecAssertionId::new(0),
            witness: Some(HirSpecTermId::new(2)),
        };
        tables.specs.assertions.push(exists);
        tables.specs.clauses[0].root = HirSpecRoot::Assertion(HirSpecAssertionId::new(1));
        let mut plain = tables.clone();
        plain.specs = HirSpecEnvironment::empty();
        let plain = lower_test(&hir_from_tables(plain).unwrap()).unwrap();
        let unit = lower_test(&hir_from_tables(tables).unwrap()).unwrap();
        let report = verify_program(
            &unit.resolve().unwrap(),
            crate::CfgAnalysisConfig::default(),
        )
        .unwrap();
        assert!(
            report.is_memory_checked_core0(),
            "{:?}",
            report.diagnostics()
        );
        assert!(
            report
                .functions()
                .values()
                .flat_map(|f| f.proofs())
                .all(|p| p.status() == ObligationStatus::Proven)
        );
        assert_eq!(unit.runtime().stable_dump(), plain.runtime().stable_dump());
        assert_eq!(
            X86_64_UNKNOWN_LINUX_GNU
                .codegen_program(unit.resolve().unwrap().runtime())
                .unwrap(),
            X86_64_UNKNOWN_LINUX_GNU
                .codegen_program(plain.resolve().unwrap().runtime())
                .unwrap()
        );
    }
}
