use nera::*;
#[path = "support/spec_exists.rs"]
mod spec_exists;
#[path = "support/spec_memory.rs"]
#[allow(dead_code)]
mod spec_memory;
#[path = "support/spec_separation.rs"]
#[allow(dead_code)]
mod spec_separation;

#[test]
fn witness_theory_and_budget_failures_are_distinct_and_do_not_grant_authority() {
    for (case, expected) in [
        (0, SpecFailure::InvalidWitness),
        (1, SpecFailure::UnsupportedTheory),
        (2, SpecFailure::BudgetExceeded),
    ] {
        let mut config = CfgAnalysisConfig::default();
        let mut unit = spec_memory::unit();
        match case {
            0 => {
                unit = spec_exists::checked_unit();
                if let SpecAssertionKind::Exists { witness, .. } =
                    &mut unit.specs.assertions_mut()[1].kind
                {
                    *witness = None;
                }
            }
            1 => {
                spec_memory::add(&mut unit, spec_memory::location(3), |terms| {
                    SpecAssertionKind::PointsTo {
                        memory: spec_memory::claim(terms),
                        value: Some(terms[2]),
                    }
                });
                // Single-cell value observations are supported since 8.2.
                // A scalar value over a partial-cell range is still outside
                // that theory; keep testing a genuinely unsupported shape.
                unit.specs.terms_mut()[1].kind = VirSpecTermKind::U64(4);
            }
            _ => {
                spec_separation::add(
                    &mut unit,
                    spec_memory::location(2),
                    &[
                        spec_separation::Claim::write(0, 8),
                        spec_separation::Claim::write(8, 16),
                    ],
                );
                config.max_region_pairs_per_instruction = 0;
            }
        }
        let unit = unit.into_validated().unwrap();
        let report = verify_program(&unit.resolve().unwrap(), config).unwrap();
        let proof = &report.functions()[&VirFunctionId::new(0)].proofs()[0];
        assert_eq!(proof.status(), ObligationStatus::Unknown);
        assert_eq!(proof.failure(), Some(expected));
        assert!(unit.as_unit().specs.trust_entries().is_empty());
    }
}
