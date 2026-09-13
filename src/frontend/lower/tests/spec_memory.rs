use super::*;
use crate::{
    HirSpecAssertionId, HirSpecRoot, ObligationStatus, SpecAssertionKind as A, VirSpecAssertionKind,
};

fn fixture(kind: usize) -> HirProgramTables {
    let mut tables = super::spec_assertions::fixture();
    let A::PointsTo { memory, .. } = tables.specs.assertions[0].kind.clone() else {
        unreachable!()
    };
    tables.specs.assertions.truncate(1);
    tables.specs.assertions[0].kind = match kind {
        0 => A::Alive(memory.pointer),
        1 => A::SameAllocation {
            left: memory.pointer,
            right: memory.pointer,
        },
        2 => A::Initialized {
            pointer: memory.pointer,
            start_bytes: memory.start_bytes,
            end_bytes: memory.end_bytes,
            layout: memory.layout,
        },
        3 => A::Permission(memory),
        4 => A::PointsTo {
            memory,
            value: None,
        },
        5 => A::PointsTo {
            memory,
            value: Some(HirSpecTermId::new(2)),
        },
        _ => A::Pure(HirSpecTermId::new(4)),
    };
    tables.specs.clauses[0].root = HirSpecRoot::Assertion(HirSpecAssertionId::new(0));
    tables
}

#[test]
fn memory_hir_lowers_to_real_authority_and_checked_state_observations() {
    for kind in 0..7 {
        let tables = fixture(kind);
        let mut plain = tables.clone();
        plain.specs = HirSpecEnvironment::empty();
        let plain = lower_test(&hir_from_tables(plain).unwrap()).unwrap();
        let unit = lower_test(&hir_from_tables(tables).unwrap()).unwrap();
        assert_eq!(unit.runtime().stable_dump(), plain.runtime().stable_dump());
        let assertion = &unit.as_unit().specs.assertions()[0];
        if let VirSpecAssertionKind::Permission(memory)
        | VirSpecAssertionKind::PointsTo { memory, .. } = &assertion.kind
        {
            assert!(matches!(
                memory.pointer,
                VirSpecSnapshot::Parameter { slot: 0, .. }
            ));
            assert!(matches!(
                memory.authority,
                VirSpecSnapshot::Parameter { slot: 1, .. }
            ));
        }
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
            if kind == 5 {
                ObligationStatus::Unknown
            } else {
                ObligationStatus::Proven
            },
            "kind {kind}: {:?}",
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
fn memory_observation_hir_rejects_foreign_snapshots_ranges_and_layouts() {
    for mutation in 0..5 {
        let mut tables = fixture(2);
        match mutation {
            0 => {
                if let A::Initialized { pointer, .. } = &mut tables.specs.assertions[0].kind {
                    *pointer = HirSpecSnapshot::Local {
                        function: HirFunctionId::new(99),
                        local: crate::HirLocalId::new(0),
                    };
                }
            }
            1 => {
                if let A::Initialized { start_bytes, .. } = &mut tables.specs.assertions[0].kind {
                    *start_bytes = HirSpecTermId::new(4);
                }
            }
            2 => {
                if let A::Initialized { end_bytes, .. } = &mut tables.specs.assertions[0].kind {
                    *end_bytes = HirSpecTermId::new(99);
                }
            }
            3 => {
                if let A::Initialized { layout, .. } = &mut tables.specs.assertions[0].kind {
                    *layout = tables.specs.terms[4].ty;
                }
            }
            _ => {
                tables.specs.assertions[0].kind = A::SameAllocation {
                    left: HirSpecSnapshot::Result {
                        function: HirFunctionId::new(0),
                    },
                    right: HirSpecSnapshot::Result {
                        function: HirFunctionId::new(0),
                    },
                }
            }
        }
        assert!(hir_from_tables(tables).is_err(), "{mutation}");
    }
}
