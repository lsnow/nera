use nera::*;
#[path = "support/spec_memory.rs"]
mod fixture;
#[path = "support/spec_arena.rs"]
#[allow(dead_code)]
mod spec_arena;
use fixture::*;

#[test]
fn arena_points_to_uses_the_existing_split_permission_and_preserves_precision_gaps() {
    for mutation in [
        spec_arena::Mutation::None,
        spec_arena::Mutation::DynamicInitialization,
    ] {
        let mut unit = spec_arena::unit(1, 3, mutation);
        let function = VirFunctionId::new(1);
        let ordinal = unit.runtime.functions[1].blocks[0].instructions.iter().position(|i| matches!(i.instruction, VirInstruction::Initialize { pointer, .. } if pointer == VirValueId::new(16))).unwrap();
        let snapshot = |value| VirSpecSnapshot::Value {
            function,
            value: VirValueId::new(value),
        };
        add(
            &mut unit,
            VirLocation::Instruction {
                function,
                block: VirBlockId::new(0),
                ordinal: ordinal as u64,
            },
            |t| SpecAssertionKind::PointsTo {
                memory: SpecMemoryClaim {
                    pointer: snapshot(16),
                    authority: snapshot(14),
                    start_bytes: t[0],
                    end_bytes: t[1],
                    layout: VirMemoryAccess::core_u64(),
                    access: SpecAccess::Write,
                },
                value: None,
            },
        );
        let unit = unit.into_validated().unwrap();
        let report =
            verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
        let status = report.functions()[&function].proofs()[0].status();
        assert_eq!(
            status,
            if matches!(mutation, spec_arena::Mutation::None) {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            }
        );
    }
}

#[test]
fn bool_points_to_checks_current_typed_representation_without_reading_the_heap() {
    let source = SourceFile::from_text(
        "spec-bool.nera",
        "fn main() -> bool { let mut x = true; let p = &mut x; *p = false; return *p; }",
    );
    let output = analyze(&source);
    assert!(output.vir().is_some(), "{:?}", output.issues());
    let mut unit = output.vir().unwrap().as_unit().clone();
    let (ordinal, pointer, permission, access) = unit.runtime.functions[0].blocks[0]
        .instructions
        .iter()
        .enumerate()
        .find_map(|(ordinal, i)| match i.instruction {
            VirInstruction::Store {
                pointer,
                permission,
                access,
                ..
            } if matches!(unit.memory.kind(access.ty), Some(VirMemoryTypeKind::Bool)) => {
                Some((ordinal, pointer, permission, access))
            }
            _ => None,
        })
        .unwrap();
    add(&mut unit, location(ordinal as u32), |t| {
        SpecAssertionKind::PointsTo {
            memory: SpecMemoryClaim {
                pointer: snapshot(pointer.get()),
                authority: snapshot(permission.get()),
                start_bytes: t[0],
                end_bytes: t[1],
                layout: access,
                access: SpecAccess::Write,
            },
            value: Some(t[2]),
        }
    });
    unit.specs.terms_mut()[1].kind = VirSpecTermKind::U64(1);
    unit.specs.terms_mut()[2].ty = VirSpecType::Bool;
    unit.specs.terms_mut()[2].kind = VirSpecTermKind::Bool(false);
    let unit = unit.into_validated().unwrap();
    let report = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::Bool(false)]
    );
}

#[test]
fn call_effects_invalidate_current_authority_without_reusing_the_precall_heap() {
    let source = SourceFile::from_text(
        "spec-call.nera",
        "fn main() -> u64 { let p=alloc<u64>(1); destroy(p); return 0; } fn destroy(p: Own<u64>) { free(p); return; }",
    );
    let output = analyze(&source);
    assert!(output.vir().is_some(), "{:?}", output.issues());
    let mut unit = output.vir().expect("valid owning call").as_unit().clone();
    let body = &unit.runtime.functions[0].blocks[0].instructions;
    let pointer = body
        .iter()
        .find_map(|i| match i.instruction {
            VirInstruction::Allocate { pointer_result, .. } => Some(pointer_result.id),
            _ => None,
        })
        .unwrap();
    let call = body
        .iter()
        .position(|i| matches!(i.instruction, VirInstruction::Call { .. }))
        .unwrap() as u32;
    add(&mut unit, location(call - 1), |_| {
        SpecAssertionKind::Alive(snapshot(pointer.get()))
    });
    add(&mut unit, location(call), |_| {
        SpecAssertionKind::Alive(snapshot(pointer.get()))
    });
    let result = proofs(unit);
    assert_eq!(result[0], ObligationStatus::Proven);
    assert_ne!(result[1], ObligationStatus::Proven);
}

fn proofs(unit: VirUnit) -> Vec<ObligationStatus> {
    let unit = unit.into_validated().unwrap();
    let report = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    report.functions()[&VirFunctionId::new(0)]
        .proofs()
        .iter()
        .map(|p| p.status())
        .collect()
}

#[test]
fn queries_observe_current_writes_deinitialization_and_free_without_heap_value_guessing() {
    use ObligationStatus::{Proven as P, Refuted as R};
    use SpecAssertionKind as A;
    let mut unit = unit();
    let runtime = unit
        .clone()
        .into_validated()
        .unwrap()
        .runtime()
        .stable_dump();
    let mut expected = vec![];
    for (point, init, live) in [
        (2, R, P),
        (3, P, P),
        (5, P, P),
        (7, R, P),
        (8, P, P),
        (10, R, R),
    ] {
        add(&mut unit, location(point), |_| A::Alive(snapshot(1)));
        expected.push(live);
        add(&mut unit, location(point), |t| A::Initialized {
            pointer: snapshot(1),
            start_bytes: t[0],
            end_bytes: t[1],
            layout: VirMemoryAccess::core_u64(),
        });
        expected.push(init);
        add(&mut unit, location(point), |t| A::Permission(claim(t)));
        expected.push(live);
        add(&mut unit, location(point), |t| A::PointsTo {
            memory: claim(t),
            value: None,
        });
        expected.push(init);
        add(&mut unit, location(point), |t| A::PointsTo {
            memory: claim(t),
            value: Some(t[2]),
        });
        expected.push(if point == 3 { P } else { R });
        add(&mut unit, location(point), |_| A::SameAllocation {
            left: snapshot(1),
            right: snapshot(1),
        });
        expected.push(P);
    }
    assert_eq!(
        unit.clone()
            .into_validated()
            .unwrap()
            .runtime()
            .stable_dump(),
        runtime
    );
    assert_eq!(proofs(unit), expected);
}

#[test]
fn checked_memory_assertions_are_erased_and_relation_traces_replay() {
    let unit = checked_unit().into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    assert_eq!(
        interpret(resolved.runtime()).unwrap().values(),
        [VirRuntimeValue::U64(7)]
    );
    let cache = verifier::relation::audit::RelationReplayCache::new(
        &resolved,
        CfgAnalysisConfig::default(),
    )
    .unwrap();
    for proof in report.functions()[&VirFunctionId::new(0)].proofs() {
        assert_eq!(proof.status(), ObligationStatus::Proven);
        assert!(!proof.relation_queries().is_empty());
        assert!(cache.accepts_spec_trace(
            proof.function(),
            proof.prove(),
            proof.relation_queries()
        ));
        assert!(!cache.accepts_spec_trace(proof.function(), proof.prove(), &[]));
        for evidence in proof.relation_queries() {
            assert!(cache.accepts_query(evidence));
            let mut changed = evidence.clone();
            changed.query.status = ObligationStatus::Unknown;
            assert!(!cache.accepts_query(&changed));
        }
    }
}

#[test]
fn observations_cannot_discharge_real_uninitialized_access_and_forged_authority_is_rejected() {
    let mut valid = unit();
    add(&mut valid, location(5), |_| {
        SpecAssertionKind::Alive(snapshot(1))
    });
    // Real load now executes after deinitialization, although alive still holds.
    valid.runtime.functions[0].blocks[0].instructions[5].instruction =
        VirInstruction::ObjectDeinitialize {
            pointer: VirValueId::new(1),
            permission: VirValueId::new(2),
            access: VirMemoryAccess::core_u64(),
        };
    let valid = valid.into_validated().unwrap();
    let report = verify_program(&valid.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert_eq!(
        report.functions()[&VirFunctionId::new(0)].proofs()[0].status(),
        ObligationStatus::Proven
    );
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .diagnostics()
            .iter()
            .any(|d| d.kind() == VerifierDiagnosticKind::RefutedObligation)
    );
    for mutation in 0..5 {
        let mut unit = checked_unit();
        match mutation {
            0 => {
                if let SpecAssertionKind::Permission(m) = &mut unit.specs.assertions_mut()[0].kind {
                    m.authority = snapshot(1);
                }
            }
            1 => {
                if let SpecAssertionKind::Permission(m) = &mut unit.specs.assertions_mut()[0].kind {
                    m.pointer = snapshot(2);
                }
            }
            2 => unit.specs.assertions_mut()[0].kind = SpecAssertionKind::Alive(snapshot(5)), // later definition
            3 => {
                unit.specs.assertions_mut()[0].kind = SpecAssertionKind::SameAllocation {
                    left: snapshot(1),
                    right: VirSpecSnapshot::Value {
                        function: VirFunctionId::new(99),
                        value: VirValueId::new(1),
                    },
                }
            }
            _ => unit.version = VirUnitVersion::V20,
        }
        assert!(unit.validate().is_err(), "mutation {mutation}");
    }
}
