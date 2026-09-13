use nera::*;
#[path = "support/spec_separation.rs"]
mod fixture;
#[path = "support/spec_arena.rs"]
#[allow(dead_code)]
mod spec_arena;
#[path = "support/spec_memory.rs"]
#[allow(dead_code)]
mod spec_memory;
use fixture::{Claim, add};

#[test]
fn arena_matching_composes_with_actual_split_join_and_consumed_permissions() {
    let mut unit = spec_arena::unit(1, 3, spec_arena::Mutation::None);
    let body = &unit.runtime.functions[1].blocks[0].instructions;
    let initialized = body
        .iter()
        .rposition(|i| matches!(i.instruction, VirInstruction::Initialize { .. }))
        .unwrap();
    let joined = body
        .iter()
        .rposition(|i| matches!(i.instruction, VirInstruction::PermissionJoin { .. }))
        .unwrap();
    let location = |ordinal| VirLocation::Instruction {
        function: VirFunctionId::new(1),
        block: VirBlockId::new(0),
        ordinal: ordinal as u64,
    };
    let claims: Vec<_> = [(3, 11), (15, 13), (16, 14)]
        .into_iter()
        .map(|(pointer, authority)| Claim {
            pointer,
            authority,
            points_to: true,
            ..Claim::write(0, 8)
        })
        .collect();
    add(&mut unit, location(initialized), &claims);
    add(&mut unit, location(joined), &claims);
    let empty_consumed: Vec<_> = claims
        .iter()
        .map(|c| Claim { end: c.start, ..*c })
        .collect();
    add(&mut unit, location(joined), &empty_consumed);
    let restored: Vec<_> = [0, 16, 32]
        .into_iter()
        .map(|start| Claim {
            pointer: 3,
            authority: 26,
            points_to: true,
            ..Claim::write(start, start + 8)
        })
        .collect();
    add(&mut unit, location(joined), &restored);
    assert_eq!(
        statuses(&unit, CfgAnalysisConfig::default()),
        [
            ObligationStatus::Proven,
            ObligationStatus::Refuted,
            ObligationStatus::Refuted,
            ObligationStatus::Proven
        ]
    );
    let valid = unit.into_validated().unwrap();
    assert_eq!(
        interpret(valid.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(49)]
    );
}

#[test]
fn shared_loan_occurrences_remain_readable_but_ended_authority_does_not_match() {
    let output = analyze(&SourceFile::from_text(
        "separation-loans.nera",
        "fn main() -> u64 { let mut x=7; let p=&x; let q=&x; return *p + *q; }",
    ));
    assert!(output.vir().is_some(), "{:?}", output.issues());
    let mut unit = output.vir().unwrap().as_unit().clone();
    let body = &unit.runtime.functions[0].blocks[0].instructions;
    let loans: Vec<_> = body
        .iter()
        .enumerate()
        .filter_map(|(ordinal, i)| match i.instruction {
            VirInstruction::LoanBegin {
                reference_result,
                permission_result,
                ..
            }
            | VirInstruction::LoanAliasShared {
                reference_result,
                permission_result,
                ..
            } => Some((ordinal, reference_result.id, permission_result.id)),
            _ => None,
        })
        .collect();
    assert_eq!(loans.len(), 2);
    let ended = body
        .iter()
        .rposition(|i| matches!(i.instruction, VirInstruction::LoanEnd { .. }))
        .unwrap();
    let claims: Vec<_> = loans
        .iter()
        .map(|&(_, pointer, authority)| Claim {
            pointer: pointer.get(),
            authority: authority.get(),
            access: SpecAccess::Read,
            points_to: true,
            ..Claim::write(0, 8)
        })
        .collect();
    add(
        &mut unit,
        VirLocation::Instruction {
            function: VirFunctionId::new(0),
            block: VirBlockId::new(0),
            ordinal: loans[1].0 as u64,
        },
        &claims,
    );
    // Use an explicit location because the fixture's helper reserves ordinal 10
    // for its own terminator, not for arbitrary source programs.
    add(
        &mut unit,
        VirLocation::Instruction {
            function: VirFunctionId::new(0),
            block: VirBlockId::new(0),
            ordinal: ended as u64,
        },
        &claims,
    );
    assert_eq!(
        statuses(&unit, CfgAnalysisConfig::default()),
        [ObligationStatus::Proven, ObligationStatus::Refuted]
    );
}

#[test]
fn nested_dags_preserve_repeated_resources_and_expansion_budgets() {
    let mut unit = fixture::checked_unit();
    let template = unit.specs.assertions()[2].clone();
    // (left * right) * left must conflict even though the nested root passed.
    let root = VirSpecAssertionId::new(3);
    unit.specs.assertions_mut().push(VirSpecAssertion {
        id: root,
        kind: SpecAssertionKind::Separation(vec![template.id, VirSpecAssertionId::new(0)]),
        ..template.clone()
    });
    unit.specs.clauses_mut()[template.clause.get() as usize].kind =
        VirSpecClauseKind::Assertion { root };
    assert_eq!(
        statuses(&unit, CfgAnalysisConfig::default()),
        [ObligationStatus::Refuted]
    );

    let mut unit = fixture::checked_unit();
    unit.specs.assertions_mut()[0].kind = SpecAssertionKind::Alive(spec_memory::snapshot(1));
    let template = unit.specs.assertions()[0].clone();
    let mut root = template.id;
    for _ in 0..20 {
        let id = VirSpecAssertionId::new(unit.specs.assertions().len() as u32);
        unit.specs.assertions_mut().push(VirSpecAssertion {
            id,
            kind: SpecAssertionKind::Separation(vec![root, root]),
            ..template.clone()
        });
        root = id;
    }
    unit.specs.clauses_mut()[template.clause.get() as usize].kind =
        VirSpecClauseKind::Assertion { root };
    assert_eq!(
        statuses(&unit, CfgAnalysisConfig::default()),
        [ObligationStatus::Unknown]
    );
}

fn statuses(unit: &VirUnit, config: CfgAnalysisConfig) -> Vec<ObligationStatus> {
    let valid = unit.clone().into_validated().unwrap();
    let report = verify_program(&valid.resolve().unwrap(), config).unwrap();
    report
        .functions()
        .values()
        .flat_map(|f| f.proofs())
        .map(|p| p.status())
        .collect()
}

#[test]
fn separation_checks_occurrences_aliases_and_requested_access_not_node_identity() {
    use ObligationStatus::{Proven as P, Refuted as R};
    for (claims, expected) in [
        (vec![Claim::write(0, 8), Claim::write(8, 16)], P),
        (vec![Claim::write(0, 8), Claim::write(0, 8)], R),
        (vec![Claim::write(0, 16), Claim::write(8, 16)], R),
        (vec![Claim::write(0, 8), Claim::write(16, 16)], P),
        (vec![Claim::write(8, 8), Claim::write(8, 8)], P),
        (
            vec![
                Claim {
                    access: SpecAccess::Read,
                    ..Claim::write(0, 8)
                };
                2
            ],
            P,
        ),
        (
            vec![
                Claim::write(0, 8),
                Claim {
                    access: SpecAccess::Read,
                    ..Claim::write(0, 8)
                },
            ],
            R,
        ),
        (vec![Claim::write(0, 8), Claim::write(16, 24)], R),
        (vec![Claim::write(0, 8), Claim::write(24, 24)], R),
    ] {
        let mut unit = spec_memory::unit();
        add(&mut unit, spec_memory::location(2), &claims);
        assert_eq!(statuses(&unit, CfgAnalysisConfig::default()), [expected]);
    }
    // Same DAG node appearing twice must still reserve the bytes twice.
    let mut unit = fixture::checked_unit();
    unit.specs.assertions_mut()[2].kind =
        SpecAssertionKind::Separation(vec![VirSpecAssertionId::new(0); 2]);
    assert_eq!(statuses(&unit, CfgAnalysisConfig::default()), [R]);
}

#[test]
fn distinct_ssa_pointer_aliases_cannot_fake_disjoint_storage() {
    let mut raw = spec_memory::unit();
    let span = raw.runtime.functions[0].source_span;
    let access = VirMemoryAccess::core_u64();
    raw.runtime.functions[0].blocks[0].instructions.splice(
        2..2,
        [
            VirInstruction::Constant {
                result: VirValue {
                    id: VirValueId::new(6),
                    ty: VirType::U64,
                },
                value: VirConstant::U64(0),
            },
            VirInstruction::PointerOffset {
                result: VirValue {
                    id: VirValueId::new(7),
                    ty: VirType::Pointer { access },
                },
                base: VirValueId::new(1),
                delta_bytes: VirValueId::new(6),
            },
        ]
        .into_iter()
        .map(|instruction| SpannedVirInstruction {
            instruction,
            source_span: span,
        }),
    );
    let mut unit = VirUnit::from_runtime(raw.memory, raw.runtime.entry, raw.runtime.functions);
    add(
        &mut unit,
        spec_memory::location(4),
        &[
            Claim::write(0, 8),
            Claim {
                pointer: 7,
                ..Claim::write(0, 8)
            },
        ],
    );
    assert_eq!(
        statuses(&unit, CfgAnalysisConfig::default()),
        [ObligationStatus::Refuted]
    );
}

#[test]
fn empty_one_past_claims_cannot_authorize_a_real_load() {
    let mut raw = spec_memory::unit();
    let span = raw.runtime.functions[0].source_span;
    let access = VirMemoryAccess::core_u64();
    raw.runtime.functions[0].blocks[0].instructions.splice(
        2..2,
        [
            VirInstruction::Constant {
                result: VirValue {
                    id: VirValueId::new(6),
                    ty: VirType::U64,
                },
                value: VirConstant::U64(16),
            },
            VirInstruction::PointerOffset {
                result: VirValue {
                    id: VirValueId::new(7),
                    ty: VirType::Pointer { access },
                },
                base: VirValueId::new(1),
                delta_bytes: VirValueId::new(6),
            },
        ]
        .into_iter()
        .map(|instruction| SpannedVirInstruction {
            instruction,
            source_span: span,
        }),
    );
    if let VirInstruction::Load { pointer, .. } =
        &mut raw.runtime.functions[0].blocks[0].instructions[8].instruction
    {
        *pointer = VirValueId::new(7);
    } else {
        unreachable!();
    }
    let mut unit = VirUnit::from_runtime(raw.memory, raw.runtime.entry, raw.runtime.functions);
    add(
        &mut unit,
        spec_memory::location(3),
        &[Claim {
            pointer: 7,
            ..Claim::write(0, 0)
        }; 2],
    );
    let valid = unit.into_validated().unwrap();
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
}

#[test]
fn failed_or_repeated_matches_never_consume_program_authority() {
    let mut unit = spec_memory::unit();
    let runtime = unit
        .clone()
        .into_validated()
        .unwrap()
        .runtime()
        .stable_dump();
    for claims in [
        vec![Claim::write(0, 8); 2],
        vec![Claim::write(0, 8), Claim::write(8, 16)],
        vec![Claim::write(0, 8), Claim::write(8, 16)],
    ] {
        add(&mut unit, spec_memory::location(2), &claims);
    }
    assert_eq!(
        statuses(&unit, CfgAnalysisConfig::default()),
        [
            ObligationStatus::Refuted,
            ObligationStatus::Proven,
            ObligationStatus::Proven
        ]
    );
    let unit = unit.into_validated().unwrap();
    assert_eq!(unit.runtime().stable_dump(), runtime);
    assert_eq!(
        interpret(unit.resolve().unwrap().runtime())
            .unwrap()
            .values(),
        [VirRuntimeValue::U64(7)]
    );
    let report = verify_program(&unit.resolve().unwrap(), CfgAnalysisConfig::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .functions()
            .values()
            .all(|f| f.cfg().all_obligations_proven())
    );
}

#[test]
fn proof_pair_budgets_and_exact_relation_replay_fail_closed() {
    let unit = fixture::checked_unit().into_validated().unwrap();
    let resolved = unit.resolve().unwrap();
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(
        report.is_memory_checked_core0(),
        "{:?}",
        report.diagnostics()
    );
    let proof = &report.functions()[&VirFunctionId::new(0)].proofs()[0];
    let cache = verifier::relation::audit::RelationReplayCache::new(
        &resolved,
        CfgAnalysisConfig::default(),
    )
    .unwrap();
    assert!(proof.relation_queries().iter().any(|q| matches!(
        q.query.goal,
        verifier::relation::audit::QueryGoal::Disjoint(..)
    )));
    assert!(cache.accepts_spec_trace(proof.function(), proof.prove(), proof.relation_queries()));
    let mut changed = proof.relation_queries().to_vec();
    changed.pop();
    assert!(!cache.accepts_spec_trace(proof.function(), proof.prove(), &changed));
    for evidence in proof.relation_queries() {
        assert!(cache.accepts_query(evidence));
        let mut changed = evidence.clone();
        changed.query.status = ObligationStatus::Unknown;
        assert!(!cache.accepts_query(&changed));
    }
    assert_eq!(
        statuses(
            unit.as_unit(),
            CfgAnalysisConfig {
                max_region_pairs_per_instruction: 0,
                ..CfgAnalysisConfig::default()
            }
        ),
        [ObligationStatus::Unknown]
    );
}
