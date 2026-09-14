use nera::{
    ByteSpan, CfgAnalysisConfig, ObligationStatus, SpannedVirInstruction, SpannedVirTerminator,
    VerifierDiagnosticKind, VerifierFindingSite, VerifierSpecEntity, VirBasicBlock, VirBlockId,
    VirBlockTarget, VirConstant, VirContractId, VirContractPosition, VirFunction, VirFunctionId,
    VirInstruction, VirLocation, VirMemorySchema, VirPredicate, VirPredicateId, VirSignature,
    VirSpecBinder, VirSpecBinderId, VirSpecBinderOwner, VirSpecClause, VirSpecClauseId,
    VirSpecClauseKind, VirSpecClauseOrigin, VirSpecClauseOwner, VirSpecLocation,
    VirSpecLoopInvariant, VirSpecLoopInvariantId, VirSpecProve, VirSpecProveId, VirSpecSnapshot,
    VirSpecTables, VirSpecTerm, VirSpecTermId, VirSpecTermKind, VirSpecType, VirTerminator,
    VirTrustEntry, VirTrustEntryId, VirTrustPolicyKind, VirTrustScope, VirType, VirUnit,
    VirValidationErrorKind, VirValue, VirValueId, verify_program,
};

fn span() -> ByteSpan {
    ByteSpan::new(0, 20).expect("fixture span")
}

fn raw_identity_unit() -> VirUnit {
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "identity".to_owned(),
            signature: VirSignature {
                parameters: vec![VirType::U64],
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: vec![VirValue {
                    id: VirValueId::new(0),
                    ty: VirType::U64,
                }],
                instructions: Vec::new(),
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return {
                        values: vec![VirValueId::new(0)],
                    },
                    source_span: span(),
                },
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

fn raw_branch_unit() -> VirUnit {
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "branch".to_owned(),
            signature: VirSignature {
                parameters: vec![VirType::Bool],
                results: Vec::new(),
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![
                VirBasicBlock {
                    id: VirBlockId::new(0),
                    parameters: vec![VirValue {
                        id: VirValueId::new(0),
                        ty: VirType::Bool,
                    }],
                    instructions: Vec::new(),
                    terminator: SpannedVirTerminator {
                        terminator: VirTerminator::Branch {
                            condition: VirValueId::new(0),
                            then_target: VirBlockTarget {
                                block: VirBlockId::new(1),
                                arguments: vec![VirValueId::new(0)],
                            },
                            else_target: VirBlockTarget {
                                block: VirBlockId::new(2),
                                arguments: Vec::new(),
                            },
                        },
                        source_span: span(),
                    },
                    source_span: span(),
                },
                VirBasicBlock {
                    id: VirBlockId::new(1),
                    parameters: vec![VirValue {
                        id: VirValueId::new(1),
                        ty: VirType::Bool,
                    }],
                    instructions: Vec::new(),
                    terminator: SpannedVirTerminator {
                        terminator: VirTerminator::Return { values: Vec::new() },
                        source_span: span(),
                    },
                    source_span: span(),
                },
                VirBasicBlock {
                    id: VirBlockId::new(2),
                    parameters: Vec::new(),
                    instructions: Vec::new(),
                    terminator: SpannedVirTerminator {
                        terminator: VirTerminator::Return { values: Vec::new() },
                        source_span: span(),
                    },
                    source_span: span(),
                },
            ],
            source_span: span(),
        }],
    )
}

fn raw_constant_result_unit() -> VirUnit {
    VirUnit::from_runtime(
        VirMemorySchema::core_u64(),
        VirFunctionId::new(0),
        vec![VirFunction {
            id: VirFunctionId::new(0),
            name: "constant_result".to_owned(),
            signature: VirSignature {
                parameters: Vec::new(),
                results: vec![VirType::U64],
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: vec![VirBasicBlock {
                id: VirBlockId::new(0),
                parameters: Vec::new(),
                instructions: vec![SpannedVirInstruction {
                    instruction: VirInstruction::Constant {
                        result: VirValue {
                            id: VirValueId::new(0),
                            ty: VirType::U64,
                        },
                        value: VirConstant::U64(7),
                    },
                    source_span: span(),
                }],
                terminator: SpannedVirTerminator {
                    terminator: VirTerminator::Return {
                        values: vec![VirValueId::new(0)],
                    },
                    source_span: span(),
                },
                source_span: span(),
            }],
            source_span: span(),
        }],
    )
}

fn origin(unit: &VirUnit) -> nera::VirOriginId {
    unit.source_map
        .origin_at(VirLocation::FunctionEntry {
            function: VirFunctionId::new(0),
        })
        .expect("function origin")
        .id
}

fn add_entry_prove(unit: &mut VirUnit) {
    let origin = origin(unit);
    unit.specs.terms_mut().extend([
        VirSpecTerm {
            id: VirSpecTermId::new(0),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::U64,
            kind: VirSpecTermKind::Snapshot(VirSpecSnapshot::Parameter {
                function: VirFunctionId::new(0),
                slot: 0,
            }),
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(1),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::U64,
            kind: VirSpecTermKind::U64(10),
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(2),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::LessThan {
                left: VirSpecTermId::new(0),
                right: VirSpecTermId::new(1),
            },
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(3),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::LessOrEqual {
                left: VirSpecTermId::new(0),
                right: VirSpecTermId::new(1),
            },
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(4),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::Equal {
                left: VirSpecTermId::new(0),
                right: VirSpecTermId::new(1),
            },
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(5),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::Not(VirSpecTermId::new(4)),
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(6),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::And(vec![VirSpecTermId::new(2), VirSpecTermId::new(3)]),
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(7),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::Or(vec![VirSpecTermId::new(5), VirSpecTermId::new(6)]),
            origin,
        },
    ]);
    unit.specs.clauses_mut().push(VirSpecClause {
        id: VirSpecClauseId::new(0),
        owner: VirSpecClauseOwner::Prove(VirSpecProveId::new(0)),
        location: VirSpecLocation::FunctionEntry {
            function: VirFunctionId::new(0),
        },
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic {
            root: VirSpecTermId::new(7),
        },
    });
    unit.specs.proves_mut().push(VirSpecProve {
        id: VirSpecProveId::new(0),
        function: VirFunctionId::new(0),
        location: VirSpecLocation::FunctionEntry {
            function: VirFunctionId::new(0),
        },
        clause: VirSpecClauseId::new(0),
        origin,
    });
}

fn add_result_contract_clause(unit: &mut VirUnit) {
    let origin = origin(unit);
    unit.specs.terms_mut().extend([
        VirSpecTerm {
            id: VirSpecTermId::new(0),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::U64,
            kind: VirSpecTermKind::Snapshot(VirSpecSnapshot::Result {
                function: VirFunctionId::new(0),
                slot: 0,
            }),
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(1),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::U64,
            kind: VirSpecTermKind::U64(10),
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(2),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::Equal {
                left: VirSpecTermId::new(0),
                right: VirSpecTermId::new(1),
            },
            origin,
        },
    ]);
    unit.specs.clauses_mut().push(VirSpecClause {
        id: VirSpecClauseId::new(0),
        owner: VirSpecClauseOwner::Contract {
            contract: VirContractId::new(0),
            position: VirContractPosition::Ensures,
        },
        location: VirSpecLocation::FunctionResult {
            function: VirFunctionId::new(0),
        },
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic {
            root: VirSpecTermId::new(2),
        },
    });
    unit.specs
        .contract_mut(VirContractId::new(0))
        .expect("contract")
        .clauses
        .push(VirSpecClauseId::new(0));
}

fn add_boolean_prove(unit: &mut VirUnit, value: bool) {
    let origin = origin(unit);
    unit.specs.terms_mut().push(VirSpecTerm {
        id: VirSpecTermId::new(0),
        clause: VirSpecClauseId::new(0),
        ty: VirSpecType::Bool,
        kind: VirSpecTermKind::Bool(value),
        origin,
    });
    unit.specs.clauses_mut().push(VirSpecClause {
        id: VirSpecClauseId::new(0),
        owner: VirSpecClauseOwner::Prove(VirSpecProveId::new(0)),
        location: VirSpecLocation::FunctionEntry {
            function: VirFunctionId::new(0),
        },
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic {
            root: VirSpecTermId::new(0),
        },
    });
    unit.specs.proves_mut().push(VirSpecProve {
        id: VirSpecProveId::new(0),
        function: VirFunctionId::new(0),
        location: VirSpecLocation::FunctionEntry {
            function: VirFunctionId::new(0),
        },
        clause: VirSpecClauseId::new(0),
        origin,
    });
}

fn add_trusted_bound_and_matching_prove(unit: &mut VirUnit) {
    let origin = origin(unit);
    for (clause, base) in [(0, 0), (1, 3)] {
        unit.specs.terms_mut().extend([
            VirSpecTerm {
                id: VirSpecTermId::new(base),
                clause: VirSpecClauseId::new(clause),
                ty: VirSpecType::U64,
                kind: VirSpecTermKind::Snapshot(VirSpecSnapshot::Parameter {
                    function: VirFunctionId::new(0),
                    slot: 0,
                }),
                origin,
            },
            VirSpecTerm {
                id: VirSpecTermId::new(base + 1),
                clause: VirSpecClauseId::new(clause),
                ty: VirSpecType::U64,
                kind: VirSpecTermKind::U64(10),
                origin,
            },
            VirSpecTerm {
                id: VirSpecTermId::new(base + 2),
                clause: VirSpecClauseId::new(clause),
                ty: VirSpecType::Bool,
                kind: VirSpecTermKind::LessThan {
                    left: VirSpecTermId::new(base),
                    right: VirSpecTermId::new(base + 1),
                },
                origin,
            },
        ]);
    }
    unit.specs.clauses_mut().extend([
        VirSpecClause {
            id: VirSpecClauseId::new(0),
            owner: VirSpecClauseOwner::TrustEntry(VirTrustEntryId::new(0)),
            location: VirSpecLocation::FunctionEntry {
                function: VirFunctionId::new(0),
            },
            origin: VirSpecClauseOrigin::Explicit { origin },
            kind: VirSpecClauseKind::Logic {
                root: VirSpecTermId::new(2),
            },
        },
        VirSpecClause {
            id: VirSpecClauseId::new(1),
            owner: VirSpecClauseOwner::Prove(VirSpecProveId::new(0)),
            location: VirSpecLocation::FunctionEntry {
                function: VirFunctionId::new(0),
            },
            origin: VirSpecClauseOrigin::Explicit { origin },
            kind: VirSpecClauseKind::Logic {
                root: VirSpecTermId::new(5),
            },
        },
    ]);
    unit.specs.trust_entries_mut().push(VirTrustEntry {
        id: VirTrustEntryId::new(0),
        scope: VirTrustScope::FunctionEntry {
            function: VirFunctionId::new(0),
        },
        policy: VirTrustPolicyKind::EntryPointAssumption,
        clause: VirSpecClauseId::new(0),
        origin,
    });
    unit.specs.proves_mut().push(VirSpecProve {
        id: VirSpecProveId::new(0),
        function: VirFunctionId::new(0),
        location: VirSpecLocation::FunctionEntry {
            function: VirFunctionId::new(0),
        },
        clause: VirSpecClauseId::new(1),
        origin,
    });
}

#[test]
fn typed_prove_validates_dumps_and_cannot_change_runtime_view() {
    let mut unit = raw_identity_unit();
    let runtime_before = unit.runtime().stable_dump();
    add_entry_prove(&mut unit);
    unit.specs = nera::VirSpecEnvironment::from_tables(VirSpecTables {
        assertions: unit.specs.assertions().to_vec(),
        contracts: unit.specs.contracts().to_vec(),
        predicates: unit.specs.predicates().to_vec(),
        binders: unit.specs.binders().to_vec(),
        terms: unit.specs.terms().to_vec(),
        clauses: unit.specs.clauses().to_vec(),
        proves: unit.specs.proves().to_vec(),
        trust_entries: unit.specs.trust_entries().to_vec(),
        loop_invariants: unit.specs.loop_invariants().to_vec(),
    });

    let validated = unit.into_validated().expect("typed prove validates");
    assert_eq!(validated.runtime().stable_dump(), runtime_before);
    let dump = validated.stable_dump();
    assert!(dump.contains("term term7 clause0: bool"));
    assert!(dump.contains("clause clause0 prove0 at fn0:entry"));
    assert!(dump.contains("prove prove0 function fn0 at fn0:entry"));
}

#[test]
fn prove_results_are_three_valued_and_only_proven_is_verified() {
    for (value, expected, diagnostic) in [
        (true, ObligationStatus::Proven, None),
        (
            false,
            ObligationStatus::Refuted,
            Some(VerifierDiagnosticKind::RefutedProof),
        ),
    ] {
        let mut unit = raw_identity_unit();
        let expected_origin = origin(&unit);
        add_boolean_prove(&mut unit, value);
        let validated = unit.into_validated().expect("boolean Prove validates");
        let verification = verify_program(
            &validated.resolve().expect("verification input resolves"),
            CfgAnalysisConfig::default(),
        )
        .expect("typed Prove is evaluated");
        let proof = &verification.functions()[&VirFunctionId::new(0)].proofs()[0];
        assert_eq!(proof.status(), expected);
        assert_eq!(proof.finding().origin(), expected_origin);
        assert_eq!(proof.finding().source_span(), span());
        assert_eq!(
            proof.finding().site(),
            VerifierFindingSite::Spec {
                location: VirSpecLocation::FunctionEntry {
                    function: VirFunctionId::new(0),
                },
                entity: VerifierSpecEntity::Prove(VirSpecProveId::new(0)),
                occurrence: None,
            }
        );
        assert_eq!(verification.is_memory_checked_core0(), expected.is_proven());
        assert_eq!(
            verification.diagnostics().first().map(|item| item.kind()),
            diagnostic
        );
    }

    let mut unknown = raw_identity_unit();
    add_entry_prove(&mut unknown);
    let validated = unknown.into_validated().expect("symbolic Prove validates");
    let verification = verify_program(
        &validated.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("symbolic Prove remains a verifier result");
    assert_eq!(
        verification.functions()[&VirFunctionId::new(0)].proofs()[0].status(),
        ObligationStatus::Unknown
    );
    assert!(!verification.is_memory_checked_core0());
    assert_eq!(
        verification.diagnostics()[0].kind(),
        VerifierDiagnosticKind::UnknownProof
    );
}

#[test]
fn prove_at_runtime_location_uses_the_cfg_path_fact() {
    let mut unit = raw_branch_unit();
    let origin = origin(&unit);
    let location = VirSpecLocation::Runtime(VirLocation::BlockEntry {
        function: VirFunctionId::new(0),
        block: VirBlockId::new(1),
    });
    unit.specs.terms_mut().push(VirSpecTerm {
        id: VirSpecTermId::new(0),
        clause: VirSpecClauseId::new(0),
        ty: VirSpecType::Bool,
        kind: VirSpecTermKind::Snapshot(VirSpecSnapshot::Value {
            function: VirFunctionId::new(0),
            value: VirValueId::new(1),
        }),
        origin,
    });
    unit.specs.clauses_mut().push(VirSpecClause {
        id: VirSpecClauseId::new(0),
        owner: VirSpecClauseOwner::Prove(VirSpecProveId::new(0)),
        location,
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic {
            root: VirSpecTermId::new(0),
        },
    });
    unit.specs.proves_mut().push(VirSpecProve {
        id: VirSpecProveId::new(0),
        function: VirFunctionId::new(0),
        location,
        clause: VirSpecClauseId::new(0),
        origin,
    });

    let mut unavailable = unit.clone();
    unavailable.specs.terms_mut()[0].kind = VirSpecTermKind::Snapshot(VirSpecSnapshot::Value {
        function: VirFunctionId::new(0),
        value: VirValueId::new(0),
    });
    assert!(matches!(
        unavailable
            .into_validated()
            .expect_err("cross-block SSA values require a target block parameter")
            .kind(),
        VirValidationErrorKind::InvalidSpecSnapshot(_)
    ));

    let validated = unit
        .into_validated()
        .expect("runtime-location Prove validates");
    let verification = verify_program(
        &validated.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("runtime-location Prove is evaluated after CFG fixed point");
    assert_eq!(
        verification.functions()[&VirFunctionId::new(0)].proofs()[0].status(),
        ObligationStatus::Proven
    );
}

#[test]
fn prove_at_function_result_checks_every_reachable_return_state() {
    let mut unit = raw_constant_result_unit();
    let origin = origin(&unit);
    unit.specs.terms_mut().extend([
        VirSpecTerm {
            id: VirSpecTermId::new(0),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::U64,
            kind: VirSpecTermKind::Snapshot(VirSpecSnapshot::Result {
                function: VirFunctionId::new(0),
                slot: 0,
            }),
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(1),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::U64,
            kind: VirSpecTermKind::U64(7),
            origin,
        },
        VirSpecTerm {
            id: VirSpecTermId::new(2),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::Equal {
                left: VirSpecTermId::new(0),
                right: VirSpecTermId::new(1),
            },
            origin,
        },
    ]);
    let location = VirSpecLocation::FunctionResult {
        function: VirFunctionId::new(0),
    };
    unit.specs.clauses_mut().push(VirSpecClause {
        id: VirSpecClauseId::new(0),
        owner: VirSpecClauseOwner::Prove(VirSpecProveId::new(0)),
        location,
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic {
            root: VirSpecTermId::new(2),
        },
    });
    unit.specs.proves_mut().push(VirSpecProve {
        id: VirSpecProveId::new(0),
        function: VirFunctionId::new(0),
        location,
        clause: VirSpecClauseId::new(0),
        origin,
    });

    let validated = unit.into_validated().expect("result Prove validates");
    let verification = verify_program(
        &validated.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("result Prove is evaluated over the return state");
    assert_eq!(
        verification.functions()[&VirFunctionId::new(0)].proofs()[0].status(),
        ObligationStatus::Proven
    );
}

#[test]
fn trust_entries_are_scoped_audited_and_never_runtime_instructions() {
    let mut raw = raw_identity_unit();
    let expected_origin = origin(&raw);
    let runtime_before = raw.runtime().stable_dump();
    add_trusted_bound_and_matching_prove(&mut raw);
    let validated = raw.clone().into_validated().expect("entry trust validates");
    assert_eq!(validated.runtime().stable_dump(), runtime_before);
    assert!(!validated.runtime().stable_dump().contains("assume"));
    assert!(
        validated
            .stable_dump()
            .contains("trust trust0 scope fn0:entry policy entry-point-assumption clause0")
    );

    let verification = verify_program(
        &validated.resolve().expect("verification input resolves"),
        CfgAnalysisConfig::default(),
    )
    .expect("registered trust fact participates in proof");
    assert!(verification.is_memory_checked_core0());
    assert_eq!(
        verification.functions()[&VirFunctionId::new(0)].proofs()[0].status(),
        ObligationStatus::Proven
    );
    assert_eq!(verification.trust_report().entries().len(), 1);
    let reported = verification.trust_report().entries()[0];
    assert_eq!(reported.id(), VirTrustEntryId::new(0));
    assert_eq!(
        reported.scope(),
        VirTrustScope::FunctionEntry {
            function: VirFunctionId::new(0)
        }
    );
    assert_eq!(reported.policy(), VirTrustPolicyKind::EntryPointAssumption);
    assert_eq!(reported.clause(), VirSpecClauseId::new(0));
    assert_eq!(reported.origin(), expected_origin);
    assert_eq!(reported.source_span(), span());
    assert_eq!(
        reported.finding().site(),
        VerifierFindingSite::Spec {
            location: VirSpecLocation::FunctionEntry {
                function: VirFunctionId::new(0),
            },
            entity: VerifierSpecEntity::TrustEntry(VirTrustEntryId::new(0)),
            occurrence: None,
        }
    );

    let mut denied_policy = raw.clone();
    denied_policy.specs.trust_entries_mut()[0].policy = VirTrustPolicyKind::ForeignContract;
    assert!(matches!(
        denied_policy
            .into_validated()
            .expect_err("reserved trust policy remains denied")
            .kind(),
        VirValidationErrorKind::TrustPolicyDenied(_)
    ));

    let mut wrong_scope = raw.clone();
    wrong_scope.specs.trust_entries_mut()[0].scope = VirTrustScope::FunctionResult {
        function: VirFunctionId::new(0),
    };
    assert!(matches!(
        wrong_scope
            .into_validated()
            .expect_err("entry policy cannot escape to a result scope")
            .kind(),
        VirValidationErrorKind::TrustPolicyDenied(_)
    ));

    let mut wrong_origin = raw;
    wrong_origin.specs.trust_entries_mut()[0].origin = nera::VirOriginId::new(999);
    assert!(matches!(
        wrong_origin
            .into_validated()
            .expect_err("trust origin must match its typed clause")
            .kind(),
        VirValidationErrorKind::InvalidTrustEntry(_)
    ));
}

#[test]
fn logical_contract_is_checked_and_orphan_ownership_is_rejected() {
    let mut unit = raw_identity_unit();
    add_result_contract_clause(&mut unit);
    let validated = unit
        .into_validated()
        .expect("logical result clause validates");

    assert!(
        !verify_program(
            &validated.resolve().expect("verification input resolves"),
            CfgAnalysisConfig::default()
        )
        .unwrap()
        .is_memory_checked_core0()
    );

    let mut orphan = validated.as_unit().clone();
    orphan
        .specs
        .contract_mut(VirContractId::new(0))
        .expect("contract")
        .clauses
        .clear();
    assert!(matches!(
        orphan
            .into_validated()
            .expect_err("global clauses require an owner backlink")
            .kind(),
        VirValidationErrorKind::InvalidSpecClauseOwner(_)
    ));
}

#[test]
fn entry_logic_cannot_borrow_a_legacy_scalar_assumption() {
    let mut raw = raw_identity_unit();
    add_result_contract_clause(&mut raw);
    let binder = raw
        .specs
        .contract(VirContractId::new(0))
        .unwrap()
        .binder(VirContractPosition::Requires, 0)
        .unwrap();
    let origin = origin(&raw);
    raw.specs
        .add_contract_clause(
            VirContractId::new(0),
            VirContractPosition::Requires,
            VirSpecClauseOrigin::Explicit { origin },
            VirSpecClauseKind::U64Range {
                binder,
                lower: 10,
                upper: 10,
            },
        )
        .unwrap();
    let unit = raw.into_validated().unwrap();
    let report = verify_program(&unit.resolve().unwrap(), Default::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .diagnostics()
            .iter()
            .any(|d| d.message().contains("whole-program entry"))
    );
}

#[test]
fn term_typing_order_snapshot_location_and_depth_are_checked() {
    let mut inferred_prove = raw_identity_unit();
    add_entry_prove(&mut inferred_prove);
    let inferred_origin = origin(&inferred_prove);
    inferred_prove.specs.clauses_mut()[0].origin = VirSpecClauseOrigin::InferredType {
        origin: inferred_origin,
    };
    assert!(matches!(
        inferred_prove
            .into_validated()
            .expect_err("only resource clauses may be inferred from runtime types")
            .kind(),
        VirValidationErrorKind::InvalidInferredTypeClause(_)
    ));

    let mut wrong_type = raw_identity_unit();
    add_entry_prove(&mut wrong_type);
    wrong_type.specs.terms_mut()[7].ty = VirSpecType::U64;
    assert!(matches!(
        wrong_type
            .into_validated()
            .expect_err("comparison result must be bool")
            .kind(),
        VirValidationErrorKind::InvalidSpecTerm(_)
    ));

    let mut forward_reference = raw_identity_unit();
    add_entry_prove(&mut forward_reference);
    forward_reference.specs.terms_mut()[0].ty = VirSpecType::Bool;
    forward_reference.specs.terms_mut()[0].kind = VirSpecTermKind::Not(VirSpecTermId::new(7));
    assert!(matches!(
        forward_reference
            .into_validated()
            .expect_err("terms only reference earlier same-clause terms")
            .kind(),
        VirValidationErrorKind::InvalidSpecTerm(_)
    ));

    let mut wrong_snapshot = raw_identity_unit();
    add_entry_prove(&mut wrong_snapshot);
    wrong_snapshot.specs.terms_mut()[0].kind = VirSpecTermKind::Snapshot(VirSpecSnapshot::Result {
        function: VirFunctionId::new(0),
        slot: 0,
    });
    assert!(matches!(
        wrong_snapshot
            .into_validated()
            .expect_err("result snapshots are unavailable at function entry")
            .kind(),
        VirValidationErrorKind::InvalidSpecSnapshot(_)
    ));

    let mut too_deep = raw_identity_unit();
    let origin = origin(&too_deep);
    too_deep.specs.terms_mut().push(VirSpecTerm {
        id: VirSpecTermId::new(0),
        clause: VirSpecClauseId::new(0),
        ty: VirSpecType::Bool,
        kind: VirSpecTermKind::Bool(true),
        origin,
    });
    for raw in 1..=256 {
        too_deep.specs.terms_mut().push(VirSpecTerm {
            id: VirSpecTermId::new(raw),
            clause: VirSpecClauseId::new(0),
            ty: VirSpecType::Bool,
            kind: VirSpecTermKind::Not(VirSpecTermId::new(raw - 1)),
            origin,
        });
    }
    too_deep.specs.clauses_mut().push(VirSpecClause {
        id: VirSpecClauseId::new(0),
        owner: VirSpecClauseOwner::Prove(VirSpecProveId::new(0)),
        location: VirSpecLocation::FunctionEntry {
            function: VirFunctionId::new(0),
        },
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic {
            root: VirSpecTermId::new(256),
        },
    });
    too_deep.specs.proves_mut().push(VirSpecProve {
        id: VirSpecProveId::new(0),
        function: VirFunctionId::new(0),
        location: VirSpecLocation::FunctionEntry {
            function: VirFunctionId::new(0),
        },
        clause: VirSpecClauseId::new(0),
        origin,
    });
    assert!(matches!(
        too_deep
            .into_validated()
            .expect_err("pure term depth is bounded")
            .kind(),
        VirValidationErrorKind::SpecTermDepthExceeded(_)
    ));
}

#[test]
fn predicate_binder_ownership_and_gated_bodies_are_explicit() {
    let mut unit = raw_identity_unit();
    let origin = origin(&unit);
    unit.specs.predicates_mut().push(VirPredicate {
        id: VirPredicateId::new(0),
        name: "word".to_owned(),
        binders: vec![VirSpecBinderId::new(0)],
        origin,
        body: None,
    });
    unit.specs.binders_mut().push(VirSpecBinder {
        id: VirSpecBinderId::new(0),
        owner: VirSpecBinderOwner::Predicate(VirPredicateId::new(0)),
        name: "value".to_owned(),
        ty: VirSpecType::U64,
        origin,
    });
    unit.clone()
        .into_validated()
        .expect("bodyless typed predicate declaration validates");

    let mut missing_backlink = unit.clone();
    missing_backlink.specs.predicates_mut()[0].binders.clear();
    assert!(matches!(
        missing_backlink
            .into_validated()
            .expect_err("binder ownership must be bidirectional")
            .kind(),
        VirValidationErrorKind::InvalidSpecBinder(_)
    ));

    unit.specs.predicates_mut()[0].body = Some(VirSpecClauseId::new(0));
    assert!(matches!(
        unit.into_validated()
            .expect_err("predicate bodies remain gated")
            .kind(),
        VirValidationErrorKind::PredicateBodyFeatureGated(_)
    ));
}

#[test]
fn nontrivial_loop_invariants_remain_gated() {
    let mut unit = raw_identity_unit();
    let origin = origin(&unit);
    let location = VirSpecLocation::Runtime(VirLocation::BlockEntry {
        function: VirFunctionId::new(0),
        block: VirBlockId::new(0),
    });
    unit.specs.terms_mut().push(VirSpecTerm {
        id: VirSpecTermId::new(0),
        clause: VirSpecClauseId::new(0),
        ty: VirSpecType::Bool,
        kind: VirSpecTermKind::Bool(true),
        origin,
    });
    unit.specs.clauses_mut().push(VirSpecClause {
        id: VirSpecClauseId::new(0),
        owner: VirSpecClauseOwner::LoopInvariant(VirSpecLoopInvariantId::new(0)),
        location,
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic {
            root: VirSpecTermId::new(0),
        },
    });
    unit.specs.loop_invariants_mut().push(VirSpecLoopInvariant {
        id: VirSpecLoopInvariantId::new(0),
        function: VirFunctionId::new(0),
        location,
        clause: VirSpecClauseId::new(0),
        origin,
    });

    assert!(matches!(
        unit.into_validated()
            .expect_err("nontrivial invariants are represented but gated")
            .kind(),
        VirValidationErrorKind::LoopInvariantFeatureGated(_)
    ));
}
