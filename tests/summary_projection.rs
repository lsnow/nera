use nera::verifier::summary::*;
use nera::{
    CfgAnalysisConfig, FrontendStatus, ObligationStatus, SourceFile, VirFunctionId, analyze,
    verify_program,
};

fn with_report(
    source: &str,
    check: impl FnOnce(&nera::ResolvedVirUnit<'_>, &nera::ProgramVerification),
) {
    let output = analyze(&SourceFile::from_text("summary.nera", source));
    assert_eq!(
        output.status(),
        FrontendStatus::AcceptedProposal,
        "{output:?}"
    );
    let unit = output.vir().unwrap();
    let resolved = unit.resolve().unwrap();
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    check(&resolved, &report);
}
fn named<'a>(
    unit: &nera::ResolvedVirUnit<'_>,
    report: &'a nera::ProgramVerification,
    name: &str,
) -> &'a nera::FunctionVerification {
    let id = unit
        .runtime()
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap()
        .id;
    &report.functions()[&id]
}
fn alternatives(summary: &FunctionSummary) -> &[ReturnAlternative] {
    let Knowledge::Known(alternatives) = &summary.normal_returns else {
        panic!("missing projection")
    };
    alternatives
}

#[test]
fn real_cfg_projection_covers_all_returns_and_old_postconditions() {
    for source in [
        include_str!("../spec/cases/verify/summary-baseline.nera"),
        include_str!("../spec/cases/aggregate/owning-abi.nera"),
        include_str!("../spec/cases/verify/initialization-interfaces-owning.nera"),
        include_str!("../spec/cases/verify/borrow-calls.nera"),
        include_str!("../spec/cases/verify/provenance-flow.nera"),
    ] {
        with_report(source, |unit, report| {
            assert!(report.is_memory_checked_core0());
            for (&id, function) in report.functions() {
                let summary = function.summary();
                summary
                    .validate_structure(unit, id, CfgAnalysisConfig::default())
                    .unwrap();
                if summary.state == SummaryState::Closed {
                    assert!(
                        alternatives(summary)
                            .iter()
                            .flat_map(|a| &a.worlds)
                            .all(|w| w.effects.may_write != Knowledge::Unknown)
                    );
                }
                let worlds = alternatives(summary)
                    .iter()
                    .flat_map(|a| &a.worlds)
                    .collect::<Vec<_>>();
                assert_eq!(worlds.len(), function.cfg().returns().len());
                for world in worlds {
                    let returned = &function.cfg().returns()[world.return_evidence];
                    assert_eq!(returned.finding().source_span(), returned.source_span());
                    assert_eq!(world.values.len(), returned.values().len());
                }
                assert_eq!(
                    summary
                        .faults
                        .requirements
                        .iter()
                        .filter(|e| e.kind == EvidenceKind::Postcondition)
                        .count(),
                    function.postconditions().len()
                );
                let dump = summary.stable_dump();
                assert_eq!(dump, summary.stable_dump());
                // Audit observations are source-local; exported interface
                // coordinates, resources and effects must not leak local IDs.
                let interface = format!(
                    "{:?}",
                    (
                        &summary.inputs,
                        &summary.input_resources,
                        &summary.normal_returns,
                        &summary.effects
                    )
                );
                for local_id in [
                    "VirValueId",
                    "VirBlockId",
                    "AbstractAllocationId",
                    "VirAllocationSite",
                    "ContractInstance",
                    "VirLoanId",
                ] {
                    assert!(!interface.contains(local_id), "leaked {local_id}");
                }
            }
        });
    }
}

#[test]
fn guards_and_results_survive_parameter_renaming() {
    let mut observations = Vec::new();
    for parameter in ["flag", "renamed"] {
        let source = format!(
            "fn main()->u64 {{ return choose(true); }} fn choose({parameter}:bool)->u64 {{ if {parameter} {{ return 10; }} return 20; }}"
        );
        with_report(&source, |unit, report| {
            let summary = named(unit, report, "choose").summary();
            let returns = alternatives(summary);
            assert_eq!(returns.len(), 2);
            for alternative in returns {
                assert_eq!(alternative.guard.len(), 1);
                let SummaryGuard::Boolean {
                    parameter: 0,
                    expected,
                } = alternative.guard[0]
                else {
                    panic!("wrong interface guard")
                };
                let SummaryValue::Word { interval, .. } = alternative.worlds[0].values[0].value
                else {
                    panic!()
                };
                assert_eq!(interval.exact_value(), Some(if expected { 10 } else { 20 }));
            }
            observations.push((summary.inputs.clone(), summary.normal_returns.clone()));
        });
    }
    assert_eq!(observations[0], observations[1]);
}

#[test]
fn local_guard_loss_merges_whole_worlds_without_dropping_a_return() {
    with_report(
        "fn main()->u64 { let flag=true; return choose(&flag); }
        fn choose(p:&bool)->u64 { if *p { return 10; } return 20; }",
        |unit, report| {
            let summary = named(unit, report, "choose").summary();
            assert!(matches!(&summary.state, SummaryState::Closed));
            let returns = alternatives(summary);
            assert_eq!(returns.len(), 1);
            assert!(returns[0].guard.is_empty());
            assert_eq!(returns[0].worlds.len(), 2);
            let values = returns[0]
                .worlds
                .iter()
                .map(|w| match w.values[0].value {
                    SummaryValue::Word { interval, .. } => interval.exact_value().unwrap(),
                    _ => panic!(),
                })
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(values, [10, 20].into());
        },
    );
}

#[test]
fn fresh_escape_and_nested_payloads_are_interface_existentials() {
    with_report(
        include_str!("../spec/cases/verify/summary-baseline.nera"),
        |unit, report| {
            let summary = named(unit, report, "make").summary();
            let world = &alternatives(summary)[0].worlds[0];
            assert!(
                world
                    .resources
                    .iter()
                    .any(|r| matches!(r.name, ResourceName::Fresh(_))
                        && r.storage == ResourceStorage::Heap)
            );
            // Indirect return storage is a physical signature input (sret), not a
            // newly allocated heap object. Only its nested owner is fresh.
            assert!(
                world
                    .resources
                    .iter()
                    .any(|r| matches!(r.name, ResourceName::Input { .. }))
            );
            assert!(
                world
                    .resources
                    .iter()
                    .flat_map(|r| &r.payloads)
                    .any(|p| matches!(p.state, SummaryMovePath::Available { .. }))
            );
            assert!(
                world
                    .resources
                    .iter()
                    .all(|r| !r.initialization.initialized().is_empty())
            );
        },
    );
}

#[test]
fn faults_and_unknowns_cannot_be_promoted_or_erased() {
    with_report(
        "fn main()->u64 { bad(); return 42; } fn bad() { let p=alloc<u64>(1); let x=*p; free(p); return; }",
        |unit, report| {
            assert!(!report.is_memory_checked_core0());
            let summary = named(unit, report, "bad").summary();
            assert!(matches!(summary.state, SummaryState::Unknown(_)));
            assert!(
                summary
                    .faults
                    .requirements
                    .iter()
                    .any(|r| r.status == ObligationStatus::Refuted)
            );
            let mut changed = summary.clone();
            changed.state = SummaryState::Candidate;
            assert!(
                changed
                    .validate_structure(
                        unit,
                        named(unit, report, "bad").cfg().function(),
                        Default::default()
                    )
                    .is_err()
            );
            changed = summary.clone();
            changed.faults.requirements.clear();
            assert!(
                changed
                    .validate_structure(
                        unit,
                        named(unit, report, "bad").cfg().function(),
                        Default::default()
                    )
                    .is_err()
            );
        },
    );
}

#[test]
fn structural_mutations_and_cross_context_reuse_are_rejected() {
    with_report(
        "fn main()->u64 { return choose(true); } fn choose(flag:bool)->u64 { if flag { return 10; } return 20; }",
        |unit, report| {
            let function = named(unit, report, "choose");
            let summary = function.summary();
            let id = function.cfg().function();
            let reject = |changed: FunctionSummary| {
                assert!(
                    changed
                        .validate_structure(unit, id, Default::default())
                        .is_err(),
                    "accepted mutation"
                )
            };
            let mut changed = summary.clone();
            changed.version += 1;
            reject(changed);
            let mut changed = summary.clone();
            changed.state = SummaryState::Candidate;
            reject(changed);
            let mut changed = summary.clone();
            changed.effects.may_write = Knowledge::Unknown;
            reject(changed);
            let mut changed = summary.clone();
            changed.parameters.clear();
            reject(changed);
            let mut changed = summary.clone();
            changed.inputs[0].coordinate.epoch = ValueEpoch::Post;
            reject(changed);
            let mut changed = summary.clone();
            changed.normal_returns = Knowledge::Unknown;
            reject(changed);
            let mut changed = summary.clone();
            if let Knowledge::Known(returns) = &mut changed.normal_returns {
                returns[0].guard = vec![SummaryGuard::Boolean {
                    parameter: 999,
                    expected: true,
                }];
            }
            reject(changed);
            let mut changed = summary.clone();
            if let Knowledge::Known(returns) = &mut changed.normal_returns {
                returns[0].worlds[0].return_evidence = 999;
            }
            reject(changed);
            let mut changed = summary.clone();
            if let Knowledge::Known(returns) = &mut changed.normal_returns {
                returns.pop();
            }
            reject(changed);
            let mut changed = summary.clone();
            if let Knowledge::Known(returns) = &mut changed.normal_returns {
                returns[0].worlds[0].values[0].coordinate.coordinate = ValueCoordinate::Result(99);
            }
            reject(changed);
            assert!(
                summary
                    .validate_structure(
                        unit,
                        id,
                        CfgAnalysisConfig {
                            max_guard_atoms_per_case: 0,
                            ..Default::default()
                        }
                    )
                    .is_err()
            );
            assert!(
                summary
                    .validate_structure(unit, VirFunctionId::new(999), Default::default())
                    .is_err()
            );
            with_report("fn main()->u64 { return 999; }", |other, _| {
                assert!(
                    summary
                        .validate_structure(other, id, Default::default())
                        .is_err()
                );
            });
        },
    );
}

#[test]
fn resource_mapping_path_and_payload_mutations_are_rejected() {
    with_report(
        include_str!("../spec/cases/verify/summary-baseline.nera"),
        |unit, report| {
            let function = named(unit, report, "make");
            let reject = |edit: fn(&mut ReturnWorld)| {
                let mut summary = function.summary().clone();
                let Knowledge::Known(returns) = &mut summary.normal_returns else {
                    panic!()
                };
                edit(&mut returns[0].worlds[0]);
                assert!(
                    summary
                        .validate_structure(unit, function.cfg().function(), Default::default())
                        .is_err()
                );
            };
            reject(|w| {
                w.resources.pop();
            });
            reject(|w| {
                w.resources.push(w.resources[0].clone());
            });
            reject(|w| {
                payload_pointer(w).resource = Knowledge::Known(ResourceName::Fresh(999));
            });
            reject(|w| {
                payload_pointer(w).access = Some(nera::VirMemoryAccess::new(
                    nera::VirTypeId::new(999),
                    nera::VirLayoutId::new(999),
                ));
            });
            reject(|w| {
                let resource = w
                    .resources
                    .iter_mut()
                    .find(|r| !r.payloads.is_empty())
                    .unwrap();
                resource.payloads[0].offset = u64::MAX;
            });
            reject(|w| {
                payload_pointer(w).object_path.as_mut().unwrap().steps.push(
                    nera::VirObjectPathSegment::Field(nera::VirFieldId::new(999)),
                );
            });
        },
    );
}

fn payload_pointer(world: &mut ReturnWorld) -> &mut SummaryPointer {
    world
        .resources
        .iter_mut()
        .flat_map(|r| &mut r.payloads)
        .find_map(|p| match &mut p.state {
            SummaryMovePath::Available { pointer, .. } => Some(pointer.as_mut()),
            _ => None,
        })
        .unwrap()
}

#[test]
fn block_argument_guards_are_rewritten_to_signature_slots() {
    use nera::*;
    let span = ByteSpan::new(0, 1).unwrap();
    let value = |id, ty| VirValue {
        id: VirValueId::new(id),
        ty,
    };
    let target = |block, arguments| VirBlockTarget {
        block: VirBlockId::new(block),
        arguments,
    };
    let block = |id, parameters, instructions: Vec<VirInstruction>, terminator| VirBasicBlock {
        id: VirBlockId::new(id),
        parameters,
        source_span: span,
        instructions: instructions
            .into_iter()
            .map(|instruction| SpannedVirInstruction {
                instruction,
                source_span: span,
            })
            .collect(),
        terminator: SpannedVirTerminator {
            terminator,
            source_span: span,
        },
    };
    let function = VirFunction {
        id: VirFunctionId::new(0),
        name: "block_args".into(),
        contract: VirContractId::new(0),
        signature: VirSignature {
            parameters: vec![VirType::Bool],
            results: vec![VirType::U64],
        },
        entry: VirBlockId::new(0),
        source_span: span,
        blocks: vec![
            block(
                0,
                vec![value(50, VirType::Bool)],
                vec![],
                VirTerminator::Jump {
                    target: target(1, vec![VirValueId::new(50)]),
                },
            ),
            block(
                1,
                vec![value(99, VirType::Bool)],
                vec![],
                VirTerminator::Branch {
                    condition: VirValueId::new(99),
                    then_target: target(2, vec![VirValueId::new(99)]),
                    else_target: target(3, vec![VirValueId::new(99)]),
                },
            ),
            block(
                2,
                vec![value(103, VirType::Bool)],
                vec![VirInstruction::Constant {
                    result: value(101, VirType::U64),
                    value: VirConstant::U64(10),
                }],
                VirTerminator::Return {
                    values: vec![VirValueId::new(101)],
                },
            ),
            block(
                3,
                vec![value(104, VirType::Bool)],
                vec![VirInstruction::Constant {
                    result: value(102, VirType::U64),
                    value: VirConstant::U64(20),
                }],
                VirTerminator::Return {
                    values: vec![VirValueId::new(102)],
                },
            ),
        ],
    };
    let unit = VirUnit::from_runtime(VirMemorySchema::core_u64(), function.id, vec![function])
        .into_validated()
        .unwrap();
    let resolved = unit.resolve().unwrap();
    let report = verify_program(&resolved, Default::default()).unwrap();
    let summary = report.functions()[&VirFunctionId::new(0)].summary();
    assert_eq!(alternatives(summary).len(), 2);
    for alternative in alternatives(summary) {
        assert!(matches!(
            alternative.guard.as_slice(),
            [SummaryGuard::Boolean { parameter: 0, .. }]
        ));
    }
    assert!(!summary.stable_dump().contains("VirValueId"));
}
