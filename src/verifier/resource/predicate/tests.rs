use super::*;
use crate::verifier::transfer_instruction;
use crate::{ByteSpan, SpannedVirInstruction, VirInstruction, VirType, VirValue};
mod boolean_consequences;
mod call_observations;
mod fields;
mod join_abstraction;
mod join_boolean_expressions;
mod join_captures;
mod join_coordinates;
mod join_dependent_coordinates;
mod join_parameters;
mod joins;
mod loop_calls;
mod loop_expressions;
mod loop_parameters;
mod loop_writes;
mod loops;
mod prefix_expressions;
mod prefix_sources;

fn binding(base: u32) -> PredicateBinding {
    PredicateBinding {
        pointer: VirValueId::new(base),
        permission: VirValueId::new(base + 1),
    }
}
// The internal call calculus transports held resources, not SSA carriers.
// Open fresh outputs through its real transfer, then label that opening for
// the unit-level logical query API. This does not install a resource or fact.
fn open_internal_named(
    input: &ResourceState,
    definition: &PredicateDefinition,
    holder: PredicateHolder,
    output: PredicateBinding,
    action: u32,
) -> ResourceState {
    let evidence = transfer_predicate(
        input,
        definition,
        definition.module(),
        &PredicateEffect::Unfold {
            holder,
            outputs: vec![output],
        },
    )
    .unwrap();
    check_predicate_evidence(input, &evidence).unwrap();
    let mut opened = evidence.output;
    opened.predicates.get_mut(&holder).unwrap().opening_action = Some(action);
    opened
}

fn definition() -> PredicateDefinition {
    PredicateDefinition::new(
        VirPredicateId::new(0),
        7,
        vec![PredicateResourceShape {
            size_bytes: 16,
            initialized: vec![ByteRange::new(0, 8).unwrap()],
        }],
    )
    .unwrap()
    .with_scalar_constraints(vec![PredicateScalarConstraint {
        access: VirMemoryAccess::core_u64(),
        resource: 0,
        offset_bytes: 0,
        lower: 0,
        upper: 8,
    }])
    .unwrap()
}
fn state() -> ResourceState {
    let id = AbstractAllocationId::new(0);
    let mut a = AbstractAllocation::new(VirRegionId::new(0), 16, 8).unwrap();
    let cell = ByteRange::new(0, 8).unwrap();
    a.mark_initialized(cell).unwrap();
    a.mark_valid(cell).unwrap();
    a.record_scalar_content(
        cell,
        VirMemoryAccess::core_u64(),
        AbstractValue::U64(U64Interval::exact(0)),
    );
    let mut s = ResourceState::new();
    s.define_allocation(id, a).unwrap();
    s.define_value(
        binding(0).pointer,
        AbstractValue::Pointer(
            AbstractPointer::new(
                AbstractProvenance::Known(id),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            )
            .with_memory_access(Some(VirMemoryAccess::core_u64())),
        ),
    )
    .unwrap();
    s.define_value(
        binding(0).permission,
        AbstractValue::Permission(AbstractPermission::new(
            AbstractProvenance::Known(id),
            AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
            AccessPermission::Write,
            FreeCapability::Yes,
        )),
    )
    .unwrap();
    s
}
fn fold(s: &ResourceState, holder: u32, base: u32) -> Result<PredicateEvidence, PredicateError> {
    transfer_predicate(
        s,
        &definition(),
        7,
        &PredicateEffect::Fold {
            holder: PredicateHolder(holder),
            bindings: vec![binding(base)],
        },
    )
}
fn unfold(s: &ResourceState, holder: u32, base: u32) -> Result<PredicateEvidence, PredicateError> {
    transfer_predicate(
        s,
        &definition(),
        7,
        &PredicateEffect::Unfold {
            holder: PredicateHolder(holder),
            outputs: vec![binding(base)],
        },
    )
}
fn instruction(s: &ResourceState, instruction: VirInstruction) -> crate::InstructionTransfer {
    transfer_instruction(
        s,
        &SpannedVirInstruction {
            instruction,
            source_span: ByteSpan::new(0, 1).unwrap(),
        },
    )
    .unwrap()
}

#[test]
fn fold_seals_real_permission_unfold_restores_once_and_free_still_executes() {
    let input = state();
    let evidence = fold(&input, 0, 0).unwrap();
    check_predicate_evidence(&input, &evidence).unwrap();
    let closed = evidence.output;
    assert!(
        closed
            .check_predicate_boundary(&[PredicateHolder(0)])
            .is_ok()
    );
    assert_eq!(
        closed.check_predicate_boundary(&[]),
        Err(PredicateError::OutstandingCleanup)
    );
    assert!(
        !instruction(
            &closed,
            VirInstruction::Load {
                result: VirValue {
                    id: VirValueId::new(8),
                    ty: VirType::U64
                },
                pointer: binding(0).pointer,
                permission: binding(0).permission,
                access: VirMemoryAccess::core_u64(),
            }
        )
        .all_obligations_proven()
    );
    assert!(
        !instruction(
            &closed,
            VirInstruction::Free {
                pointer: binding(0).pointer,
                permission: binding(0).permission,
            }
        )
        .all_obligations_proven()
    );
    assert_eq!(fold(&closed, 0, 0), Err(PredicateError::AlreadyFolded));
    let opened = unfold(&closed, 0, 10).unwrap().output;
    assert_eq!(unfold(&opened, 0, 20), Err(PredicateError::AlreadyUnfolded));
    assert_eq!(
        opened.check_predicate_boundary(&[PredicateHolder(0)]),
        Err(PredicateError::OpenBoundary)
    );
    let finish = PredicateEffect::Finish {
        holder: PredicateHolder(0),
    };
    assert_eq!(
        transfer_predicate(&opened, &definition(), 7, &finish),
        Err(PredicateError::OutstandingCleanup)
    );
    let freed = instruction(
        &opened,
        VirInstruction::Free {
            pointer: binding(10).pointer,
            permission: binding(10).permission,
        },
    );
    assert!(freed.all_obligations_proven(), "{:?}", freed.obligations());
    let retired = transfer_predicate(freed.state(), &definition(), 7, &finish)
        .unwrap()
        .output;
    retired.check_predicate_boundary(&[]).unwrap();
}

#[test]
fn copied_pointer_does_not_copy_holder_and_move_invalidates_source() {
    let mut s = state();
    s.define_value(VirValueId::new(4), *s.value(binding(0).pointer).unwrap())
        .unwrap();
    let closed = fold(&s, 0, 0).unwrap().output;
    assert_eq!(fold(&closed, 1, 0), Err(PredicateError::MissingAuthority));
    let moved = transfer_predicate(
        &closed,
        &definition(),
        99,
        &PredicateEffect::Move {
            source: PredicateHolder(0),
            destination: PredicateHolder(1),
        },
    )
    .unwrap()
    .output;
    assert_eq!(unfold(&moved, 0, 10), Err(PredicateError::MissingHolder));
    assert!(unfold(&moved, 1, 10).is_ok());
    assert_eq!(
        transfer_predicate(
            &moved,
            &definition(),
            7,
            &PredicateEffect::Move {
                source: PredicateHolder(1),
                destination: PredicateHolder(1),
            }
        ),
        Err(PredicateError::HolderOccupied)
    );
}

#[test]
fn branch_join_widen_and_guard_collapse_cannot_discard_a_holder() {
    let input = state();
    let closed = fold(&input, 0, 0).unwrap().output;
    let opened = unfold(&closed, 0, 10).unwrap().output;
    assert_eq!(
        closed.join(&input),
        Err(ResourceJoinError::PredicateStateMismatch)
    );
    assert_eq!(
        closed.join(&opened),
        Err(ResourceJoinError::PredicateStateMismatch)
    );
    assert_eq!(
        closed.widen(&opened),
        Err(ResourceJoinError::PredicateStateMismatch)
    );
    assert_eq!(closed.join(&closed).unwrap(), closed);
    assert_eq!(closed.join(&ResourceState::unreachable()).unwrap(), closed);
    let projected = closed.project_cfg_edge(&[]);
    let mut expected = closed.predicates.clone();
    expected.get_mut(&PredicateHolder(0)).unwrap().resources[0].carrier = None;
    assert_eq!(projected.predicate_instances(), &expected);
    assert_eq!(
        projected.check_predicate_boundary(&[]),
        Err(PredicateError::OutstandingCleanup)
    );
    let mut loop_state = ResourceState::new();
    assert!(loop_state.inherit_loop_resources(&closed, &BTreeSet::new()));
    assert_eq!(loop_state.predicates, closed.predicates);
    let mut rejected_frame = ResourceState::new();
    let allocation = closed.predicates[&PredicateHolder(0)].resources[0].allocation;
    assert!(!rejected_frame.inherit_loop_resources(&closed, &BTreeSet::from([allocation])));
    assert_eq!(rejected_frame, ResourceState::new());
}

#[test]
fn invariant_must_be_reestablished_from_real_memory_and_mutated_evidence_fails() {
    let input = state();
    let mut evidence = fold(&input, 0, 0).unwrap();
    evidence.output.predicates.clear();
    assert_eq!(
        check_predicate_evidence(&input, &evidence),
        Err(PredicateError::InvalidEvidence)
    );
    let closed = fold(&input, 0, 0).unwrap().output;
    let mut opened = unfold(&closed, 0, 10).unwrap().output;
    opened
        .define_value(
            VirValueId::new(20),
            AbstractValue::U64(U64Interval::exact(9)),
        )
        .unwrap();
    let broken = instruction(
        &opened,
        VirInstruction::Store {
            pointer: binding(10).pointer,
            permission: binding(10).permission,
            value: VirValueId::new(20),
            access: VirMemoryAccess::core_u64(),
        },
    );
    assert!(broken.all_obligations_proven());
    assert_eq!(
        fold(broken.state(), 0, 10),
        Err(PredicateError::UnprovedRepresentation)
    );
    assert_eq!(
        broken
            .state()
            .check_predicate_boundary(&[PredicateHolder(0)]),
        Err(PredicateError::OpenBoundary)
    );
    assert!(fold(&opened, 0, 10).is_ok());
}

#[test]
fn module_identity_and_definition_are_checked_on_every_open() {
    let closed = fold(&state(), 0, 0).unwrap().output;
    let effect = PredicateEffect::Unfold {
        holder: PredicateHolder(0),
        outputs: vec![binding(10)],
    };
    assert_eq!(
        transfer_predicate(&closed, &definition(), 8, &effect),
        Err(PredicateError::PrivateRepresentation)
    );
    let different = PredicateDefinition::new(
        VirPredicateId::new(1),
        7,
        vec![PredicateResourceShape {
            size_bytes: 16,
            initialized: vec![],
        }],
    )
    .unwrap();
    assert_eq!(
        transfer_predicate(&closed, &different, 7, &effect),
        Err(PredicateError::WrongDeclaration)
    );
    assert_eq!(unfold(&closed, 0, 0), Err(PredicateError::HolderOccupied));
}

#[test]
fn initialization_aliases_and_active_loans_cannot_be_hidden_by_fold() {
    let mut s = state();
    s.allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .mark_uninitialized(ByteRange::new(0, 8).unwrap())
        .unwrap();
    assert_eq!(fold(&s, 0, 0), Err(PredicateError::UnprovedRepresentation));
    let mut s = state();
    s.define_value(VirValueId::new(8), *s.value(binding(0).permission).unwrap())
        .unwrap();
    assert_eq!(fold(&s, 0, 0), Err(PredicateError::AliasedAuthority));
    let mut s = state();
    s.define_loan(
        VirLoanId::new(0),
        AbstractLoan::new(
            AbstractProvenance::Known(AbstractAllocationId::new(0)),
            ByteRange::new(0, 8).unwrap(),
            VirLoanKind::Shared,
            VirBorrowRegionId::new(0),
            None,
            LoanActivity::Active,
        ),
    )
    .unwrap();
    assert_eq!(fold(&s, 0, 0), Err(PredicateError::Borrowed));
    let mut s = fold(&state(), 0, 0).unwrap().output;
    s.define_loan(
        VirLoanId::new(0),
        AbstractLoan::new(
            AbstractProvenance::Known(AbstractAllocationId::new(0)),
            ByteRange::new(0, 8).unwrap(),
            VirLoanKind::Shared,
            VirBorrowRegionId::new(0),
            None,
            LoanActivity::Active,
        ),
    )
    .unwrap();
    assert_eq!(unfold(&s, 0, 10), Err(PredicateError::Borrowed));
}

#[test]
fn failed_unfold_is_atomic_and_witness_identity_prevents_allocation_reuse() {
    let mut closed = fold(&state(), 0, 0).unwrap().output;
    let before = closed.clone();
    let effect = PredicateEffect::Unfold {
        holder: PredicateHolder(0),
        outputs: vec![PredicateBinding {
            pointer: VirValueId::new(10),
            permission: VirValueId::new(10),
        }],
    };
    assert_eq!(
        transfer_predicate(&closed, &definition(), 7, &effect),
        Err(PredicateError::HolderOccupied)
    );
    assert_eq!(closed, before);
    let id = AbstractAllocationId::new(0);
    closed
        .allocation_mut(id)
        .unwrap()
        .set_liveness(LivenessState::Dead);
    assert_eq!(
        closed.introduce_allocation_instance(
            id,
            AbstractAllocation::new(VirRegionId::new(0), 16, 8).unwrap()
        ),
        Err(ResourceStateDefinitionError::AllocationInstanceStillReferenced(id))
    );
}

#[test]
fn declarations_and_effects_have_hard_budgets_and_no_implicit_axioms() {
    assert_eq!(
        PredicateDefinition::new(VirPredicateId::new(0), 0, vec![]),
        Err(PredicateError::InvalidDefinition)
    );
    assert_eq!(
        PredicateDefinition::new(
            VirPredicateId::new(0),
            0,
            vec![PredicateResourceShape {
                size_bytes: 8,
                initialized: vec![ByteRange::new(0, 16).unwrap()],
            }]
        ),
        Err(PredicateError::InvalidDefinition)
    );
    let input = ResourceState::new();
    assert_eq!(fold(&input, 0, 0), Err(PredicateError::InvalidBinding));
    assert_eq!(unfold(&input, 0, 10), Err(PredicateError::MissingHolder));
    let unreachable = ResourceState::unreachable();
    assert_eq!(fold(&unreachable, 0, 0).unwrap().output, unreachable);
}

#[test]
fn opaque_call_maps_the_holder_and_preserves_the_callers_frame() {
    let mut caller = fold(&state(), 0, 0).unwrap().output;
    caller
        .define_value(
            VirValueId::new(90),
            AbstractValue::U64(U64Interval::exact(42)),
        )
        .unwrap();
    let mapping = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(7),
    };
    let (frame, callee) = enter_predicate_call(&caller, &[mapping]).unwrap();
    assert_eq!(callee.predicate_instances().len(), 1);
    assert!(callee.values().is_empty());
    let mut opened = unfold(&callee, 7, 10).unwrap().output;
    opened
        .define_value(
            VirValueId::new(20),
            AbstractValue::U64(U64Interval::exact(5)),
        )
        .unwrap();
    let updated = instruction(
        &opened,
        VirInstruction::Store {
            pointer: binding(10).pointer,
            permission: binding(10).permission,
            value: VirValueId::new(20),
            access: VirMemoryAccess::core_u64(),
        },
    );
    assert!(updated.all_obligations_proven());
    let closed = fold(updated.state(), 7, 10).unwrap().output;
    let returned = frame
        .resume(
            &closed,
            &[PredicateCallBinding {
                caller: PredicateHolder(1),
                callee: PredicateHolder(7),
            }],
        )
        .unwrap();
    assert!(
        !returned
            .predicate_instances()
            .contains_key(&PredicateHolder(0))
    );
    assert_eq!(
        returned.value(VirValueId::new(90)),
        caller.value(VirValueId::new(90))
    );
    assert!(
        returned
            .allocation(AbstractAllocationId::new(0))
            .unwrap()
            .scalar_content(ByteRange::new(0, 8).unwrap(), VirMemoryAccess::core_u64())
            == Some(AbstractValue::U64(U64Interval::exact(5)))
    );
    assert!(unfold(&returned, 1, 30).is_ok());
}

#[test]
fn call_mapping_rejects_duplicates_open_returns_and_missing_cleanup() {
    let caller = fold(&state(), 0, 0).unwrap().output;
    let mapping = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(7),
    };
    assert!(matches!(
        enter_predicate_call(&caller, &[mapping, mapping]),
        Err(PredicateError::AliasedAuthority)
    ));
    let (frame, callee) = enter_predicate_call(&caller, &[mapping]).unwrap();
    let opened = unfold(&callee, 7, 10).unwrap().output;
    assert!(matches!(
        enter_predicate_call(&opened, &[]),
        Err(PredicateError::OpenBoundary)
    ));
    assert_eq!(
        frame.resume(&opened, &[mapping]),
        Err(PredicateError::OpenBoundary)
    );
    let (frame, callee) = enter_predicate_call(&caller, &[mapping]).unwrap();
    assert_eq!(
        frame.resume(&callee, &[]),
        Err(PredicateError::OutstandingCleanup)
    );
    let (frame, callee) = enter_predicate_call(&caller, &[mapping]).unwrap();
    let opened = unfold(&callee, 7, 10).unwrap().output;
    let freed = instruction(
        &opened,
        VirInstruction::Free {
            pointer: binding(10).pointer,
            permission: binding(10).permission,
        },
    );
    assert!(freed.all_obligations_proven());
    // Actual free alone does not silently retire the predicate witness scope.
    assert_eq!(
        frame.resume(freed.state(), &[]),
        Err(PredicateError::OpenBoundary)
    );
    let (frame, _) = enter_predicate_call(&caller, &[mapping]).unwrap();
    let cleaned = transfer_predicate(
        freed.state(),
        &definition(),
        7,
        &PredicateEffect::Finish {
            holder: PredicateHolder(7),
        },
    )
    .unwrap()
    .output;
    let returned = frame.resume(&cleaned, &[]).unwrap();
    assert_eq!(
        returned
            .allocation(AbstractAllocationId::new(0))
            .unwrap()
            .liveness(),
        LivenessState::Dead
    );
    returned.check_predicate_boundary(&[]).unwrap();
}

#[test]
fn conditional_cases_retain_cleanup_and_budget_collapse_fails_closed() {
    use crate::verifier::guarded::{
        ConditionalResourceState, GuardedReduction, GuardedStateLimits,
    };
    let mut present = fold(&state(), 0, 0).unwrap().output;
    let mut absent = state();
    present.conjoin_path_fact(PathFact::boolean(VirValueId::new(40), true));
    absent.conjoin_path_fact(PathFact::boolean(VirValueId::new(40), false));
    let cases = vec![present, absent];
    let kept = ConditionalResourceState::from_cases(
        cases.clone(),
        BTreeSet::new(),
        GuardedStateLimits {
            max_cases: 2,
            max_guard_atoms: 2,
        },
        GuardedReduction::Selective,
    )
    .unwrap();
    assert_eq!(kept.cases().len(), 2);
    assert_eq!(
        kept.collapsed(),
        Err(ResourceJoinError::PredicateStateMismatch)
    );
    assert_eq!(
        ConditionalResourceState::from_cases(
            cases,
            BTreeSet::new(),
            GuardedStateLimits {
                max_cases: 1,
                max_guard_atoms: 2,
            },
            GuardedReduction::Selective
        ),
        Err(ResourceJoinError::PredicateStateMismatch)
    );
}

#[test]
fn native_cfg_exit_cannot_forget_even_a_dead_open_predicate() {
    let source =
        crate::SourceFile::from_text("predicate-exit.nera", "fn main() -> u64 { return 42; }");
    let output = crate::analyze(&source);
    let unit = output.vir().unwrap().resolve().unwrap();
    let closed = fold(&state(), 0, 0).unwrap().output;
    let opened = unfold(&closed, 0, 10).unwrap().output;
    let freed = instruction(
        &opened,
        VirInstruction::Free {
            pointer: binding(10).pointer,
            permission: binding(10).permission,
        },
    );
    let report = crate::analyze_function_cfg_with_entry(
        &unit,
        crate::VirFunctionId::new(0),
        &freed.state().project_cfg_edge(&[]),
        Default::default(),
    )
    .unwrap();
    assert!(!report.all_obligations_proven());
    assert!(report.obligations().iter().any(|o| matches!(
        o.obligation().kind(),
        crate::ResourceObligationKind::PredicateBoundaryRestored {
            function_exit: true,
            ..
        }
    )));
}

#[test]
fn instance_budget_never_drops_old_holders_or_consumes_the_new_permission() {
    let mut s = ResourceState::new();
    for n in 0..=MAX_PREDICATE_INSTANCES {
        let sample = state();
        let id = AbstractAllocationId::new(n as u32);
        let provenance = AbstractProvenance::Known(id);
        let b = binding(n as u32 * 2);
        s.define_allocation(
            id,
            sample
                .allocation(AbstractAllocationId::new(0))
                .unwrap()
                .clone(),
        )
        .unwrap();
        s.define_value(
            b.pointer,
            AbstractValue::Pointer(
                AbstractPointer::new(
                    provenance,
                    U64Interval::exact(0),
                    GuaranteedAlignment::new(8).unwrap(),
                )
                .with_memory_access(Some(VirMemoryAccess::core_u64())),
            ),
        )
        .unwrap();
        s.define_value(
            b.permission,
            AbstractValue::Permission(AbstractPermission::new(
                provenance,
                AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
                AccessPermission::Write,
                FreeCapability::Yes,
            )),
        )
        .unwrap();
        if n == MAX_PREDICATE_INSTANCES {
            let before = s.clone();
            assert_eq!(
                fold(&s, n as u32, n as u32 * 2),
                Err(PredicateError::Budget)
            );
            assert_eq!(s, before);
            assert_eq!(s.predicate_instances().len(), MAX_PREDICATE_INSTANCES);
        } else {
            s = fold(&s, n as u32, n as u32 * 2).unwrap().output;
        }
    }
}

#[test]
fn stored_linear_payloads_cannot_be_silently_sealed_or_overwritten() {
    let mut s = state();
    let Some(AbstractValue::Pointer(p)) = s.value(binding(0).pointer).copied() else {
        unreachable!()
    };
    let Some(AbstractValue::Permission(a)) = s.value(binding(0).permission).copied() else {
        unreachable!()
    };
    assert!(
        s.allocation_mut(AbstractAllocationId::new(0))
            .unwrap()
            .set_resource_payload(
                ResourcePayloadKey::new(0, VirMemoryAccess::core_u64()),
                MovePathState::available(TypedResourcePayload::new(p, a)),
            )
            .is_ok()
    );
    assert_eq!(fold(&s, 0, 0), Err(PredicateError::UnsupportedStorage));
}

#[test]
fn ordinary_call_transfer_checks_the_open_representation_boundary() {
    let source = crate::SourceFile::from_text(
        "predicate-call.nera",
        "fn main() -> u64 { return answer(); } fn answer() -> u64 { return 42; }",
    );
    let output = crate::analyze(&source);
    let unit = output.vir().unwrap().as_unit();
    let call = unit.runtime.functions[0]
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .find(|i| matches!(i.instruction, VirInstruction::Call { .. }))
        .unwrap();
    let closed = fold(&state(), 0, 0).unwrap().output;
    let open = unfold(&closed, 0, 10).unwrap().output;
    for (input, expected) in [
        (closed, crate::ObligationStatus::Proven),
        (open, crate::ObligationStatus::Refuted),
    ] {
        let result = transfer_instruction(&input.project_cfg_edge(&[]), call).unwrap();
        assert!(result.obligations().iter().any(|o| matches!(
            o.kind(),
            crate::ResourceObligationKind::PredicateBoundaryRestored {
                function_exit: false,
                ..
            }
        ) && o.status() == expected));
    }
}

fn reopen_carrier(
    s: &ResourceState,
    holder: u32,
    pointer: u32,
    permission: u32,
) -> Result<PredicateEvidence, PredicateError> {
    transfer_predicate(
        s,
        &definition(),
        7,
        &PredicateEffect::UnfoldInPlace {
            holder: PredicateHolder(holder),
            bindings: vec![PredicateBinding {
                pointer: VirValueId::new(pointer),
                permission: VirValueId::new(permission),
            }],
        },
    )
}

#[test]
fn permission_moves_preserve_sealing_and_retire_the_old_carrier() {
    let closed = fold(&state(), 0, 0).unwrap().output;
    let moved = instruction(
        &closed,
        VirInstruction::PermissionMove {
            result: VirValue {
                id: VirValueId::new(11),
                ty: VirType::Permission,
            },
            source: VirValueId::new(1),
        },
    );
    assert!(moved.all_obligations_proven());
    assert!(
        matches!(moved.state().value(VirValueId::new(11)), Some(AbstractValue::Permission(p)) if p.availability() == PermissionAvailability::Consumed)
    );
    assert!(reopen_carrier(moved.state(), 0, 0, 1).is_err());
    assert!(
        !instruction(
            moved.state(),
            VirInstruction::PermissionMove {
                result: VirValue {
                    id: VirValueId::new(12),
                    ty: VirType::Permission
                },
                source: VirValueId::new(1),
            }
        )
        .all_obligations_proven()
    );
    let mut reopened = reopen_carrier(moved.state(), 9, 0, 11).unwrap();
    check_predicate_evidence(moved.state(), &reopened).unwrap();
    assert!(!reopened.output.predicates.contains_key(&PredicateHolder(0)));
    assert!(reopened.output.predicates.contains_key(&PredicateHolder(9)));
    reopened
        .output
        .predicates
        .get_mut(&PredicateHolder(9))
        .unwrap()
        .resources[0]
        .carrier = Some(VirValueId::new(1));
    assert_eq!(
        check_predicate_evidence(moved.state(), &reopened),
        Err(PredicateError::InvalidEvidence)
    );
}

#[test]
fn cfg_renames_and_duplicate_slots_cannot_copy_a_sealed_token() {
    let closed = fold(&state(), 0, 0).unwrap().output;
    let projected = closed
        .project_cfg_case(&[
            (VirValueId::new(0), VirValueId::new(20)),
            (VirValueId::new(1), VirValueId::new(21)),
            (VirValueId::new(0), VirValueId::new(30)),
            (VirValueId::new(1), VirValueId::new(31)),
        ])
        .unwrap();
    assert!(reopen_carrier(&projected, 9, 30, 31).is_err());
    let opened = reopen_carrier(&projected, 9, 20, 21).unwrap().output;
    assert!(reopen_carrier(&opened, 10, 30, 31).is_err());
    let mut dropped = closed.project_cfg_case(&[]).unwrap();
    dropped
        .define_value(
            VirValueId::new(0),
            *closed.value(VirValueId::new(0)).unwrap(),
        )
        .unwrap();
    dropped
        .define_value(
            VirValueId::new(1),
            *closed.value(VirValueId::new(1)).unwrap(),
        )
        .unwrap();
    assert!(reopen_carrier(&dropped, 0, 0, 1).is_err());
    assert_eq!(
        dropped.check_predicate_boundary(&[]),
        Err(PredicateError::OutstandingCleanup)
    );
}

#[test]
fn internal_call_frames_do_not_reuse_ssa_carriers_across_namespaces() {
    let caller = fold(&state(), 0, 0).unwrap().output;
    let map = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(7),
    };
    let (frame, mut callee) = enter_predicate_call(&caller, &[map]).unwrap();
    for id in [0, 1] {
        callee
            .define_value(
                VirValueId::new(id),
                *caller.value(VirValueId::new(id)).unwrap(),
            )
            .unwrap();
    }
    assert!(reopen_carrier(&callee, 7, 0, 1).is_err());
    let returned = frame.resume(&callee, &[map]).unwrap();
    assert!(reopen_carrier(&returned, 0, 0, 1).is_err());
    // The internal API still explicitly binds fresh outputs to the held resource.
    assert!(unfold(&returned, 0, 10).is_ok());
}

#[test]
fn sealed_views_preserve_loans_and_recheck_representation_after_memory_effects() {
    let mut s = state();
    let id = AbstractAllocationId::new(0);
    let range = ByteRange::new(8, 16).unwrap();
    let mut def = definition();
    def.resources[0].initialized = vec![ByteRange::new(0, 16).unwrap()];
    let a = s.allocation_mut(id).unwrap();
    a.mark_initialized(range).unwrap();
    a.mark_valid(range).unwrap();
    a.record_scalar_content(
        range,
        VirMemoryAccess::core_u64(),
        AbstractValue::U64(U64Interval::exact(0)),
    );
    let loan_id = VirLoanId::new(0);
    s.define_loan(
        loan_id,
        AbstractLoan::new(
            AbstractProvenance::Known(id),
            range,
            crate::VirLoanKind::Mutable,
            crate::VirBorrowRegionId::new(0),
            None,
            LoanActivity::Active,
        )
        .with_authority(VirValueId::new(11))
        .with_footprint(Some(MemoryFootprint {
            provenance: AbstractProvenance::Known(id),
            access: VirMemoryAccess::core_u64(),
            stride_bytes: 8,
            range: AbstractByteRange::Exact(range),
            envelope: range,
        })),
    )
    .unwrap();
    s.define_value(
        VirValueId::new(10),
        AbstractValue::Pointer(
            AbstractPointer::new(
                AbstractProvenance::Known(id),
                U64Interval::exact(8),
                GuaranteedAlignment::new(8).unwrap(),
            )
            .with_memory_access(Some(VirMemoryAccess::core_u64())),
        ),
    )
    .unwrap();
    s.define_value(
        VirValueId::new(11),
        AbstractValue::Permission(
            AbstractPermission::new(
                AbstractProvenance::Known(id),
                AbstractByteRange::Exact(range),
                AccessPermission::Write,
                FreeCapability::No,
            )
            .with_authority(PermissionAuthority::Loan(loan_id)),
        ),
    )
    .unwrap();
    let effect = PredicateEffect::Fold {
        holder: PredicateHolder(0),
        bindings: vec![binding(0)],
    };
    let evidence = transfer_predicate(&s, &def, 7, &effect).unwrap();
    check_predicate_evidence(&s, &evidence).unwrap();
    let closed = evidence.output;
    assert_eq!(closed.loans, s.loans);
    assert_eq!(
        closed.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let mut nested = closed.clone();
    nested
        .loan_mut(loan_id)
        .unwrap()
        .set_activity(LoanActivity::Suspended);
    let child_id = VirLoanId::new(1);
    let child = |range| {
        AbstractLoan::new(
            AbstractProvenance::Known(id),
            range,
            crate::VirLoanKind::Mutable,
            crate::VirBorrowRegionId::new(0),
            Some(loan_id),
            LoanActivity::Active,
        )
        .with_authority(VirValueId::new(12))
        .with_footprint(Some(MemoryFootprint {
            provenance: AbstractProvenance::Known(id),
            access: VirMemoryAccess::core_u64(),
            stride_bytes: 8,
            range: AbstractByteRange::Exact(range),
            envelope: range,
        }))
    };
    nested.define_loan(child_id, child(range)).unwrap();
    let AbstractValue::Permission(parent_token) = *nested.value(VirValueId::new(11)).unwrap()
    else {
        panic!()
    };
    nested
        .define_value(
            VirValueId::new(12),
            AbstractValue::Permission(
                parent_token.with_authority(PermissionAuthority::Loan(child_id)),
            ),
        )
        .unwrap();
    assert_eq!(
        nested.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_eq!(
        nested.loan(loan_id).unwrap().activity(),
        LoanActivity::Suspended
    );
    // Preserving the representation never reopens the owner while either
    // the reserved parent range or a descendant remains borrowed.
    assert_eq!(
        transfer_predicate(
            &nested,
            &def,
            7,
            &PredicateEffect::Unfold {
                holder: PredicateHolder(0),
                outputs: vec![binding(20)],
            }
        )
        .unwrap_err(),
        PredicateError::Borrowed
    );
    let mut unknown_child = nested.clone();
    unknown_child
        .loan_mut(child_id)
        .unwrap()
        .set_activity(LoanActivity::MaybeActive);
    assert_eq!(
        unknown_child.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    // Every descendant is checked too; a malformed child cannot expose a
    // constrained field merely because its parent reserves other bytes.
    *nested.loan_mut(child_id).unwrap() = child(ByteRange::new(0, 8).unwrap());
    assert_eq!(
        nested.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    assert!(matches!(
        enter_predicate_call(
            &closed,
            &[PredicateCallBinding {
                caller: PredicateHolder(0),
                callee: PredicateHolder(1)
            }]
        ),
        Err(PredicateError::Borrowed)
    ));
    assert!(matches!(
        transfer_predicate(
            &closed,
            &def,
            7,
            &PredicateEffect::Unfold {
                holder: PredicateHolder(0),
                outputs: vec![binding(20)]
            }
        ),
        Err(PredicateError::Borrowed)
    ));

    let deinitialize = crate::SpannedVirInstruction {
        instruction: crate::VirInstruction::ObjectDeinitialize {
            pointer: VirValueId::new(10),
            permission: VirValueId::new(11),
            access: VirMemoryAccess::core_u64(),
        },
        source_span: ByteSpan::new(0, 1).unwrap(),
    };
    let transfer = transfer_instruction(&closed, &deinitialize).unwrap();
    assert!(transfer.obligations().iter().any(|o| matches!(
        o.kind(),
        crate::ResourceObligationKind::PredicateInvariantPreserved { holder: 0 }
    ) && o.status()
        == crate::ObligationStatus::Unknown));
    assert_eq!(
        transfer
            .state()
            .allocation(id)
            .unwrap()
            .initialization()
            .classify(range),
        InitializationClass::Uninitialized
    );

    // Symbolic views may use a conservative envelope for exclusion only.
    // Losing the actual range, or exposing a constrained cell, still fails.
    let mut symbolic = s.clone();
    let selected = AbstractByteRange::Symbolic {
        start: SymbolicRangeBound::constant(8),
        end: SymbolicRangeBound::new(
            AffineExpression::identity(VirValueId::new(100)),
            U64Interval::new(8, 16).unwrap(),
        ),
    };
    symbolic
        .define_value(
            VirValueId::new(100),
            AbstractValue::U64(U64Interval::new(8, 16).unwrap()),
        )
        .unwrap();
    let mut footprint = symbolic.loan(loan_id).unwrap().footprint().unwrap();
    footprint.range = selected;
    *symbolic.loan_mut(loan_id).unwrap() = symbolic
        .loan(loan_id)
        .unwrap()
        .clone()
        .with_footprint(Some(footprint));
    *symbolic.value_mut(VirValueId::new(11)).unwrap() = AbstractValue::Permission(
        AbstractPermission::new(
            AbstractProvenance::Known(id),
            selected,
            AccessPermission::Write,
            FreeCapability::No,
        )
        .with_authority(PermissionAuthority::Loan(loan_id)),
    );
    let folded = transfer_predicate(&symbolic, &def, 7, &effect).unwrap();
    check_predicate_evidence(&symbolic, &folded).unwrap();
    assert_eq!(
        folded.output.loan(loan_id).unwrap().actual_range(),
        selected
    );
    for (actual, envelope) in [
        (AbstractByteRange::Unknown, range),
        (selected, ByteRange::new(0, 16).unwrap()),
    ] {
        let mut bad = symbolic.clone();
        footprint.range = actual;
        footprint.envelope = envelope;
        *bad.loan_mut(loan_id).unwrap() = bad
            .loan(loan_id)
            .unwrap()
            .clone()
            .with_footprint(Some(footprint));
        assert_eq!(
            transfer_predicate(&bad, &def, 7, &effect),
            Err(PredicateError::Borrowed)
        );
    }

    // The same mutable authority may not cover the constrained scalar.
    def.scalar_constraints[0].offset_bytes = 8;
    assert_eq!(
        transfer_predicate(&s, &def, 7, &effect),
        Err(PredicateError::Borrowed)
    );
}

#[test]
fn borrowed_finish_observes_contents_without_ending_loans_or_creating_ownership() {
    let mut input = state();
    let id = AbstractAllocationId::new(0);
    let loan_id = VirLoanId::new(0);
    let range = ByteRange::new(0, 16).unwrap();
    let permission = AbstractPermission::new(
        AbstractProvenance::Known(id),
        AbstractByteRange::Exact(range),
        AccessPermission::Write,
        FreeCapability::No,
    )
    .with_authority(PermissionAuthority::Loan(loan_id));
    *input.value_mut(binding(0).permission).unwrap() = AbstractValue::Permission(permission);
    input
        .define_loan(
            loan_id,
            AbstractLoan::new(
                AbstractProvenance::Known(id),
                range,
                crate::VirLoanKind::Mutable,
                crate::VirBorrowRegionId::new(0),
                None,
                LoanActivity::Active,
            )
            .with_authority(binding(0).permission)
            .with_footprint(Some(MemoryFootprint {
                provenance: AbstractProvenance::Known(id),
                access: VirMemoryAccess::core_u64(),
                stride_bytes: 8,
                range: AbstractByteRange::Exact(range),
                envelope: range,
            })),
        )
        .unwrap();
    let sealed = fold(&input, 0, 0).unwrap();
    check_predicate_evidence(&input, &sealed).unwrap();
    assert_eq!(sealed.output.loans, input.loans);
    let mut exported = sealed.output.clone();
    assert_eq!(
        exported.export_predicate_parameters(
            &definition(),
            &[(VirLoanId::new(1), binding(0).permission)]
        ),
        Err(PredicateError::MissingHolder)
    );
    assert_eq!(exported, sealed.output);
    exported
        .export_predicate_parameters(&definition(), &[(loan_id, binding(0).permission)])
        .unwrap();
    assert_eq!(exported, input);
    let opened = transfer_predicate(
        &sealed.output,
        &definition(),
        7,
        &PredicateEffect::UnfoldInPlace {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
        },
    )
    .unwrap();
    check_predicate_evidence(&sealed.output, &opened).unwrap();
    let finish = PredicateEffect::Finish {
        holder: PredicateHolder(0),
    };
    let released = transfer_predicate(&opened.output, &definition(), 7, &finish).unwrap();
    check_predicate_evidence(&opened.output, &released).unwrap();
    assert_eq!(released.output.loans, input.loans);
    assert_eq!(released.output.allocations, input.allocations);
    assert_eq!(
        released.output.value(binding(0).permission),
        Some(&AbstractValue::Permission(permission))
    );
    assert!(released.output.predicates.is_empty());
    let mut bad = opened.output.clone();
    bad.allocation_mut(id).unwrap().record_scalar_content(
        ByteRange::new(0, 8).unwrap(),
        VirMemoryAccess::core_u64(),
        AbstractValue::U64(U64Interval::exact(9)),
    );
    let before = bad.clone();
    assert_eq!(
        transfer_predicate(&bad, &definition(), 7, &finish),
        Err(PredicateError::OutstandingCleanup)
    );
    assert_eq!(bad, before);
    let mut ended = sealed.output;
    ended
        .loan_mut(loan_id)
        .unwrap()
        .set_activity(LoanActivity::Ended);
    assert_eq!(
        ended.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    // Static loan sites cannot be recycled while either an open or a closed
    // predicate still names their old dynamic instance.
    let mut replacement = input.loan(loan_id).unwrap().clone();
    replacement.set_activity(LoanActivity::Active);
    let mut ended_open = opened.output;
    ended_open
        .loan_mut(loan_id)
        .unwrap()
        .set_activity(LoanActivity::Ended);
    for mut pending in [ended, ended_open.clone()] {
        let before = pending.clone();
        assert_eq!(
            pending.define_next_loan_instance(loan_id, replacement.clone()),
            Err(ResourceStateDefinitionError::DuplicateLoan(loan_id))
        );
        assert_eq!(pending, before);
    }
    // An Ended flag alone is not an actual loan end: its authority must also
    // have been consumed. Reject the malformed state before simulating NLL.
    assert_eq!(
        transfer_predicate(&ended_open, &definition(), 7, &finish),
        Err(PredicateError::OutstandingCleanup)
    );
    assert!(
        ended_open
            .loan_mut(loan_id)
            .unwrap()
            .remove_authority(binding(0).permission)
    );
    *ended_open.value_mut(binding(0).permission).unwrap() =
        AbstractValue::Permission(permission.with_availability(PermissionAvailability::Consumed));
    let mut cleaned = transfer_predicate(&ended_open, &definition(), 7, &finish)
        .unwrap()
        .output;
    cleaned
        .define_next_loan_instance(loan_id, replacement)
        .unwrap();
}

#[test]
fn suspended_predicate_export_preserves_actual_child_loans_and_checks_authority() {
    let mut input = state();
    let id = AbstractAllocationId::new(0);
    let loan_id = VirLoanId::new(0);
    let range = ByteRange::new(0, 16).unwrap();
    let permission = AbstractPermission::new(
        AbstractProvenance::Known(id),
        AbstractByteRange::Exact(range),
        AccessPermission::Write,
        FreeCapability::No,
    )
    .with_authority(PermissionAuthority::Loan(loan_id));
    *input.value_mut(binding(0).permission).unwrap() = AbstractValue::Permission(permission);
    input
        .define_loan(
            loan_id,
            AbstractLoan::new(
                AbstractProvenance::Known(id),
                range,
                crate::VirLoanKind::Mutable,
                crate::VirBorrowRegionId::new(0),
                None,
                LoanActivity::Active,
            )
            .with_authority(binding(0).permission)
            .with_footprint(Some(MemoryFootprint {
                provenance: AbstractProvenance::Known(id),
                access: VirMemoryAccess::core_u64(),
                stride_bytes: 8,
                range: AbstractByteRange::Exact(range),
                envelope: range,
            })),
        )
        .unwrap();

    let child = VirLoanId::new(1);
    let child_range = ByteRange::new(8, 16).unwrap();
    input
        .loan_mut(loan_id)
        .unwrap()
        .set_activity(LoanActivity::Suspended);
    input
        .define_loan(
            child,
            AbstractLoan::new(
                AbstractProvenance::Known(id),
                child_range,
                VirLoanKind::Mutable,
                crate::VirBorrowRegionId::new(0),
                Some(loan_id),
                LoanActivity::Active,
            )
            .with_footprint(Some(MemoryFootprint {
                provenance: AbstractProvenance::Known(id),
                access: VirMemoryAccess::core_u64(),
                stride_bytes: 8,
                range: AbstractByteRange::Exact(child_range),
                envelope: child_range,
            })),
        )
        .unwrap();
    let sealed = fold(&input, 0, 0).unwrap();
    check_predicate_evidence(&input, &sealed).unwrap();
    assert_eq!(
        sealed.output.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_eq!(
        transfer_predicate(
            &sealed.output,
            &definition(),
            7,
            &PredicateEffect::UnfoldInPlace {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)]
            }
        ),
        Err(PredicateError::Borrowed)
    );
    let mut exported = sealed.output.clone();
    exported
        .export_predicate_parameters(&definition(), &[(loan_id, binding(0).permission)])
        .unwrap();
    assert_eq!(
        exported, input,
        "ABI export preserves suspended parent, child and allocation facts"
    );
    assert_eq!(
        sealed.output.predicate_observation_view(),
        input,
        "logical observation exposes only the actual carrier, retaining every loan"
    );
    for mutation in 0..6 {
        let mut bad = sealed.output.clone();
        match mutation {
            0 => {
                bad.loan_mut(loan_id)
                    .unwrap()
                    .remove_authority(binding(0).permission);
            }
            1 => bad
                .loan_mut(loan_id)
                .unwrap()
                .set_activity(LoanActivity::Ended),
            2 => bad
                .loan_mut(child)
                .unwrap()
                .set_activity(LoanActivity::MaybeActive),
            3 | 4 => {
                let loan = bad.loan(child).unwrap().clone();
                let mut footprint = loan.footprint().unwrap();
                footprint.range = if mutation == 3 {
                    AbstractByteRange::Unknown
                } else {
                    AbstractByteRange::Exact(range)
                };
                footprint.envelope = range;
                *bad.loan_mut(child).unwrap() = loan.with_footprint(Some(footprint));
            }
            5 => bad
                .allocation_mut(id)
                .unwrap()
                .mark_uninitialized(ByteRange::new(0, 8).unwrap())
                .unwrap(),
            _ => unreachable!(),
        }
        let before = bad.clone();
        assert_eq!(
            bad.predicate_observation_view(),
            before,
            "invalid representation or loan evidence cannot supply a logical read"
        );
        assert!(
            bad.export_predicate_parameters(&definition(), &[(loan_id, binding(0).permission)])
                .is_err(),
            "mutation {mutation}"
        );
        assert_eq!(bad, before, "rejected export must be atomic");
    }
}

// Refolding checks a representation; it is not an owner/loan conversion.
#[test]
fn refold_preserves_the_original_authority_identity() {
    fn install_loan(s: &mut ResourceState, base: u32, loan: crate::VirLoanId) {
        let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
        let range = ByteRange::new(0, 16).unwrap();
        s.values
            .insert(binding(base).pointer, *s.value(binding(0).pointer).unwrap());
        s.values.insert(
            binding(base).permission,
            AbstractValue::Permission(
                AbstractPermission::new(
                    provenance,
                    AbstractByteRange::Exact(range),
                    AccessPermission::Write,
                    FreeCapability::No,
                )
                .with_authority(PermissionAuthority::Loan(loan)),
            ),
        );
        s.define_loan(
            loan,
            AbstractLoan::new(
                provenance,
                range,
                crate::VirLoanKind::Mutable,
                crate::VirBorrowRegionId::new(0),
                None,
                LoanActivity::Active,
            )
            .with_authority(binding(base).permission)
            .with_footprint(Some(MemoryFootprint {
                provenance,
                access: VirMemoryAccess::core_u64(),
                stride_bytes: 8,
                range: AbstractByteRange::Exact(range),
                envelope: range,
            })),
        )
        .unwrap();
    }
    fn open(s: &ResourceState) -> ResourceState {
        let closed = fold(s, 0, 0).unwrap().output;
        transfer_predicate(
            &closed,
            &definition(),
            7,
            &PredicateEffect::UnfoldInPlace {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
            },
        )
        .unwrap()
        .output
    }
    let owner = state();
    let mut owner_open = open(&owner);
    install_loan(&mut owner_open, 2, crate::VirLoanId::new(0));
    let before = owner_open.clone();
    assert_eq!(
        fold(&owner_open, 0, 2),
        Err(PredicateError::MissingAuthority)
    );
    assert_eq!(owner_open, before);

    let mut borrowed = state();
    install_loan(&mut borrowed, 0, crate::VirLoanId::new(0));
    let opened = open(&borrowed);
    // The same loan can still refold and its evidence is replayable.
    let same = fold(&opened, 0, 0).unwrap();
    check_predicate_evidence(&opened, &same).unwrap();
    for replacement_is_owner in [false, true] {
        let mut changed = opened.clone();
        changed
            .loan_mut(crate::VirLoanId::new(0))
            .unwrap()
            .set_activity(LoanActivity::Ended);
        let AbstractValue::Permission(p) = changed.value_mut(binding(0).permission).unwrap() else {
            unreachable!()
        };
        p.mark_consumed();
        if replacement_is_owner {
            changed.values.insert(
                binding(2).pointer,
                *owner.value(binding(0).pointer).unwrap(),
            );
            changed.values.insert(
                binding(2).permission,
                *owner.value(binding(0).permission).unwrap(),
            );
        } else {
            install_loan(&mut changed, 2, crate::VirLoanId::new(1));
        }
        let before = changed.clone();
        assert_eq!(fold(&changed, 0, 2), Err(PredicateError::MissingAuthority));
        assert_eq!(changed, before);
    }
}

#[test]
fn scoped_owner_handoff_preserves_cleanup_and_requires_the_real_ended_loan() {
    let mut state = fold(&state(), 0, 0).unwrap().output;
    let original = state.clone();
    let loan = crate::VirLoanId::new(9);
    let range = ByteRange::new(0, 16).unwrap();
    let effect = crate::VirLoanEffect {
        loan,
        kind: crate::VirLoanKind::Mutable,
        region: crate::VirBorrowRegionId::new(0),
        parent: None,
        source_pointer: binding(0).pointer,
        source_permission: binding(0).permission,
        reference: VirMemoryAccess::core_u64(),
        range: crate::VirLoanRange {
            start_bytes: 0,
            end_bytes: 16,
        },
        origin: crate::VirOriginId::new(0),
    };
    assert_eq!(
        state.prepare_predicate_borrow(effect, 16),
        Some(PredicateHolder(0))
    );
    let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
    state.values.insert(
        binding(2).pointer,
        *state.value(binding(0).pointer).unwrap(),
    );
    state.values.insert(
        binding(2).permission,
        AbstractValue::Permission(
            AbstractPermission::new(
                provenance,
                AbstractByteRange::Exact(range),
                AccessPermission::Write,
                FreeCapability::No,
            )
            .with_authority(PermissionAuthority::Loan(loan)),
        ),
    );
    state
        .define_loan(
            loan,
            AbstractLoan::new(
                provenance,
                range,
                crate::VirLoanKind::Mutable,
                crate::VirBorrowRegionId::new(0),
                None,
                LoanActivity::Active,
            )
            .with_authority(binding(2).permission)
            .with_footprint(Some(MemoryFootprint {
                provenance,
                access: VirMemoryAccess::core_u64(),
                stride_bytes: 8,
                range: AbstractByteRange::Exact(range),
                envelope: range,
            })),
        )
        .unwrap();
    state
        .seal_predicate_borrow(PredicateHolder(0), loan, binding(2))
        .unwrap();
    // Three simultaneous restoration frames, including a non-immediate owner.
    let mut nested = state.clone();
    let mut chain = vec![(PredicateHolder(0), loan, binding(2))];
    for depth in 0..2 {
        let parent = crate::VirLoanId::new(9 + depth);
        let child_loan = crate::VirLoanId::new(10 + depth);
        let source = binding(2 + depth * 2);
        let child_binding = binding(4 + depth * 2);
        let holder = nested
            .prepare_predicate_borrow(
                crate::VirLoanEffect {
                    loan: child_loan,
                    parent: Some(parent),
                    source_pointer: source.pointer,
                    source_permission: source.permission,
                    ..effect
                },
                16,
            )
            .unwrap();
        nested
            .loan_mut(parent)
            .unwrap()
            .set_activity(LoanActivity::Suspended);
        nested.values.insert(
            child_binding.pointer,
            *nested.value(source.pointer).unwrap(),
        );
        let AbstractValue::Permission(permission) = *nested.value(source.permission).unwrap()
        else {
            unreachable!()
        };
        nested.values.insert(
            child_binding.permission,
            AbstractValue::Permission(
                permission.with_authority(PermissionAuthority::Loan(child_loan)),
            ),
        );
        nested
            .define_loan(
                child_loan,
                AbstractLoan::new(
                    provenance,
                    range,
                    crate::VirLoanKind::Mutable,
                    effect.region,
                    Some(parent),
                    LoanActivity::Active,
                )
                .with_authority(child_binding.permission)
                .with_footprint(Some(MemoryFootprint {
                    provenance,
                    access: VirMemoryAccess::core_u64(),
                    stride_bytes: 8,
                    range: AbstractByteRange::Exact(range),
                    envelope: range,
                })),
            )
            .unwrap();
        nested
            .seal_predicate_borrow(holder, child_loan, child_binding)
            .unwrap();
        chain.push((holder, child_loan, child_binding));
    }
    let leaf = chain.last().unwrap().2;
    for missing in [chain[1].0, chain[2].0] {
        let mut broken = nested.clone();
        broken.predicates.remove(&missing);
        assert!(
            broken
                .export_predicate_interface(&definition(), &[leaf])
                .is_err()
        );
    }
    assert!(nested.prepare_predicate_restore(loan, binding(2)).is_err());
    for (holder, child_loan, child_binding) in chain.into_iter().rev() {
        assert_eq!(
            nested
                .prepare_predicate_restore(child_loan, child_binding)
                .unwrap(),
            Some(holder)
        );
        assert!(nested.restore_predicate_lender(holder, child_loan).is_err());
        let AbstractValue::Permission(p) = nested.value_mut(child_binding.permission).unwrap()
        else {
            unreachable!()
        };
        p.mark_consumed();
        let child = nested.loan_mut(child_loan).unwrap();
        child.remove_authority(child_binding.permission);
        child.set_activity(LoanActivity::Ended);
        if let Some(parent) = child.parent() {
            nested
                .loan_mut(parent)
                .unwrap()
                .set_activity(LoanActivity::Active);
        }
        nested.restore_predicate_lender(holder, child_loan).unwrap();
    }
    assert_eq!(nested.predicates, original.predicates);
    assert_eq!(nested.allocations, original.allocations);
    let suspended = state.clone();
    assert_eq!(state.join(&suspended).unwrap(), state);
    let mut relabeled = suspended.clone();
    let parent = relabeled.predicates.remove(&PredicateHolder(0)).unwrap();
    relabeled.predicates.insert(PredicateHolder(99), parent);
    assert_eq!(
        state.join(&relabeled),
        Err(ResourceJoinError::PredicateStateMismatch)
    );
    assert_eq!(
        relabeled.join(&state),
        Err(ResourceJoinError::PredicateStateMismatch)
    );
    assert_eq!(state.allocations, original.allocations);
    assert_eq!(
        state.value(binding(0).permission),
        original.value(binding(0).permission)
    );
    assert_eq!(
        state.check_predicate_boundary(&[PredicateHolder(0)]),
        Err(PredicateError::Borrowed)
    );
    assert_eq!(
        state.restore_predicate_lender(PredicateHolder(0), loan),
        Err(PredicateError::Borrowed)
    );
    assert_eq!(state, suspended);
    assert_eq!(
        transfer_predicate(
            &state,
            &definition(),
            7,
            &PredicateEffect::Move {
                source: PredicateHolder(0),
                destination: PredicateHolder(3),
            }
        ),
        Err(PredicateError::Borrowed)
    );
    let child = *state
        .predicates
        .keys()
        .find(|h| **h != PredicateHolder(0))
        .unwrap();
    let opened = transfer_predicate(
        &state,
        &definition(),
        7,
        &PredicateEffect::UnfoldInPlace {
            holder: child,
            bindings: vec![binding(2)],
        },
    )
    .unwrap();
    check_predicate_evidence(&state, &opened).unwrap();
    let mut open = opened.output;
    let before = open.clone();
    assert_eq!(
        open.prepare_predicate_restore(loan, binding(2)),
        Err(PredicateError::OpenBoundary)
    );
    assert_eq!(open, before);
    let closed = transfer_predicate(
        &open,
        &definition(),
        7,
        &PredicateEffect::Fold {
            holder: child,
            bindings: vec![binding(2)],
        },
    )
    .unwrap();
    check_predicate_evidence(&open, &closed).unwrap();
    state = closed.output;
    assert_eq!(
        state.prepare_predicate_restore(loan, binding(2)).unwrap(),
        Some(PredicateHolder(0))
    );
    assert_eq!(state.predicates.len(), 1);
    // Consuming the child token alone does not discharge the live loan.
    assert_eq!(
        state.restore_predicate_lender(PredicateHolder(0), loan),
        Err(PredicateError::Borrowed)
    );
    let AbstractValue::Permission(permission) = state.value_mut(binding(2).permission).unwrap()
    else {
        unreachable!()
    };
    permission.mark_consumed();
    let tracked = state.loan_mut(loan).unwrap();
    tracked.remove_authority(binding(2).permission);
    tracked.set_activity(LoanActivity::Ended);
    state
        .restore_predicate_lender(PredicateHolder(0), loan)
        .unwrap();
    assert_eq!(state.predicates, original.predicates);
    assert_eq!(state.allocations, original.allocations);
    assert!(
        state
            .check_predicate_boundary(&[PredicateHolder(0)])
            .is_ok()
    );
}

#[test]
fn stored_predicate_tokens_require_the_exact_payload_and_actual_destruction() {
    let mut s = fold(&state(), 0, 0).unwrap().output;
    let holder = PredicateHolder(0);
    let resource = s.predicates[&holder].resources[0].clone();
    let storage = AbstractAllocationId::new(1);
    let key = ResourcePayloadKey::new(0, VirMemoryAccess::core_u64());
    s.define_allocation(storage, AbstractAllocation::new_local(8, 8).unwrap())
        .unwrap();
    let payload = TypedResourcePayload::new(
        resource.pointer,
        resource
            .permission
            .with_availability(PermissionAvailability::Consumed),
    );
    assert_eq!(
        s.predicate_carrier_to_store(binding(0).permission, resource.pointer),
        Some((holder, resource.permission))
    );
    assert!(s.store_predicate_carrier(binding(0).permission, storage, key));
    assert!(!s.predicate_representation_valid(&s.predicates[&holder]));
    s.allocation_mut(storage)
        .unwrap()
        .set_resource_payload(key, MovePathState::available(payload))
        .unwrap();
    assert!(s.predicate_representation_valid(&s.predicates[&holder]));
    assert!(!s.finish_dropped_predicate(holder));
    assert_eq!(
        transfer_predicate(
            &s,
            &definition(),
            7,
            &PredicateEffect::Unfold {
                holder,
                outputs: vec![binding(2)],
            }
        ),
        Err(PredicateError::MissingAuthority)
    );
    let before = s.clone();
    assert!(
        s.take_predicate_carrier(
            storage,
            key,
            TypedResourcePayload::new(resource.pointer, resource.permission),
            binding(2).permission
        )
        .is_err()
    );
    assert_eq!(s, before);
    let mut lost = s.clone();
    lost.allocation_mut(storage)
        .unwrap()
        .set_resource_payload(key, MovePathState::Unknown)
        .unwrap();
    let before = lost.clone();
    assert!(
        lost.take_predicate_carrier(storage, key, payload, binding(2).permission)
            .is_err()
    );
    assert_eq!(lost, before);
    let mut taken = s.clone();
    assert!(
        taken
            .take_predicate_carrier(storage, key, payload, binding(2).permission)
            .unwrap()
    );
    assert!(
        !taken
            .take_predicate_carrier(storage, key, payload, binding(4).permission)
            .unwrap()
    );
    assert_eq!(
        taken.predicates[&holder].resources[0].carrier,
        Some(binding(2).permission)
    );
    assert!(
        s.predicate_owner_to_drop(storage, key, &payload, &BTreeSet::from([(storage, key)]))
            .is_some()
    );
    s.allocation_mut(resource.allocation).unwrap().mark_dead();
    assert!(!s.finish_dropped_predicate(holder));
    s.allocation_mut(storage)
        .unwrap()
        .set_resource_payload(key, MovePathState::Moved)
        .unwrap();
    assert!(s.finish_dropped_predicate(holder));
    assert!(s.predicates.is_empty());
}

#[test]
fn grouped_drop_checks_all_members_and_retires_only_after_every_release() {
    let mut s = state();
    let other = AbstractAllocationId::new(1);
    s.define_allocation(
        other,
        s.allocation(AbstractAllocationId::new(0)).unwrap().clone(),
    )
    .unwrap();
    s.define_value(
        binding(2).pointer,
        AbstractValue::Pointer(
            AbstractPointer::new(
                AbstractProvenance::Known(other),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            )
            .with_memory_access(Some(VirMemoryAccess::core_u64())),
        ),
    )
    .unwrap();
    s.define_value(
        binding(2).permission,
        AbstractValue::Permission(AbstractPermission::new(
            AbstractProvenance::Known(other),
            AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
            AccessPermission::Write,
            FreeCapability::Yes,
        )),
    )
    .unwrap();
    let shape = definition().resources[0].clone();
    let definition =
        PredicateDefinition::new(VirPredicateId::new(0), 7, vec![shape.clone(), shape]).unwrap();
    let evidence = transfer_predicate(
        &s,
        &definition,
        7,
        &PredicateEffect::Fold {
            holder: PredicateHolder(0),
            bindings: vec![binding(0), binding(2)],
        },
    )
    .unwrap();
    check_predicate_evidence(&s, &evidence).unwrap();
    s = evidence.output;
    let resources = s.predicates[&PredicateHolder(0)].resources.clone();
    let storage = AbstractAllocationId::new(2);
    s.define_allocation(storage, AbstractAllocation::new_local(16, 8).unwrap())
        .unwrap();
    let keys = [
        ResourcePayloadKey::new(0, VirMemoryAccess::core_u64()),
        ResourcePayloadKey::new(8, VirMemoryAccess::core_u64()),
    ];
    let scope = keys
        .map(|key| (storage, key))
        .into_iter()
        .collect::<BTreeSet<_>>();
    let payloads = resources
        .iter()
        .map(|r| {
            TypedResourcePayload::new(
                r.pointer,
                r.permission
                    .with_availability(PermissionAvailability::Consumed),
            )
        })
        .collect::<Vec<_>>();
    for i in 0..2 {
        assert!(s.store_predicate_carrier(binding(i as u32 * 2).permission, storage, keys[i]));
        s.allocation_mut(storage)
            .unwrap()
            .set_resource_payload(keys[i], MovePathState::available(payloads[i]))
            .unwrap();
    }
    for i in 0..2 {
        assert!(
            s.predicate_owner_to_drop(storage, keys[i], &payloads[i], &scope)
                .is_some()
        );
        assert!(
            s.predicate_owner_to_drop(
                storage,
                keys[i],
                &payloads[i],
                &BTreeSet::from([(storage, keys[i])])
            )
            .is_some()
        );
    }
    check_split_group_cleanup(&s, PredicateHolder(0));
    let mut missing = s.clone();
    missing
        .allocation_mut(storage)
        .unwrap()
        .set_resource_payload(keys[1], MovePathState::Unknown)
        .unwrap();
    let before = missing.clone();
    assert!(
        missing
            .predicate_owner_to_drop(storage, keys[0], &payloads[0], &scope)
            .is_none()
    );
    assert_eq!(missing, before);
    let mut borrowed = s.clone();
    borrowed
        .define_loan(
            crate::VirLoanId::new(0),
            AbstractLoan::new(
                resources[1].pointer.provenance(),
                ByteRange::new(0, 16).unwrap(),
                crate::VirLoanKind::Shared,
                crate::VirBorrowRegionId::new(0),
                None,
                LoanActivity::Active,
            )
            .with_footprint(Some(MemoryFootprint {
                provenance: resources[1].pointer.provenance(),
                access: VirMemoryAccess::core_u64(),
                stride_bytes: 8,
                range: AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
                envelope: ByteRange::new(0, 16).unwrap(),
            })),
        )
        .unwrap();
    assert!(
        borrowed
            .predicate_owner_to_drop(storage, keys[0], &payloads[0], &scope)
            .is_none()
    );
    for i in 0..2 {
        s.allocation_mut(resources[i].allocation)
            .unwrap()
            .mark_dead();
        assert!(!s.finish_dropped_predicate(PredicateHolder(0)));
        s.allocation_mut(storage)
            .unwrap()
            .set_resource_payload(keys[i], MovePathState::Moved)
            .unwrap();
        assert_eq!(s.finish_dropped_predicate(PredicateHolder(0)), i == 1);
    }
    assert!(s.predicates.is_empty());
}

#[test]
fn object_drop_rejects_damaged_groups_and_checks_complete_groups() {
    let source = include_str!("../../../../spec/cases/verify/predicate-group-drop.nera");
    let output = crate::analyze(&crate::SourceFile::from_text("group.nera", source));
    let unit = output.vir().unwrap().as_unit();
    let mut state = ResourceState::new();
    let mut owners = Vec::new();
    let mut folded = false;
    let mut tested = false;
    for instruction in &unit.runtime.functions[0].blocks[0].instructions {
        if let VirInstruction::Allocate { pointer_result, .. } = instruction.instruction {
            owners.push(pointer_result.id);
        }
        if matches!(
            instruction.instruction,
            VirInstruction::ResourceInitialize { .. }
        ) && !folded
        {
            assert_eq!(owners.len(), 2);
            let bindings = owners
                .iter()
                .map(|pointer| {
                    let AbstractValue::Pointer(p) = state.value(*pointer).unwrap() else {
                        unreachable!()
                    };
                    let permission = state
                        .values()
                        .iter()
                        .find_map(|(id, value)| match value {
                            AbstractValue::Permission(q)
                                if q.provenance() == p.provenance()
                                    && q.availability() == PermissionAvailability::Available =>
                            {
                                Some(*id)
                            }
                            _ => None,
                        })
                        .unwrap();
                    PredicateBinding {
                        pointer: *pointer,
                        permission,
                    }
                })
                .collect();
            let definition = PredicateDefinition::new(
                VirPredicateId::new(0),
                0,
                vec![
                    PredicateResourceShape {
                        size_bytes: 8,
                        initialized: vec![]
                    };
                    2
                ],
            )
            .unwrap();
            state = transfer_predicate(
                &state,
                &definition,
                0,
                &PredicateEffect::Fold {
                    holder: PredicateHolder(0),
                    bindings,
                },
            )
            .unwrap()
            .output;
            folded = true;
        }
        if let VirInstruction::ObjectDrop { pointer, .. } = instruction.instruction
            && let Some(instance) = state.predicates.get(&PredicateHolder(0))
            && instance.resources.iter().all(|r| r.storage.is_some())
            && matches!(state.value(pointer),Some(AbstractValue::Pointer(p)) if p.provenance()==AbstractProvenance::Known(instance.resources[0].storage.unwrap().0))
        {
            let mut damaged = state.clone();
            let (storage, key) = instance.resources[1].storage.unwrap();
            damaged
                .allocation_mut(storage)
                .unwrap()
                .set_resource_payload(key, MovePathState::Unknown)
                .unwrap();
            let failed = crate::verifier::transfer_instruction_with_memory(
                &damaged,
                instruction,
                &unit.memory,
            )
            .unwrap();
            assert!(failed.obligations().iter().any(|o| !o.is_proven()));
            // Refuted drop obligations suppress this successor rather than
            // publishing a partially cleaned valid state.
            assert!(!failed.state().path_condition().is_reachable());
            let complete = crate::verifier::transfer_instruction_with_memory(
                &state,
                instruction,
                &unit.memory,
            )
            .unwrap();
            assert!(
                complete.obligations().iter().all(|o| o.is_proven()),
                "{:?}",
                complete.obligations()
            );
            assert!(complete.state().predicate_instances().is_empty());
            for r in &instance.resources {
                assert_eq!(
                    complete
                        .state()
                        .allocation(r.allocation)
                        .unwrap()
                        .liveness(),
                    LivenessState::Dead
                );
            }
            tested = true;
            break;
        }
        let step =
            crate::verifier::transfer_instruction_with_memory(&state, instruction, &unit.memory)
                .unwrap();
        assert!(
            step.obligations().iter().all(|o| o.is_proven()),
            "{:?}",
            step.obligations()
        );
        state = step.state().clone();
    }
    assert!(tested);
}

#[test]
fn stored_predicate_abi_adapters_are_atomic_and_erase_scratch_values() {
    for borrowed in [false, true] {
        let mut entry = state();
        let loan = crate::VirLoanId::new(0);
        if borrowed {
            let AbstractValue::Permission(owner) = *entry.value(binding(0).permission).unwrap()
            else {
                unreachable!()
            };
            entry.values.insert(
                binding(0).permission,
                AbstractValue::Permission(
                    AbstractPermission::new(
                        owner.provenance(),
                        owner.range(),
                        AccessPermission::Write,
                        FreeCapability::No,
                    )
                    .with_authority(PermissionAuthority::Loan(loan)),
                ),
            );
            entry
                .define_loan(
                    loan,
                    AbstractLoan::new(
                        owner.provenance(),
                        ByteRange::new(0, 16).unwrap(),
                        crate::VirLoanKind::Mutable,
                        crate::VirBorrowRegionId::new(0),
                        None,
                        LoanActivity::Active,
                    )
                    .with_authority(binding(0).permission)
                    .with_footprint(Some(MemoryFootprint {
                        provenance: owner.provenance(),
                        access: VirMemoryAccess::core_u64(),
                        stride_bytes: 8,
                        range: owner.range(),
                        envelope: ByteRange::new(0, 16).unwrap(),
                    })),
                )
                .unwrap();
        }
        if borrowed {
            let mut missing = entry.clone();
            let loan_without_range = missing.loan(loan).unwrap().clone().with_footprint(None);
            *missing.loan_mut(loan).unwrap() = loan_without_range;
            assert_eq!(fold(&missing, 0, 0), Err(PredicateError::MissingAuthority));
        }
        let mut s = fold(&entry, 0, 0).unwrap().output;
        let r = s.predicates[&PredicateHolder(0)].resources[0].clone();
        let storage = AbstractAllocationId::new(1);
        let key = ResourcePayloadKey::new(0, VirMemoryAccess::core_u64());
        s.define_allocation(storage, AbstractAllocation::new_local(8, 8).unwrap())
            .unwrap();
        assert!(s.store_predicate_carrier(binding(0).permission, storage, key));
        s.allocation_mut(storage)
            .unwrap()
            .set_resource_payload(
                key,
                MovePathState::available(TypedResourcePayload::new(
                    r.pointer,
                    r.permission
                        .with_availability(PermissionAvailability::Consumed),
                )),
            )
            .unwrap();
        if borrowed {
            assert!(s.loan_mut(loan).unwrap().move_authority_to_storage(
                binding(0).permission,
                storage,
                key
            ));
        }
        s.define_value(
            binding(4).pointer,
            AbstractValue::Pointer(
                AbstractPointer::new(
                    AbstractProvenance::Known(storage),
                    U64Interval::exact(0),
                    GuaranteedAlignment::new(8).unwrap(),
                )
                .with_memory_access(Some(VirMemoryAccess::core_u64())),
            ),
        )
        .unwrap();
        s.define_value(
            binding(4).permission,
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(storage),
                AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap()),
                AccessPermission::Write,
                FreeCapability::No,
            )),
        )
        .unwrap();
        let before = s.clone();
        assert!(
            s.predicate_storage_interface(
                &definition(),
                &[binding(4)],
                &[Some((8, VirMemoryAccess::core_u64()))],
                None
            )
            .is_err()
        );
        assert_eq!(s, before);
        let projection = [Some((0, VirMemoryAccess::core_u64()))];
        s.predicate_storage_interface(&definition(), &[binding(4)], &projection, None)
            .unwrap();
        assert!(s.predicates.is_empty());
        assert_eq!(
            s.values.keys().collect::<Vec<_>>(),
            before.values.keys().collect::<Vec<_>>()
        );
        assert_eq!(s.allocation(r.allocation), before.allocation(r.allocation));
        assert_eq!(s.loans, before.loans);
        let exported = s.clone();
        if borrowed {
            let mut exhausted = exported.clone();
            exhausted
                .loan_mut(loan)
                .unwrap()
                .add_authority(VirValueId::new(u32::MAX));
            let original = exhausted.clone();
            assert_eq!(
                exhausted.predicate_storage_interface(
                    &definition(),
                    &[binding(4)],
                    &projection,
                    Some((PredicateHolder(12), true))
                ),
                Err(PredicateError::Budget)
            );
            assert_eq!(exhausted, original);
            let mut broken = exported.clone();
            assert!(broken.loan_mut(loan).unwrap().move_authority_from_storage(
                storage,
                key,
                VirValueId::new(100)
            ));
            let original = broken.clone();
            assert!(
                broken
                    .predicate_storage_interface(
                        &definition(),
                        &[binding(4)],
                        &projection,
                        Some((PredicateHolder(12), true))
                    )
                    .is_err()
            );
            assert_eq!(broken, original);
        }
        assert!(
            s.predicate_storage_interface(&definition(), &[binding(4)], &projection, None)
                .is_err()
        );
        assert_eq!(s, exported);
        s.predicate_storage_interface(
            &definition(),
            &[binding(4)],
            &projection,
            Some((PredicateHolder(12), true)),
        )
        .unwrap();
        assert_eq!(
            s.values.keys().collect::<Vec<_>>(),
            before.values.keys().collect::<Vec<_>>()
        );
        assert_eq!(s.loans, before.loans);
        let imported = &s.predicates[&PredicateHolder(12)];
        assert_eq!(imported.resources[0].storage, Some((storage, key)));
        assert_eq!(imported.resources[0].carrier, None);
        assert!(s.predicate_representation_valid(imported));
        assert_eq!(
            s.allocation(r.allocation)
                .unwrap()
                .initialization()
                .classify(ByteRange::new(8, 16).unwrap()),
            InitializationClass::MaybeInitialized
        );
        let before = s.clone();
        assert!(
            s.predicate_storage_interface(
                &definition(),
                &[binding(4)],
                &projection,
                Some((PredicateHolder(13), true))
            )
            .is_err()
        );
        assert_eq!(s, before);
    }
}

#[test]
fn predicate_observation_views_are_disposable_and_check_real_closed_tokens() {
    let closed = fold(&state(), 0, 0).unwrap().output;
    let original = closed.clone();
    let view = closed.predicate_observation_view();
    assert_eq!(closed, original);
    assert!(
        matches!(closed.value(binding(0).permission), Some(AbstractValue::Permission(p)) if p.availability() == PermissionAvailability::Consumed)
    );
    assert!(
        matches!(view.value(binding(0).permission), Some(AbstractValue::Permission(p)) if p.availability() == PermissionAvailability::Available)
    );
    assert!(view.predicates.is_empty());
    assert_eq!(
        view.allocation(AbstractAllocationId::new(0)),
        closed.allocation(AbstractAllocationId::new(0))
    );
    let mut malformed = closed.clone();
    malformed.values.remove(&binding(0).pointer);
    assert_eq!(malformed.predicate_observation_view(), malformed);
    let mut malformed = closed.clone();
    malformed
        .predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .borrowed_by
        .insert(0, crate::VirLoanId::new(7));
    assert_eq!(malformed.predicate_observation_view(), malformed);
    let mut malformed = closed;
    malformed
        .allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .record_scalar_content(
            ByteRange::new(0, 8).unwrap(),
            VirMemoryAccess::core_u64(),
            AbstractValue::U64(U64Interval::exact(9)),
        );
    assert_eq!(malformed.predicate_observation_view(), malformed);
}

#[test]
fn predicate_import_preserves_checked_scalars_and_rejects_contradictions_atomically() {
    for n in [0, 5, 9] {
        let mut input = state();
        let id = AbstractAllocationId::new(0);
        let cell = ByteRange::new(0, 8).unwrap();
        input.allocation_mut(id).unwrap().record_scalar_content(
            cell,
            VirMemoryAccess::core_u64(),
            AbstractValue::U64(U64Interval::exact(n)),
        );
        let original = input.clone();
        let result =
            input.import_predicate_interface(&definition(), &[binding(0)], PredicateHolder(0));
        if n <= 8 {
            result.unwrap();
            assert_eq!(
                input
                    .allocation(id)
                    .unwrap()
                    .scalar_content(cell, VirMemoryAccess::core_u64()),
                Some(AbstractValue::U64(U64Interval::exact(n)))
            );
        } else {
            assert_eq!(result, Err(PredicateError::UnprovedRepresentation));
            assert_eq!(input, original);
        }
    }
}

#[test]
fn multi_resource_handoff_is_incremental_and_restoration_is_atomic() {
    let mut input = state();
    let first = AbstractAllocationId::new(0);
    let second = AbstractAllocationId::new(1);
    input
        .define_allocation(second, input.allocation(first).unwrap().clone())
        .unwrap();
    let provenance = AbstractProvenance::Known(second);
    input
        .define_value(
            binding(2).pointer,
            AbstractValue::Pointer(
                AbstractPointer::new(
                    provenance,
                    U64Interval::exact(0),
                    GuaranteedAlignment::new(8).unwrap(),
                )
                .with_memory_access(Some(VirMemoryAccess::core_u64())),
            ),
        )
        .unwrap();
    input
        .define_value(
            binding(2).permission,
            AbstractValue::Permission(AbstractPermission::new(
                provenance,
                AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
                AccessPermission::Write,
                FreeCapability::Yes,
            )),
        )
        .unwrap();
    let single = definition();
    let mut pair = PredicateDefinition::new(
        single.id(),
        single.module(),
        vec![single.resources[0].clone(); 2],
    )
    .unwrap();
    pair = pair
        .with_scalar_constraints(vec![
            single.scalar_constraints[0],
            PredicateScalarConstraint {
                resource: 1,
                ..single.scalar_constraints[0]
            },
        ])
        .unwrap();
    input
        .predicate_fold(
            &pair,
            pair.module(),
            PredicateHolder(0),
            &[binding(0), binding(2)],
        )
        .unwrap();
    let sealed = input.clone();
    let range = ByteRange::new(0, 16).unwrap();
    for index in 0..2u32 {
        let source = binding(index * 2);
        let target = binding(4 + index * 2);
        let loan = crate::VirLoanId::new(index);
        let effect = crate::VirLoanEffect {
            loan,
            kind: crate::VirLoanKind::Mutable,
            region: crate::VirBorrowRegionId::new(0),
            parent: None,
            source_pointer: source.pointer,
            source_permission: source.permission,
            reference: VirMemoryAccess::core_u64(),
            range: crate::VirLoanRange {
                start_bytes: 0,
                end_bytes: 16,
            },
            origin: crate::VirOriginId::new(0),
        };
        assert_eq!(
            input.prepare_predicate_borrow(effect, 16),
            Some(PredicateHolder(0))
        );
        let AbstractValue::Permission(permission) = *input.value(source.permission).unwrap() else {
            unreachable!()
        };
        input
            .values
            .insert(target.pointer, *input.value(source.pointer).unwrap());
        input.values.insert(
            target.permission,
            AbstractValue::Permission(
                AbstractPermission::new(
                    permission.provenance(),
                    permission.range(),
                    AccessPermission::Write,
                    FreeCapability::No,
                )
                .with_authority(PermissionAuthority::Loan(loan)),
            ),
        );
        input
            .define_loan(
                loan,
                AbstractLoan::new(
                    permission.provenance(),
                    range,
                    crate::VirLoanKind::Mutable,
                    effect.region,
                    None,
                    LoanActivity::Active,
                )
                .with_authority(target.permission)
                .with_footprint(Some(MemoryFootprint {
                    provenance: permission.provenance(),
                    access: VirMemoryAccess::core_u64(),
                    stride_bytes: 8,
                    range: permission.range(),
                    envelope: range,
                })),
            )
            .unwrap();
        // Partial formation must reject malformed authority before publishing
        // even the first edge of a multi-resource group.
        for malformed in [
            AbstractPermission::new(
                permission.provenance(),
                permission.range(),
                AccessPermission::Read,
                FreeCapability::No,
            ),
            AbstractPermission::new(
                permission.provenance(),
                permission.range(),
                AccessPermission::Write,
                FreeCapability::Yes,
            ),
            AbstractPermission::new(
                permission.provenance(),
                AbstractByteRange::Unknown,
                AccessPermission::Write,
                FreeCapability::No,
            ),
        ] {
            let mut broken = input.clone();
            broken.values.insert(
                target.permission,
                AbstractValue::Permission(
                    malformed.with_authority(PermissionAuthority::Loan(loan)),
                ),
            );
            let before = broken.clone();
            assert!(
                broken
                    .seal_predicate_borrow(PredicateHolder(0), loan, target)
                    .is_err()
            );
            assert_eq!(broken, before);
        }
        input
            .seal_predicate_borrow(PredicateHolder(0), loan, target)
            .unwrap();
        assert_eq!(input.predicates.len(), if index == 0 { 1 } else { 2 });
        let before = input.clone();
        assert!(
            input
                .restore_predicate_lender(PredicateHolder(0), loan)
                .is_err()
        );
        assert_eq!(input, before);
    }
    // Aggregate cleanup ends both real stored loans before restoring the lender.
    let mut stored = input.clone();
    let child = *stored
        .predicates
        .keys()
        .find(|h| **h != PredicateHolder(0))
        .unwrap();
    let storage = AbstractAllocationId::new(2);
    stored
        .define_allocation(storage, AbstractAllocation::new_local(16, 8).unwrap())
        .unwrap();
    let keys = [
        ResourcePayloadKey::new(0, VirMemoryAccess::core_u64()),
        ResourcePayloadKey::new(8, VirMemoryAccess::core_u64()),
    ];
    let mut payloads = Vec::new();
    for index in 0..2u32 {
        let source = binding(4 + index * 2);
        let r = stored.predicates[&child].resources[index as usize].clone();
        assert!(
            stored
                .predicate_carrier_to_store(source.permission, r.pointer)
                .is_some()
        );
        let payload = TypedResourcePayload::new(
            r.pointer,
            r.permission
                .with_availability(PermissionAvailability::Consumed),
        );
        let key = keys[index as usize];
        assert!(stored.store_predicate_carrier(source.permission, storage, key));
        stored
            .allocation_mut(storage)
            .unwrap()
            .set_resource_payload(key, MovePathState::available(payload))
            .unwrap();
        assert!(
            stored
                .loan_mut(crate::VirLoanId::new(index))
                .unwrap()
                .move_authority_to_storage(source.permission, storage, key)
        );
        payloads.push(payload);
    }
    check_split_group_cleanup(&stored, child);
    // ABI adaptation must move each real authority out and back, including
    // when another member fails after earlier members were already extracted.
    let mut adapted = stored.clone();
    let root = binding(100);
    adapted
        .define_value(
            root.pointer,
            AbstractValue::Pointer(AbstractPointer::new(
                AbstractProvenance::Known(storage),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            )),
        )
        .unwrap();
    adapted
        .define_value(
            root.permission,
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(storage),
                AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
                AccessPermission::Write,
                FreeCapability::No,
            )),
        )
        .unwrap();
    let projections = [
        Some((0, VirMemoryAccess::core_u64())),
        Some((8, VirMemoryAccess::core_u64())),
    ];
    let original = adapted.clone();
    assert!(
        adapted
            .predicate_storage_interface(
                &pair,
                &[root, root],
                &[projections[0], Some((16, VirMemoryAccess::core_u64()))],
                None
            )
            .is_err()
    );
    assert_eq!(adapted, original);
    adapted
        .predicate_storage_interface(&pair, &[root, root], &projections, None)
        .unwrap();
    assert_eq!(adapted.loans, original.loans);
    assert_eq!(adapted.values, original.values);
    assert!(!adapted.predicates.contains_key(&child));
    let exported = adapted.clone();
    let mut broken = exported.clone();
    assert!(
        broken
            .loan_mut(crate::VirLoanId::new(1))
            .unwrap()
            .move_authority_from_storage(storage, keys[1], VirValueId::new(200))
    );
    let before = broken.clone();
    assert!(
        broken
            .predicate_storage_interface(&pair, &[root, root], &projections, Some((child, false)))
            .is_err()
    );
    assert_eq!(broken, before);
    adapted
        .predicate_storage_interface(&pair, &[root, root], &projections, Some((child, false)))
        .unwrap();
    assert_eq!(adapted.loans, original.loans);
    assert_eq!(adapted.values, original.values);
    assert_eq!(adapted.predicates, original.predicates);
    assert!(adapted.predicate_representation_valid(&adapted.predicates[&child]));
    let scope = BTreeSet::from([(storage, keys[0]), (storage, keys[1])]);
    for index in 0..2 {
        assert_eq!(
            stored.predicate_borrowed_to_drop(storage, keys[index], &payloads[index], &scope),
            Some(child)
        );
        assert_eq!(
            stored.predicate_borrowed_to_drop(
                storage,
                keys[index],
                &payloads[index],
                &BTreeSet::from([(storage, keys[index])])
            ),
            Some(child)
        );
        assert_eq!(
            stored.predicate_borrowed_to_drop(
                storage,
                keys[index],
                &payloads[index],
                &BTreeSet::new()
            ),
            None
        );
    }
    let before = stored.clone();
    assert!(!stored.finish_dropped_predicate(child));
    assert_eq!(stored, before);
    let output = binding(20);
    let mut detached = stored.clone();
    assert!(
        detached
            .loan_mut(crate::VirLoanId::new(0))
            .unwrap()
            .move_authority_from_storage(storage, keys[0], output.permission)
    );
    assert!(!detached.predicate_representation_valid(&detached.predicates[&child]));
    let before = detached.clone();
    assert!(
        detached
            .take_predicate_carrier(storage, keys[0], payloads[0], output.permission)
            .is_err()
    );
    assert_eq!(detached, before);
    let mut taken = stored.clone();
    assert!(
        taken
            .take_predicate_carrier(storage, keys[0], payloads[0], output.permission)
            .unwrap()
    );
    assert!(
        taken
            .loan(crate::VirLoanId::new(0))
            .unwrap()
            .has_value_authority(output.permission)
    );
    assert!(
        !taken
            .loan(crate::VirLoanId::new(0))
            .unwrap()
            .authorities()
            .contains(&crate::verifier::resource::AbstractLoanAuthority::stored(
                storage, keys[0]
            ))
    );
    let mut wrong_payload = stored.clone();
    let before = wrong_payload.clone();
    assert!(
        wrong_payload
            .take_predicate_carrier(storage, keys[0], payloads[1], output.permission)
            .is_err()
    );
    assert_eq!(wrong_payload, before);
    for (index, key) in keys.into_iter().enumerate() {
        let loan = stored
            .loan_mut(crate::VirLoanId::new(index as u32))
            .unwrap();
        assert!(loan.remove_stored_authority(storage, key));
        loan.set_activity(LoanActivity::Ended);
        stored
            .allocation_mut(storage)
            .unwrap()
            .set_resource_payload(key, MovePathState::Moved)
            .unwrap();
    }
    let ended = BTreeSet::from([crate::VirLoanId::new(0), crate::VirLoanId::new(1)]);
    let original = stored.clone();
    // Ending real loans does not silently retire a still-owned child token.
    assert!(stored.restore_ended_predicate_lenders(&ended).is_err());
    assert_eq!(stored, original);
    let mut exported = stored.clone();
    exported.predicates.remove(&child);
    for index in 0..2 {
        let mut broken = exported.clone();
        broken
            .allocation_mut(AbstractAllocationId::new(index))
            .unwrap()
            .record_scalar_content(
                ByteRange::new(0, 8).unwrap(),
                VirMemoryAccess::core_u64(),
                AbstractValue::U64(U64Interval::exact(9)),
            );
        let before = broken.clone();
        assert!(broken.restore_ended_predicate_lenders(&ended).is_err());
        assert_eq!(broken, before);
    }
    let mut stale = exported.clone();
    stale
        .loan_mut(crate::VirLoanId::new(1))
        .unwrap()
        .add_stored_authority(storage, keys[1]);
    let before = stale.clone();
    assert!(stale.restore_ended_predicate_lenders(&ended).is_err());
    assert_eq!(stale, before);
    exported.restore_ended_predicate_lenders(&ended).unwrap();
    assert_eq!(exported.predicates, sealed.predicates);
    assert!(stored.finish_dropped_predicate(child));
    assert_eq!(stored.predicates, sealed.predicates);

    for order in [[0u32, 1u32], [1u32, 0u32]] {
        let mut returned = input.clone();
        for index in order {
            let loan = crate::VirLoanId::new(index);
            let target = binding(4 + index * 2);
            let mut broken = returned.clone();
            broken
                .allocations
                .get_mut(&AbstractAllocationId::new(index))
                .unwrap()
                .record_scalar_content(
                    ByteRange::new(0, 8).unwrap(),
                    VirMemoryAccess::core_u64(),
                    AbstractValue::U64(U64Interval::exact(9)),
                );
            let before = broken.clone();
            assert!(broken.prepare_predicate_restore(loan, target).is_err());
            assert_eq!(broken, before);
            assert_eq!(
                returned.prepare_predicate_restore(loan, target).unwrap(),
                Some(PredicateHolder(0))
            );
            let l = returned.loan_mut(loan).unwrap();
            assert!(l.remove_authority(target.permission));
            l.set_activity(LoanActivity::Ended);
            let AbstractValue::Permission(p) = returned.value_mut(target.permission).unwrap()
            else {
                unreachable!()
            };
            p.mark_consumed();
            returned
                .restore_predicate_lender(PredicateHolder(0), loan)
                .unwrap();
        }
        assert_eq!(returned.predicates, sealed.predicates);
        returned
            .check_predicate_boundary(&[PredicateHolder(0)])
            .unwrap();
    }
}

fn logical_definition() -> PredicateDefinition {
    use crate::predicate_logic::*;
    let mut definition = definition();
    definition.logic.existentials.push(Existential {
        name: "used".into(),
        ty: LogicType::Usize,
        default: None,
    });
    definition.logic.constraints.push(LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
            },
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Word(7),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::LessEqual(0, 1),
            },
        ],
        root: 2,
    });
    definition
}
fn explicit_effect(value: u64) -> PredicateEffect {
    use crate::predicate_logic::*;
    PredicateEffect::FoldWithWitnesses {
        holder: PredicateHolder(0),
        bindings: vec![binding(0)],
        witnesses: WitnessArguments {
            arguments: vec![],
            inputs: vec![],
            values: vec![(
                0,
                LogicExpression {
                    nodes: vec![LogicNode {
                        ty: LogicType::Usize,
                        kind: LogicNodeKind::Word(value),
                    }],
                    root: 0,
                },
            )],
        },
    }
}
#[test]
fn checked_witnesses_are_saved_and_replayed_not_accepted_as_assumptions() {
    let input = state();
    let definition = logical_definition();
    let evidence = transfer_predicate(&input, &definition, 7, &explicit_effect(6)).unwrap();
    check_predicate_evidence(&input, &evidence).unwrap();
    let instance = evidence.output.predicates.get(&PredicateHolder(0)).unwrap();
    assert_eq!(instance.logical_witnesses.len(), 1);
    assert_eq!(instance.logic_scope.unwrap().instance, 0);
    assert_eq!(evidence.output.next_predicate_scope, 1);
    let mut forged = evidence.clone();
    forged.effect = explicit_effect(8);
    assert!(check_predicate_evidence(&input, &forged).is_err());
    assert_eq!(input.next_predicate_scope, 0);
    assert!(input.predicates.is_empty());
    assert!(transfer_predicate(&input, &definition, 7, &explicit_effect(8)).is_err());
}
#[test]
fn equal_witness_values_do_not_reuse_refolded_instance_identity() {
    let definition = logical_definition();
    let first = transfer_predicate(&state(), &definition, 7, &explicit_effect(6))
        .unwrap()
        .output;
    let first_scope = first.predicates[&PredicateHolder(0)].logic_scope.unwrap();
    let open = transfer_predicate(
        &first,
        &definition,
        7,
        &PredicateEffect::UnfoldInPlace {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        open.predicates[&PredicateHolder(0)]
            .logic_scope
            .unwrap()
            .opening,
        1
    );
    let next = transfer_predicate(&open, &definition, 7, &explicit_effect(6))
        .unwrap()
        .output;
    let next_scope = next.predicates[&PredicateHolder(0)].logic_scope.unwrap();
    assert_ne!(first_scope.instance, next_scope.instance);
    assert_eq!(
        first.predicates[&PredicateHolder(0)].logical_witnesses,
        next.predicates[&PredicateHolder(0)].logical_witnesses
    );
}
#[test]
fn witness_values_cannot_create_missing_representation_authority() {
    let mut input = state();
    let id = binding(0).permission;
    let AbstractValue::Permission(permission) = input.values.get_mut(&id).unwrap() else {
        panic!()
    };
    permission.mark_consumed();
    let snapshot = input.clone();
    assert_eq!(
        transfer_predicate(&input, &logical_definition(), 7, &explicit_effect(6)),
        Err(PredicateError::MissingAuthority)
    );
    assert_eq!(input, snapshot);
}
#[test]
fn stale_or_untyped_witness_observations_cannot_pass_direct_transfer() {
    use crate::predicate_logic::*;
    let mut effect = explicit_effect(6);
    let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
        unreachable!()
    };
    witnesses.values[0].1.nodes[0].kind = LogicNodeKind::Observe {
        resource: 0,
        offset: 0,
        access: VirMemoryAccess::core_u64(),
        time: ObservationTime::Current,
    };
    // A hand-built definition has no canonical observation layout; initialized
    // bytes and a caller-supplied access cannot replace independent typing.
    assert!(transfer_predicate(&state(), &logical_definition(), 7, &effect).is_err());
}
#[test]
fn exhausted_opening_scope_cannot_restore_consumed_permissions() {
    let definition = logical_definition();
    let mut input = transfer_predicate(&state(), &definition, 7, &explicit_effect(6))
        .unwrap()
        .output;
    input
        .predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .logic_scope
        .as_mut()
        .unwrap()
        .opening = u64::MAX;
    let snapshot = input.clone();
    assert_eq!(
        transfer_predicate(
            &input,
            &definition,
            7,
            &PredicateEffect::UnfoldInPlace {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
            }
        ),
        Err(PredicateError::Budget)
    );
    assert_eq!(input, snapshot);
}

#[test]
fn opened_input_is_consumed_by_refold_and_cannot_cross_instances() {
    use crate::predicate_logic::*;
    let definition = logical_definition();
    let sealed = transfer_predicate(&state(), &definition, 7, &explicit_effect(6))
        .unwrap()
        .output;
    let open = transfer_predicate(
        &sealed,
        &definition,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 20,
        },
    )
    .unwrap()
    .output;
    let mut effect = explicit_effect(0);
    let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
        unreachable!()
    };
    witnesses.inputs = vec![(
        LogicType::Usize,
        WitnessInput::Opened {
            action: 20,
            holder: 0,
            binder: 0,
        },
    )];
    witnesses.values[0].1.nodes[0].kind = LogicNodeKind::Binder(LogicBinder::Parameter(0));
    let evidence = transfer_predicate(&open, &definition, 7, &effect).unwrap();
    check_predicate_evidence(&open, &evidence).unwrap();
    let reopened = transfer_predicate(
        &evidence.output,
        &definition,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 21,
        },
    )
    .unwrap()
    .output;
    assert!(transfer_predicate(&reopened, &definition, 7, &effect).is_err());
    for (action, holder, binder) in [(19, 0, 0), (20, 1, 0), (20, 0, 1)] {
        let mut bad = effect.clone();
        let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut bad else {
            unreachable!()
        };
        witnesses.inputs[0].1 = WitnessInput::Opened {
            action,
            holder,
            binder,
        };
        assert!(transfer_predicate(&open, &definition, 7, &bad).is_err());
    }
    assert_eq!(
        open.predicates[&PredicateHolder(0)].opening_action,
        Some(20)
    );
}

#[test]
fn finish_retires_opened_witness_access_with_the_instance() {
    let definition = logical_definition();
    let sealed = transfer_predicate(&state(), &definition, 7, &explicit_effect(6))
        .unwrap()
        .output;
    let open = transfer_predicate(
        &sealed,
        &definition,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 20,
        },
    )
    .unwrap()
    .output;
    let freed = instruction(
        &open,
        VirInstruction::Free {
            pointer: binding(0).pointer,
            permission: binding(0).permission,
        },
    );
    assert!(freed.all_obligations_proven());
    let retired = transfer_predicate(
        freed.state(),
        &definition,
        7,
        &PredicateEffect::Finish {
            holder: PredicateHolder(0),
        },
    )
    .unwrap()
    .output;
    assert!(!retired.predicates.contains_key(&PredicateHolder(0)));
    let mut replacement = state();
    replacement.next_predicate_scope = retired.next_predicate_scope;
    let mut effect = explicit_effect(6);
    let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
        unreachable!()
    };
    witnesses.inputs = vec![(
        crate::predicate_logic::LogicType::Usize,
        crate::predicate_logic::WitnessInput::Opened {
            action: 20,
            holder: 0,
            binder: 0,
        },
    )];
    witnesses.values[0].1.nodes[0].kind = crate::predicate_logic::LogicNodeKind::Binder(
        crate::predicate_logic::LogicBinder::Parameter(0),
    );
    assert!(transfer_predicate(&replacement, &definition, 7, &effect).is_err());
}

#[test]
fn call_boundaries_freshen_hidden_symbols_without_losing_correlations() {
    use crate::predicate_logic::*;
    let mut definition = logical_definition();
    definition.logic.existentials.push(Existential {
        name: "same".into(),
        ty: LogicType::Usize,
        default: Some(LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
            }],
            root: 0,
        }),
    });
    let mut input = state();
    input
        .define_value(
            VirValueId::new(90),
            AbstractValue::U64(U64Interval::new(2, 6).unwrap()),
        )
        .unwrap();
    let mut effect = explicit_effect(0);
    let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
        unreachable!()
    };
    witnesses.inputs = vec![(LogicType::Usize, WitnessInput::Scalar(VirValueId::new(90)))];
    witnesses.values[0].1.nodes[0].kind = LogicNodeKind::Binder(LogicBinder::Parameter(0));
    let caller = transfer_predicate(&input, &definition, 7, &effect)
        .unwrap()
        .output;
    let mapping = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(7),
    };
    let (frame, callee) = enter_predicate_call(&caller, &[mapping]).unwrap();
    let before = &caller.predicates[&PredicateHolder(0)];
    let inside = &callee.predicates[&PredicateHolder(7)];
    assert_ne!(before.logic_scope, inside.logic_scope);
    assert_ne!(before.logical_witnesses[0], inside.logical_witnesses[0]);
    assert_eq!(inside.logical_witnesses[0], inside.logical_witnesses[1]);
    assert_eq!(
        before.resources[0].allocation,
        inside.resources[0].allocation
    );
    assert_eq!(
        before.resources[0].permission,
        inside.resources[0].permission
    );
    let returned = frame.resume(&callee, &[mapping]).unwrap();
    let after = &returned.predicates[&PredicateHolder(0)];
    assert_ne!(after.logic_scope, inside.logic_scope);
    assert_ne!(after.logic_scope, before.logic_scope);
    assert_eq!(after.logical_witnesses[0], after.logical_witnesses[1]);
    assert_eq!(
        before.resources[0].allocation,
        after.resources[0].allocation
    );
    let mut exhausted = caller.clone();
    exhausted.next_predicate_scope = u64::MAX;
    assert!(matches!(
        enter_predicate_call(&exhausted, &[mapping]),
        Err(PredicateError::Budget)
    ));
    assert_eq!(
        exhausted.predicates[&PredicateHolder(0)].logic_scope,
        before.logic_scope
    );
}

#[test]
fn symbolic_predicate_arguments_survive_opening_but_do_not_alias_foreign_ssa() {
    use crate::predicate_logic::*;
    let mut definition = logical_definition();
    definition.logic.parameters.push(LogicParameter {
        position: 1,
        name: "limit".into(),
        ty: LogicType::Usize,
    });
    let mut input = state();
    input
        .define_value(
            VirValueId::new(90),
            AbstractValue::U64(U64Interval::new(2, 6).unwrap()),
        )
        .unwrap();
    let mut effect = explicit_effect(6);
    let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
        unreachable!()
    };
    witnesses.inputs = vec![(LogicType::Usize, WitnessInput::Scalar(VirValueId::new(90)))];
    witnesses.arguments = vec![LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Usize,
            kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
        }],
        root: 0,
    }];
    let mut arguments = witnesses.clone();
    arguments.values.clear();
    let sealed = transfer_predicate(&input, &definition, 7, &effect)
        .unwrap()
        .output;
    let open = transfer_predicate(
        &sealed,
        &definition,
        7,
        &PredicateEffect::WithArguments {
            holder: PredicateHolder(0),
            arguments: arguments.clone(),
            effect: Box::new(PredicateEffect::UnfoldNamed {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
                action: 20,
            }),
        },
    )
    .unwrap()
    .output;
    open.check_predicate_arguments(&definition, PredicateHolder(0), &arguments)
        .unwrap();
    let map = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(7),
    };
    let (frame, callee) = enter_predicate_call(&sealed, &[map]).unwrap();
    let returned = frame.resume(&callee, &[map]).unwrap();
    // A captured foreign SSA symbol is not related to the current SSA number
    // until an ordinary call-summary adapter proves that relationship.
    assert!(
        returned
            .check_predicate_arguments(&definition, PredicateHolder(0), &arguments)
            .is_err()
    );
    let mut wrong = arguments;
    wrong.arguments[0].nodes[0].kind = LogicNodeKind::Word(9);
    assert!(
        sealed
            .check_predicate_arguments(&definition, PredicateHolder(0), &wrong)
            .is_err()
    );
}

#[test]
fn logical_argument_check_follows_the_actual_carrier_when_unfold_renames_holder() {
    let definition = logical_definition();
    let sealed = transfer_predicate(&state(), &definition, 7, &explicit_effect(6))
        .unwrap()
        .output;
    let effect = PredicateEffect::WithArguments {
        holder: PredicateHolder(9),
        arguments: Default::default(),
        effect: Box::new(PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(9),
            bindings: vec![binding(0)],
            action: 20,
        }),
    };
    let evidence = transfer_predicate(&sealed, &definition, 7, &effect).unwrap();
    check_predicate_evidence(&sealed, &evidence).unwrap();
    assert!(!evidence.output.predicates.contains_key(&PredicateHolder(0)));
    assert!(!evidence.output.predicates[&PredicateHolder(9)].is_folded());
}

// This invariant cannot be represented by the legacy single-field bounds:
// the current cell must still equal the immutable witness captured at fold.
fn snapshot_equality_definition() -> PredicateDefinition {
    use crate::predicate_logic::*;
    let mut def = definition();
    def.scalar_constraints.clear();
    def.logic_observations
        .insert((0, 0, VirMemoryAccess::core_u64()), LogicType::U64);
    let observation = LogicNode {
        ty: LogicType::U64,
        kind: LogicNodeKind::Observe {
            resource: 0,
            offset: 0,
            access: VirMemoryAccess::core_u64(),
            time: ObservationTime::Current,
        },
    };
    def.logic.existentials.push(Existential {
        name: "saved".into(),
        ty: LogicType::U64,
        default: Some(LogicExpression {
            nodes: vec![observation.clone()],
            root: 0,
        }),
    });
    def.logic.constraints.push(LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::U64,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
            },
            observation,
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Equal(0, 1),
            },
        ],
        root: 2,
    });
    def
}

#[test]
fn sealed_logic_is_rechecked_without_recomputing_default_witnesses() {
    let def = snapshot_equality_definition();
    let sealed = transfer_predicate(
        &state(),
        &def,
        7,
        &PredicateEffect::Fold {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        sealed.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let mut changed = sealed.clone();
    changed
        .allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .record_scalar_content(
            ByteRange::new(0, 8).unwrap(),
            VirMemoryAccess::core_u64(),
            AbstractValue::U64(U64Interval::exact(1)),
        );
    let before = changed.clone();
    assert_eq!(
        changed.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    assert_eq!(
        changed.check_predicate_boundary(&[PredicateHolder(0)]),
        Err(PredicateError::UnprovedRepresentation)
    );
    assert_eq!(
        changed.export_predicate_interface(&def, &[binding(0)]),
        Err(PredicateError::UnprovedRepresentation)
    );
    assert_eq!(
        changed, before,
        "failed ABI export must not expose the consumed carrier"
    );
    assert!(matches!(
        enter_predicate_call(
            &changed,
            &[PredicateCallBinding {
                caller: PredicateHolder(0),
                callee: PredicateHolder(1),
            }]
        ),
        Err(PredicateError::UnprovedRepresentation)
    ));
    assert!(
        matches!(
            enter_predicate_call(&changed, &[]),
            Err(PredicateError::UnprovedRepresentation)
        ),
        "a violated untransferred snapshot is still a call-boundary obligation"
    );
    assert_eq!(changed, before);
    let (frame, empty_callee) = enter_predicate_call(&sealed, &[]).unwrap();
    assert!(empty_callee.predicate_instances().is_empty());
    let resumed = frame.resume(&empty_callee, &[]).unwrap();
    assert_eq!(
        resumed, sealed,
        "untransferred valid snapshots remain in their caller scope"
    );
    let transfer = instruction(
        &changed,
        VirInstruction::Constant {
            result: VirValue {
                id: VirValueId::new(90),
                ty: VirType::U64,
            },
            value: crate::VirConstant::U64(0),
        },
    );
    assert!(transfer.obligations().iter().any(|o| matches!(
        o.kind(),
        crate::ResourceObligationKind::PredicateInvariantPreserved { holder: 0 }
    ) && o.status()
        == crate::ObligationStatus::Unknown));
    assert_eq!(
        changed.predicates[&PredicateHolder(0)].logical_witnesses,
        sealed.predicates[&PredicateHolder(0)].logical_witnesses
    );
}

#[test]
fn current_unknown_memory_does_not_alias_the_fold_snapshot() {
    let def = snapshot_equality_definition();
    let mut input = state();
    input
        .allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .record_scalar_content(
            ByteRange::new(0, 8).unwrap(),
            VirMemoryAccess::core_u64(),
            AbstractValue::U64(U64Interval::new(0, 8).unwrap()),
        );
    let before = input.clone();
    assert_eq!(
        transfer_predicate(
            &input,
            &def,
            7,
            &PredicateEffect::Fold {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
            },
        ),
        Err(PredicateError::UnprovedRepresentation),
        "equal intervals without an observation identity cannot prove snapshot equality"
    );
    assert_eq!(input, before);
}

#[test]
fn logical_observation_loan_exclusion_is_typed_and_range_sensitive() {
    use crate::predicate_logic::*;
    for (ty, width) in [(LogicType::U64, 8), (LogicType::Bool, 1)] {
        let mut def = snapshot_equality_definition();
        // Only the observation footprint matters for this compatibility check.
        def.logic.constraints = vec![LogicExpression {
            nodes: vec![LogicNode {
                ty,
                kind: LogicNodeKind::Observe {
                    resource: 0,
                    offset: 0,
                    access: VirMemoryAccess::core_u64(),
                    time: ObservationTime::Current,
                },
            }],
            root: 0,
        }];
        for (kind, start, end, accepted) in [
            (crate::VirLoanKind::Mutable, 0, width, false),
            (crate::VirLoanKind::Mutable, width, 16, true),
            (crate::VirLoanKind::Shared, 0, width, true),
        ] {
            let mut input = state();
            input
                .define_loan(
                    VirLoanId::new(0),
                    AbstractLoan::new(
                        AbstractProvenance::Known(AbstractAllocationId::new(0)),
                        ByteRange::new(start, end).unwrap(),
                        kind,
                        crate::VirBorrowRegionId::new(0),
                        None,
                        LoanActivity::Active,
                    )
                    .with_footprint(Some(MemoryFootprint {
                        provenance: AbstractProvenance::Known(AbstractAllocationId::new(0)),
                        access: VirMemoryAccess::core_u64(),
                        stride_bytes: width,
                        range: AbstractByteRange::Exact(ByteRange::new(start, end).unwrap()),
                        envelope: ByteRange::new(start, end).unwrap(),
                    })),
                )
                .unwrap();
            assert_eq!(
                input
                    .predicate_loans_compatible(
                        &def,
                        0,
                        AbstractProvenance::Known(AbstractAllocationId::new(0)),
                        None
                    )
                    .is_ok(),
                accepted
            );
            let loan = input.loan(VirLoanId::new(0)).unwrap().clone();
            *input.loan_mut(VirLoanId::new(0)).unwrap() = loan.with_footprint(None);
            assert_eq!(
                input.predicate_loans_compatible(
                    &def,
                    0,
                    AbstractProvenance::Known(AbstractAllocationId::new(0)),
                    None,
                ),
                Err(PredicateError::Borrowed),
                "a conservative envelope cannot substitute for an actual footprint",
            );
        }
    }
}

#[test]
fn cfg_edges_preserve_logical_snapshots_only_through_actual_value_aliases() {
    use crate::predicate_logic::*;
    let mut def = logical_definition();
    def.logic.parameters.push(LogicParameter {
        position: 1,
        name: "limit".into(),
        ty: LogicType::Usize,
    });
    let mut input = state();
    for id in [90, 91] {
        input
            .define_value(
                VirValueId::new(id),
                AbstractValue::U64(U64Interval::new(2, 6).unwrap()),
            )
            .unwrap();
    }
    let mut effect = explicit_effect(6);
    let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
        unreachable!()
    };
    witnesses.inputs = vec![(LogicType::Usize, WitnessInput::Scalar(VirValueId::new(90)))];
    witnesses.arguments = vec![LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Usize,
            kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
        }],
        root: 0,
    }];
    let mut arguments = witnesses.clone();
    arguments.values.clear();
    let sealed = transfer_predicate(&input, &def, 7, &effect).unwrap().output;
    let project = |state: &ResourceState, source, target| {
        let renames = [
            (VirValueId::new(0), VirValueId::new(0)),
            (VirValueId::new(1), VirValueId::new(1)),
            (VirValueId::new(source), VirValueId::new(target)),
        ];
        let mut projected = state.project_cfg_edge(&renames);
        for (source, target) in renames {
            projected
                .define_value(target, *state.value(source).unwrap())
                .unwrap();
        }
        projected
    };
    let mut renamed = project(&sealed, 90, 100);
    arguments.inputs[0].1 = WitnessInput::Scalar(VirValueId::new(100));
    renamed
        .check_predicate_arguments(&def, PredicateHolder(0), &arguments)
        .unwrap();
    assert_eq!(
        renamed.predicates[&PredicateHolder(0)].logical_parameters,
        sealed.predicates[&PredicateHolder(0)].logical_parameters
    );
    renamed = project(&renamed, 100, 101);
    arguments.inputs[0].1 = WitnessInput::Scalar(VirValueId::new(101));
    renamed
        .check_predicate_arguments(&def, PredicateHolder(0), &arguments)
        .unwrap();

    // An unrelated input with the same interval now occupies the old SSA
    // number. The old code compared Local(scope, 90) to itself and accepted it.
    let reused = project(&sealed, 91, 90);
    arguments.inputs[0].1 = WitnessInput::Scalar(VirValueId::new(90));
    assert!(
        reused
            .check_predicate_arguments(&def, PredicateHolder(0), &arguments)
            .is_err()
    );
    assert_eq!(
        reused.predicates[&PredicateHolder(0)].logical_parameters,
        sealed.predicates[&PredicateHolder(0)].logical_parameters
    );

    // Dropping an alias cannot regain it on a later edge by reusing its name.
    renamed
        .define_value(
            VirValueId::new(91),
            AbstractValue::U64(U64Interval::new(2, 6).unwrap()),
        )
        .unwrap();
    let dropped = project(&renamed, 91, 90);
    assert!(
        dropped
            .check_predicate_arguments(&def, PredicateHolder(0), &arguments)
            .is_err()
    );
}

#[test]
fn historical_memory_coordinates_preserve_unknown_snapshots_until_the_origin_is_lost() {
    let def = snapshot_equality_definition();
    let cell = ByteRange::new(0, 8).unwrap();
    let access = VirMemoryAccess::core_u64();
    let allocation = AbstractAllocationId::new(0);
    let mut input = state();
    input
        .allocation_mut(allocation)
        .unwrap()
        .record_scalar_content(
            cell,
            access,
            AbstractValue::U64(U64Interval::new(0, 8).unwrap()),
        );
    input.seed_scalar_origins();
    let origin = input
        .allocation(allocation)
        .unwrap()
        .scalar_origin(cell, access)
        .unwrap();
    let sealed = transfer_predicate(
        &input,
        &def,
        7,
        &PredicateEffect::Fold {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        sealed.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let mut rewritten = sealed.clone();
    rewritten
        .allocation_mut(allocation)
        .unwrap()
        .record_scalar_content(
            cell,
            access,
            AbstractValue::U64(U64Interval::new(0, 8).unwrap()),
        );
    assert_eq!(
        rewritten.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    // A canonical store from the same historical input can re-establish the
    // relation; interval equality by itself cannot do so.
    rewritten
        .allocation_mut(allocation)
        .unwrap()
        .set_scalar_origin(cell, access, origin);
    assert_eq!(
        rewritten.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    rewritten
        .allocation_mut(allocation)
        .unwrap()
        .set_scalar_origin(cell, access, origin.add(1).unwrap());
    assert_eq!(
        rewritten.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    // Merely forgetting memory contents also removes the identity, despite
    // retaining live ownership and initialized bytes.
    let mut forgotten = sealed.clone();
    forgotten
        .allocation_mut(allocation)
        .unwrap()
        .forget_scalar_contents(cell);
    assert_eq!(
        forgotten.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
}

#[test]
fn historical_parameter_origins_connect_derived_actuals_without_ssa_number_aliases() {
    use crate::predicate_logic::*;
    let mut def = logical_definition();
    def.logic.parameters.push(LogicParameter {
        position: 1,
        name: "limit".into(),
        ty: LogicType::Usize,
    });
    let mut input = state();
    input
        .define_value(
            VirValueId::new(90),
            AbstractValue::U64(U64Interval::new(2, 6).unwrap()),
        )
        .unwrap();
    input.seed_parameter_origins(crate::VirFunctionId::new(1), &[VirValueId::new(90)]);
    let origin = input.word_origin(VirValueId::new(90)).unwrap();
    let mut effect = explicit_effect(6);
    let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
        unreachable!()
    };
    witnesses.inputs = vec![(LogicType::Usize, WitnessInput::Scalar(VirValueId::new(90)))];
    witnesses.arguments = vec![LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            },
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Word(1),
            },
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Add(0, 1),
            },
        ],
        root: 2,
    }];
    let mut actual = WitnessArguments {
        inputs: vec![(LogicType::Usize, WitnessInput::Scalar(VirValueId::new(100)))],
        arguments: vec![LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            }],
            root: 0,
        }],
        values: vec![],
    };
    let mut sealed = transfer_predicate(&input, &def, 7, &effect).unwrap().output;
    sealed
        .define_value(
            VirValueId::new(100),
            AbstractValue::U64(U64Interval::new(3, 7).unwrap()),
        )
        .unwrap();
    // This derived value is not a CFG alias of parameter 90.
    sealed.set_word_origin(VirValueId::new(100), origin.add(1).unwrap());
    sealed
        .check_predicate_arguments(&def, PredicateHolder(0), &actual)
        .unwrap();
    sealed
        .define_value(
            VirValueId::new(101),
            AbstractValue::U64(U64Interval::new(3, 7).unwrap()),
        )
        .unwrap();
    actual.inputs[0].1 = WitnessInput::Scalar(VirValueId::new(101));
    assert!(
        sealed
            .check_predicate_arguments(&def, PredicateHolder(0), &actual)
            .is_err()
    );
    // A different function's identically numbered parameter is also distinct.
    let mut foreign = input.clone();
    foreign.seed_parameter_origins(crate::VirFunctionId::new(2), &[VirValueId::new(90)]);
    sealed.set_word_origin(
        VirValueId::new(101),
        foreign
            .word_origin(VirValueId::new(90))
            .unwrap()
            .add(1)
            .unwrap(),
    );
    assert!(
        sealed
            .check_predicate_arguments(&def, PredicateHolder(0), &actual)
            .is_err()
    );
    actual.inputs[0].1 = WitnessInput::Scalar(VirValueId::new(100));
    let mapping = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(8),
    };
    let (frame, callee) = enter_predicate_call(&sealed, &[mapping]).unwrap();
    let returned = frame.resume(&callee, &[mapping]).unwrap();
    assert!(
        returned
            .check_predicate_arguments(&def, PredicateHolder(0), &actual)
            .is_err(),
        "an internal frame without scalar ABI mapping cannot import caller origins as local facts"
    );
}

#[test]
fn local_refold_rebinds_opened_historical_values_without_recapturing_memory() {
    use crate::predicate_logic::*;
    for projected in [false, true] {
        let mut def = snapshot_equality_definition();
        if projected {
            def.projected_witnesses.insert(0);
            // Equality must be checked by the projection adapter even without a
            // user-written equality constraint.
            def.logic.constraints.clear();
        }
        let mut input = state();
        let id = AbstractAllocationId::new(0);
        let bytes = ByteRange::new(0, 8).unwrap();
        let access = VirMemoryAccess::core_u64();
        input.allocation_mut(id).unwrap().record_scalar_content(
            bytes,
            access,
            AbstractValue::U64(U64Interval::new(0, 8).unwrap()),
        );
        input.seed_scalar_origins();
        let original = input
            .allocation(id)
            .unwrap()
            .scalar_origin(bytes, access)
            .unwrap();
        let folded = transfer_predicate(
            &input,
            &def,
            7,
            &PredicateEffect::Fold {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
            },
        )
        .unwrap()
        .output;
        let opened = transfer_predicate(
            &folded,
            &def,
            7,
            &PredicateEffect::UnfoldNamed {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
                action: 20,
            },
        )
        .unwrap()
        .output;
        let refold = PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses: WitnessArguments {
                arguments: vec![],
                inputs: vec![(
                    LogicType::U64,
                    WitnessInput::Opened {
                        action: 20,
                        holder: 0,
                        binder: 0,
                    },
                )],
                values: vec![(
                    0,
                    LogicExpression {
                        nodes: vec![LogicNode {
                            ty: LogicType::U64,
                            kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                        }],
                        root: 0,
                    },
                )],
            },
        };
        let evidence = transfer_predicate(&opened, &def, 7, &refold).unwrap();
        check_predicate_evidence(&opened, &evidence).unwrap();
        assert_ne!(
            evidence.output.predicates[&PredicateHolder(0)].logic_scope,
            folded.predicates[&PredicateHolder(0)].logic_scope
        );
        assert_eq!(
            evidence.output.closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
        let mut changed = opened.clone();
        changed.allocation_mut(id).unwrap().record_scalar_content(
            bytes,
            access,
            AbstractValue::U64(U64Interval::new(1, 9).unwrap()),
        );
        changed.allocation_mut(id).unwrap().set_scalar_origin(
            bytes,
            access,
            original.add(1).unwrap(),
        );
        assert_eq!(
            transfer_predicate(&changed, &def, 7, &refold).unwrap_err(),
            PredicateError::UnprovedRepresentation
        );
        // Refold may instead deliberately choose the new default. That is a new
        // witness, unlike the stale opened binder used above.
        assert!(
            transfer_predicate(
                &changed,
                &def,
                7,
                &PredicateEffect::Fold {
                    holder: PredicateHolder(0),
                    bindings: vec![binding(0)],
                }
            )
            .is_ok()
        );
    }
}

#[test]
fn logical_precondition_export_checks_parameters_before_exposing_permissions() {
    use crate::predicate_logic::*;
    let mut def = definition();
    def.logic.parameters.push(LogicParameter {
        name: "limit".into(),
        position: 1,
        ty: LogicType::Usize,
    });
    let args = |value| WitnessArguments {
        inputs: vec![],
        values: vec![],
        arguments: vec![LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Word(value),
            }],
            root: 0,
        }],
    };
    let mut sealed = transfer_predicate(
        &state(),
        &def,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses: args(7),
        },
    )
    .unwrap()
    .output;
    let before = sealed.clone();
    assert!(
        sealed
            .predicate_storage_interface_with_arguments(
                &def,
                &[binding(0)],
                &[None],
                None,
                &args(8)
            )
            .is_err()
    );
    assert_eq!(sealed, before);
    assert!(
        sealed
            .predicate_storage_interface_with_arguments(
                &def,
                &[binding(0)],
                &[None],
                None,
                &WitnessArguments::default()
            )
            .is_err()
    );
    assert_eq!(sealed, before);
    sealed
        .predicate_storage_interface_with_arguments(&def, &[binding(0)], &[None], None, &args(7))
        .unwrap();
    assert!(sealed.predicates.is_empty());
    sealed
        .predicate_storage_interface_with_arguments(
            &def,
            &[binding(0)],
            &[None],
            Some((PredicateHolder(9), true)),
            &args(7),
        )
        .unwrap();
    sealed
        .check_predicate_arguments(&def, PredicateHolder(9), &args(7))
        .unwrap();
    assert!(
        sealed
            .check_predicate_arguments(&def, PredicateHolder(9), &args(8))
            .is_err()
    );
}

#[test]
fn postcondition_snapshots_ignore_reused_ssa_numbers_and_leave_no_scratch_values() {
    use crate::predicate_logic::*;
    let mut def = definition();
    def.logic.parameters.push(LogicParameter {
        name: "limit".into(),
        position: 1,
        ty: LogicType::Usize,
    });
    let mut entry = state();
    let original = VirValueId::new(90);
    entry
        .define_value(
            original,
            AbstractValue::U64(U64Interval::new(2, 6).unwrap()),
        )
        .unwrap();
    entry.seed_parameter_origins(crate::VirFunctionId::new(1), &[original]);
    let term = LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Usize,
            kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
        }],
        root: 0,
    };
    let actual = WitnessArguments {
        inputs: vec![(LogicType::Usize, WitnessInput::Scalar(original))],
        arguments: vec![term.clone()],
        values: vec![],
    };
    let closed = transfer_predicate(
        &entry,
        &def,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses: actual.clone(),
        },
    )
    .unwrap()
    .output;
    let mut current = closed.project_cfg_edge(&[
        (VirValueId::new(0), VirValueId::new(0)),
        (VirValueId::new(1), VirValueId::new(1)),
    ]);
    for id in [VirValueId::new(0), VirValueId::new(1)] {
        current
            .define_value(id, *closed.value(id).unwrap())
            .unwrap();
    }
    current
        .define_value(original, AbstractValue::U64(U64Interval::exact(99)))
        .unwrap();
    let before = current.clone();
    let metadata = WitnessArguments {
        inputs: vec![(LogicType::Usize, WitnessInput::Scalar(0u32))],
        arguments: vec![term],
        values: vec![],
    };
    current
        .with_predicate_input_snapshots(&entry, &[original], &metadata, |candidate, inputs, _| {
            let mut actual = actual.clone();
            actual.inputs[0].1 = WitnessInput::Scalar(inputs[0]);
            candidate.check_predicate_arguments(&def, PredicateHolder(0), &actual)
        })
        .unwrap();
    assert_eq!(
        current, before,
        "temporary values and origins must not escape"
    );
    assert!(
        current
            .check_predicate_arguments(&def, PredicateHolder(0), &actual)
            .is_err()
    );
    let result = current.with_predicate_input_snapshots(
        &entry,
        &[original],
        &metadata,
        |candidate, _, _| {
            candidate.predicates.clear();
            Err(PredicateError::InvalidBinding)
        },
    );
    assert_eq!(result, Err(PredicateError::InvalidBinding));
    assert_eq!(current, before, "failed post export is atomic");
    assert!(
        current
            .with_predicate_input_snapshots(
                &entry,
                &[binding(0).permission],
                &metadata,
                |_, _, _| Ok(())
            )
            .is_err()
    );
    assert_eq!(
        current, before,
        "entry permission cannot become a scalar snapshot"
    );
}

#[test]
fn boolean_snapshots_follow_cfg_aliases_and_remain_foreign_after_calls() {
    use crate::predicate_logic::*;
    let mut def = logical_definition();
    def.logic.parameters.push(LogicParameter {
        position: 1,
        name: "limit".into(),
        ty: LogicType::Bool,
    });
    let mut input = state();
    for id in [90, 91] {
        input
            .define_value(
                VirValueId::new(id),
                AbstractValue::Bool(crate::verifier::AbstractBool::Unknown),
            )
            .unwrap();
    }
    let mut effect = explicit_effect(6);
    let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
        unreachable!()
    };
    witnesses.inputs = vec![(LogicType::Bool, WitnessInput::Scalar(VirValueId::new(90)))];
    witnesses.arguments = vec![LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Bool,
            kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
        }],
        root: 0,
    }];
    let mut arguments = witnesses.clone();
    arguments.values.clear();
    let sealed = transfer_predicate(&input, &def, 7, &effect).unwrap().output;
    let project = |state: &ResourceState, source, target| {
        let renames = [
            (VirValueId::new(0), VirValueId::new(0)),
            (VirValueId::new(1), VirValueId::new(1)),
            (VirValueId::new(source), VirValueId::new(target)),
        ];
        let mut projected = state.project_cfg_edge(&renames);
        for (source, target) in renames {
            projected
                .define_value(target, *state.value(source).unwrap())
                .unwrap();
        }
        projected
    };
    let mut renamed = project(&sealed, 90, 100);
    arguments.inputs[0].1 = WitnessInput::Scalar(VirValueId::new(100));
    renamed
        .check_predicate_arguments(&def, PredicateHolder(0), &arguments)
        .unwrap();
    assert_eq!(
        renamed.predicates[&PredicateHolder(0)].logical_parameters,
        sealed.predicates[&PredicateHolder(0)].logical_parameters
    );
    renamed = project(&renamed, 100, 101);
    arguments.inputs[0].1 = WitnessInput::Scalar(VirValueId::new(101));
    renamed
        .check_predicate_arguments(&def, PredicateHolder(0), &arguments)
        .unwrap();

    // An unrelated unknown Boolean now occupies the old SSA
    // number. The old code compared Local(scope, 90) to itself and accepted it.
    let reused = project(&sealed, 91, 90);
    arguments.inputs[0].1 = WitnessInput::Scalar(VirValueId::new(90));
    assert!(
        reused
            .check_predicate_arguments(&def, PredicateHolder(0), &arguments)
            .is_err()
    );
    assert_eq!(
        reused.predicates[&PredicateHolder(0)].logical_parameters,
        sealed.predicates[&PredicateHolder(0)].logical_parameters
    );

    // Dropping an alias cannot regain it on a later edge by reusing its name.
    renamed
        .define_value(
            VirValueId::new(91),
            AbstractValue::Bool(crate::verifier::AbstractBool::Unknown),
        )
        .unwrap();
    let dropped = project(&renamed, 91, 90);
    assert!(
        dropped
            .check_predicate_arguments(&def, PredicateHolder(0), &arguments)
            .is_err()
    );

    let mapping = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(8),
    };
    let (frame, callee) = enter_predicate_call(&sealed, &[mapping]).unwrap();
    let returned = frame.resume(&callee, &[mapping]).unwrap();
    assert!(
        returned
            .check_predicate_arguments(&def, PredicateHolder(0), &arguments)
            .is_err()
    );
}

#[test]
fn boolean_postcondition_snapshots_keep_entry_identity_and_clean_up() {
    use crate::predicate_logic::*;
    let mut def = definition();
    def.logic.parameters.push(LogicParameter {
        name: "limit".into(),
        position: 1,
        ty: LogicType::Bool,
    });
    let mut entry = state();
    let original = VirValueId::new(90);
    entry
        .define_value(
            original,
            AbstractValue::Bool(crate::verifier::AbstractBool::Unknown),
        )
        .unwrap();
    entry.seed_parameter_origins(crate::VirFunctionId::new(1), &[original]);
    let term = LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Bool,
            kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
        }],
        root: 0,
    };
    let actual = WitnessArguments {
        inputs: vec![(LogicType::Bool, WitnessInput::Scalar(original))],
        arguments: vec![term.clone()],
        values: vec![],
    };
    let closed = transfer_predicate(
        &entry,
        &def,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses: actual.clone(),
        },
    )
    .unwrap()
    .output;
    let mut current = closed.project_cfg_edge(&[
        (VirValueId::new(0), VirValueId::new(0)),
        (VirValueId::new(1), VirValueId::new(1)),
    ]);
    for id in [VirValueId::new(0), VirValueId::new(1)] {
        current
            .define_value(id, *closed.value(id).unwrap())
            .unwrap();
    }
    current
        .define_value(
            original,
            AbstractValue::Bool(crate::verifier::AbstractBool::Unknown),
        )
        .unwrap();
    let before = current.clone();
    let metadata = WitnessArguments {
        inputs: vec![(LogicType::Bool, WitnessInput::Scalar(0u32))],
        arguments: vec![term],
        values: vec![],
    };
    current
        .with_predicate_input_snapshots(&entry, &[original], &metadata, |candidate, inputs, _| {
            let mut actual = actual.clone();
            actual.inputs[0].1 = WitnessInput::Scalar(inputs[0]);
            candidate.check_predicate_arguments(&def, PredicateHolder(0), &actual)
        })
        .unwrap();
    assert_eq!(
        current, before,
        "temporary values and origins must not escape"
    );
    assert!(
        current
            .check_predicate_arguments(&def, PredicateHolder(0), &actual)
            .is_err()
    );
    let result = current.with_predicate_input_snapshots(
        &entry,
        &[original],
        &metadata,
        |candidate, _, _| {
            candidate.predicates.clear();
            Err(PredicateError::InvalidBinding)
        },
    );
    assert_eq!(result, Err(PredicateError::InvalidBinding));
    assert_eq!(current, before, "failed post export is atomic");
    assert!(
        current
            .with_predicate_input_snapshots(
                &entry,
                &[binding(0).permission],
                &metadata,
                |_, _, _| Ok(())
            )
            .is_err()
    );
    assert_eq!(
        current, before,
        "entry permission cannot become a scalar snapshot"
    );

    let mut foreign_entry = entry.clone();
    foreign_entry.seed_parameter_origins(crate::VirFunctionId::new(2), &[original]);
    assert!(
        current
            .with_predicate_input_snapshots(
                &foreign_entry,
                &[original],
                &metadata,
                |candidate, inputs, _| {
                    let mut actual = actual.clone();
                    actual.inputs[0].1 = WitnessInput::Scalar(inputs[0]);
                    candidate.check_predicate_arguments(&def, PredicateHolder(0), &actual)
                }
            )
            .is_err()
    );
    assert_eq!(current, before);
    let mapping = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(8),
    };
    let (frame, callee) = enter_predicate_call(&closed, &[mapping]).unwrap();
    let mut returned = frame.resume(&callee, &[mapping]).unwrap();
    assert!(
        returned
            .with_predicate_input_snapshots(
                &entry,
                &[original],
                &metadata,
                |candidate, inputs, _| {
                    let mut actual = actual.clone();
                    actual.inputs[0].1 = WitnessInput::Scalar(inputs[0]);
                    candidate.check_predicate_arguments(&def, PredicateHolder(0), &actual)
                }
            )
            .is_err(),
        "internal frames without scalar ABI mapping cannot restore local entry identity"
    );
    let mut replaced = closed.clone();
    *replaced.value_mut(original).unwrap() =
        AbstractValue::Bool(crate::verifier::AbstractBool::Unknown);
    assert!(
        replaced
            .check_predicate_arguments(&def, PredicateHolder(0), &actual)
            .is_err()
    );
    for expected in [false, true] {
        let mut narrowed = closed.clone();
        assert!(narrowed.narrow_bool_value(original, expected));
        let frozen = narrowed.predicates[&PredicateHolder(0)]
            .logical_parameters
            .clone();
        narrowed
            .check_predicate_arguments(&def, PredicateHolder(0), &actual)
            .unwrap();
        let before = narrowed.clone();
        narrowed
            .with_predicate_input_snapshots(
                &entry,
                &[original],
                &metadata,
                |candidate, inputs, _| {
                    let mut actual = actual.clone();
                    actual.inputs[0].1 = WitnessInput::Scalar(inputs[0]);
                    candidate.check_predicate_arguments(&def, PredicateHolder(0), &actual)
                },
            )
            .unwrap();
        assert_eq!(narrowed, before);
        assert_eq!(
            narrowed.predicates[&PredicateHolder(0)].logical_parameters,
            frozen
        );
        assert!(!narrowed.narrow_bool_value(original, !expected));
        assert_eq!(
            narrowed, before,
            "contradictory narrowing must not change the state"
        );
        let mut conflicting = narrowed.clone();
        let alias = VirValueId::new(91);
        conflicting
            .define_value(
                alias,
                AbstractValue::Bool(if expected {
                    crate::verifier::AbstractBool::False
                } else {
                    crate::verifier::AbstractBool::True
                }),
            )
            .unwrap();
        conflicting.set_bool_origin(alias, conflicting.bool_origin(original).unwrap());
        assert!(
            conflicting
                .check_predicate_arguments(&def, PredicateHolder(0), &actual)
                .is_err(),
            "inconsistent source facts must not select a convenient truth value"
        );
    }
    assert!(returned.narrow_bool_value(original, true));
    assert!(
        returned
            .check_predicate_arguments(&def, PredicateHolder(0), &actual)
            .is_err(),
        "a captured foreign origin cannot use local path facts"
    );
}

#[test]
fn boolean_opened_witness_refold_rebinds_only_local_entry_identity() {
    use crate::predicate_logic::*;
    let term = |binder| LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Bool,
            kind: LogicNodeKind::Binder(binder),
        }],
        root: 0,
    };
    let mut def = definition();
    def.logic.parameters.push(LogicParameter {
        name: "flag".into(),
        position: 1,
        ty: LogicType::Bool,
    });
    def.logic.existentials.push(Existential {
        name: "saved".into(),
        ty: LogicType::Bool,
        default: Some(term(LogicBinder::Parameter(0))),
    });
    def.logic.constraints.push(LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Equal(0, 1),
            },
        ],
        root: 2,
    });
    let input_id = VirValueId::new(90);
    let mut input = state();
    input
        .define_value(
            input_id,
            AbstractValue::Bool(crate::verifier::AbstractBool::Unknown),
        )
        .unwrap();
    input.seed_parameter_origins(crate::VirFunctionId::new(1), &[input_id]);
    let arguments = WitnessArguments {
        inputs: vec![(LogicType::Bool, WitnessInput::Scalar(input_id))],
        arguments: vec![term(LogicBinder::Parameter(0))],
        values: vec![],
    };
    let folded = transfer_predicate(
        &input,
        &def,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses: arguments.clone(),
        },
    )
    .unwrap()
    .output;
    let opened = transfer_predicate(
        &folded,
        &def,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 20,
        },
    )
    .unwrap()
    .output;
    let mut explicit = arguments;
    explicit.inputs.push((
        LogicType::Bool,
        WitnessInput::Opened {
            action: 20,
            holder: 0,
            binder: 0,
        },
    ));
    explicit.values.push((0, term(LogicBinder::Parameter(1))));
    let refold = PredicateEffect::FoldWithWitnesses {
        holder: PredicateHolder(0),
        bindings: vec![binding(0)],
        witnesses: explicit,
    };
    let evidence = transfer_predicate(&opened, &def, 7, &refold).unwrap();
    check_predicate_evidence(&opened, &evidence).unwrap();
    assert_eq!(
        evidence.output.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let mut changed = opened.clone();
    *changed.value_mut(input_id).unwrap() =
        AbstractValue::Bool(crate::verifier::AbstractBool::Unknown);
    assert!(transfer_predicate(&changed, &def, 7, &refold).is_err());
}

#[test]
fn boolean_memory_coordinates_require_actual_same_source_writes() {
    let mut def = snapshot_equality_definition();
    let access = VirMemoryAccess {
        ty: crate::VirTypeId::new(90),
        layout: crate::VirLayoutId::new(90),
    };
    def.logic_observations.clear();
    def.logic_observations
        .insert((0, 0, access), crate::predicate_logic::LogicType::Bool);
    def.logic.existentials[0].ty = crate::predicate_logic::LogicType::Bool;
    for expr in def.logic.existentials[0]
        .default
        .iter_mut()
        .chain(def.logic.constraints.iter_mut())
    {
        for node in &mut expr.nodes {
            node.ty = crate::predicate_logic::LogicType::Bool;
            if let crate::predicate_logic::LogicNodeKind::Observe { access: old, .. } =
                &mut node.kind
            {
                *old = access;
            }
        }
    }
    let cell = ByteRange::new(0, 1).unwrap();
    let allocation = AbstractAllocationId::new(0);
    let mut input = state();
    input
        .allocation_mut(allocation)
        .unwrap()
        .record_scalar_content(
            cell,
            access,
            AbstractValue::Bool(crate::verifier::AbstractBool::Unknown),
        );
    input.seed_scalar_origins();
    let origin = input
        .allocation(allocation)
        .unwrap()
        .bool_origin(cell, access)
        .unwrap();
    let sealed = transfer_predicate(
        &input,
        &def,
        7,
        &PredicateEffect::Fold {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        sealed.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let mut rewritten = sealed.clone();
    rewritten
        .allocation_mut(allocation)
        .unwrap()
        .record_scalar_content(
            cell,
            access,
            AbstractValue::Bool(crate::verifier::AbstractBool::Unknown),
        );
    assert_eq!(
        rewritten.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    // A canonical store from the same historical input can re-establish the
    // relation; abstract-value equality by itself cannot do so.
    rewritten
        .allocation_mut(allocation)
        .unwrap()
        .set_bool_origin(cell, access, origin);
    assert_eq!(
        rewritten.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    rewritten
        .allocation_mut(allocation)
        .unwrap()
        .set_bool_origin(
            cell,
            access,
            BoolOrigin::Parameter {
                function: crate::VirFunctionId::new(9),
                value: VirValueId::new(90),
            },
        );
    assert_eq!(
        rewritten.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    // Merely forgetting memory contents also removes the identity, despite
    // retaining live ownership and initialized bytes.
    let mut forgotten = sealed.clone();
    forgotten
        .allocation_mut(allocation)
        .unwrap()
        .forget_scalar_contents(cell);
    assert_eq!(
        forgotten.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    let mut path = sealed.clone();
    let loaded = VirValueId::new(90);
    path.define_value(
        loaded,
        AbstractValue::Bool(crate::verifier::AbstractBool::Unknown),
    )
    .unwrap();
    path.set_bool_origin(loaded, origin);
    assert!(path.narrow_bool_value(loaded, true));
    let snapshots = path.predicates[&PredicateHolder(0)]
        .logical_witnesses
        .clone();
    // A concrete write is equal to the old snapshot only on the path where
    // a genuine load of that immutable source established its truth value.
    path.allocation_mut(allocation)
        .unwrap()
        .record_scalar_content(
            cell,
            access,
            AbstractValue::Bool(crate::verifier::AbstractBool::True),
        );
    assert_eq!(
        path.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_eq!(
        path.predicates[&PredicateHolder(0)].logical_witnesses,
        snapshots
    );
    *path.value_mut(loaded).unwrap() = AbstractValue::Bool(crate::verifier::AbstractBool::True);
    assert_eq!(
        path.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)],
        "the same concrete value without its load origin cannot refine a saved snapshot"
    );
}

#[test]
fn interface_import_cannot_rechoose_pure_existential_defaults() {
    use crate::predicate_logic::*;
    let mut def = definition();
    def.logic.existentials.push(Existential {
        name: "hidden".into(),
        ty: LogicType::U64,
        default: Some(LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::U64,
                kind: LogicNodeKind::Word(0),
            }],
            root: 0,
        }),
    });
    let mut input = state();
    input
        .import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            false,
        )
        .unwrap();
    let first = input.predicates[&PredicateHolder(0)].logical_witnesses[0].clone();
    let LogicValue::Word(word) = &first.value else {
        panic!("typed hidden word");
    };
    assert_eq!((word.lower, word.upper), (0, u64::MAX));
    assert!(matches!(
        word.terms.keys().next(),
        Some(logic::ObservationAtom::Existential { binder: 0, .. })
    ));
    assert_ne!(first.value, LogicValue::Word(AffineValue::exact(0)));
    input
        .export_predicate_interface(&def, &[binding(0)])
        .unwrap();
    input
        .import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(1),
            &Default::default(),
            false,
        )
        .unwrap();
    assert_ne!(
        first,
        input.predicates[&PredicateHolder(1)].logical_witnesses[0]
    );
    let mut missing = state();
    let Some(AbstractValue::Permission(permission)) = missing.value_mut(binding(0).permission)
    else {
        unreachable!()
    };
    permission.mark_consumed();
    let before = missing.clone();
    assert!(
        missing
            .import_predicate_interface_with_arguments(
                &def,
                &[binding(0)],
                PredicateHolder(0),
                &Default::default(),
                false,
            )
            .is_err()
    );
    assert_eq!(
        missing, before,
        "abstract binders cannot supply missing authority"
    );
}

#[test]
fn projected_witness_cells_block_writable_loans_even_without_constraints() {
    for (ty, width) in [
        (crate::predicate_logic::LogicType::U64, 8),
        (crate::predicate_logic::LogicType::Bool, 1),
    ] {
        let mut def = snapshot_equality_definition();
        def.logic.existentials[0].ty = ty;
        def.logic.existentials[0].default.as_mut().unwrap().nodes[0].ty = ty;
        def.logic.constraints.clear();
        def.projected_witnesses.insert(0);
        for (kind, start, end, allowed) in [
            (crate::VirLoanKind::Mutable, 0, width, false),
            (crate::VirLoanKind::Mutable, width, 16, true),
            (crate::VirLoanKind::Shared, 0, width, true),
        ] {
            let mut input = state();
            input
                .define_loan(
                    VirLoanId::new(0),
                    AbstractLoan::new(
                        AbstractProvenance::Known(AbstractAllocationId::new(0)),
                        ByteRange::new(start, end).unwrap(),
                        kind,
                        crate::VirBorrowRegionId::new(0),
                        None,
                        LoanActivity::Active,
                    )
                    .with_footprint(Some(MemoryFootprint {
                        provenance: AbstractProvenance::Known(AbstractAllocationId::new(0)),
                        access: VirMemoryAccess::core_u64(),
                        stride_bytes: width,
                        range: AbstractByteRange::Exact(ByteRange::new(start, end).unwrap()),
                        envelope: ByteRange::new(start, end).unwrap(),
                    })),
                )
                .unwrap();
            assert_eq!(
                input
                    .predicate_loans_compatible(
                        &def,
                        0,
                        AbstractProvenance::Known(AbstractAllocationId::new(0)),
                        None
                    )
                    .is_ok(),
                allowed
            );
            let loan = input.loan(VirLoanId::new(0)).unwrap().clone();
            *input.loan_mut(VirLoanId::new(0)).unwrap() = loan.with_footprint(None);
            assert_eq!(
                input.predicate_loans_compatible(
                    &def,
                    0,
                    AbstractProvenance::Known(AbstractAllocationId::new(0)),
                    None,
                ),
                Err(PredicateError::Borrowed),
                "a conservative envelope cannot substitute for an actual footprint",
            );
        }
        // A non-projected local witness is a snapshot, not an implicit invariant
        // requiring its source field to stay unchanged.
        def.projected_witnesses.clear();
        let mut input = state();
        input
            .define_loan(
                VirLoanId::new(0),
                AbstractLoan::new(
                    AbstractProvenance::Known(AbstractAllocationId::new(0)),
                    ByteRange::new(0, 8).unwrap(),
                    crate::VirLoanKind::Mutable,
                    crate::VirBorrowRegionId::new(0),
                    None,
                    LoanActivity::Active,
                )
                .with_footprint(Some(MemoryFootprint {
                    provenance: AbstractProvenance::Known(AbstractAllocationId::new(0)),
                    access: VirMemoryAccess::core_u64(),
                    stride_bytes: 8,
                    range: AbstractByteRange::Exact(ByteRange::new(0, 8).unwrap()),
                    envelope: ByteRange::new(0, 8).unwrap(),
                })),
            )
            .unwrap();
        assert!(
            input
                .predicate_loans_compatible(
                    &def,
                    0,
                    AbstractProvenance::Known(AbstractAllocationId::new(0)),
                    None
                )
                .is_ok()
        );
    }
}

#[test]
fn current_unknown_boolean_memory_does_not_alias_the_fold_snapshot() {
    let mut def = snapshot_equality_definition();
    let access = VirMemoryAccess {
        ty: crate::VirTypeId::new(90),
        layout: crate::VirLayoutId::new(90),
    };
    def.logic_observations.clear();
    def.logic_observations
        .insert((0, 0, access), crate::predicate_logic::LogicType::Bool);
    def.logic.existentials[0].ty = crate::predicate_logic::LogicType::Bool;
    for expression in def.logic.existentials[0]
        .default
        .iter_mut()
        .chain(def.logic.constraints.iter_mut())
    {
        for node in &mut expression.nodes {
            node.ty = crate::predicate_logic::LogicType::Bool;
            if let crate::predicate_logic::LogicNodeKind::Observe { access: field, .. } =
                &mut node.kind
            {
                *field = access;
            }
        }
    }
    let mut input = state();
    input
        .allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .record_scalar_content(
            ByteRange::new(0, 1).unwrap(),
            access,
            AbstractValue::Bool(crate::verifier::AbstractBool::Unknown),
        );
    let before = input.clone();
    assert_eq!(
        transfer_predicate(
            &input,
            &def,
            7,
            &PredicateEffect::Fold {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
            },
        ),
        Err(PredicateError::UnprovedRepresentation),
        "equal intervals without an observation identity cannot prove snapshot equality"
    );
    assert_eq!(input, before);
}

#[test]
fn entry_projected_witnesses_capture_field_origins_before_sealing() {
    use crate::predicate_logic::*;
    for boolean in [false, true] {
        let mut def = snapshot_equality_definition();
        def.projected_witnesses.insert(0);
        let access = if boolean {
            VirMemoryAccess {
                ty: crate::VirTypeId::new(90),
                layout: crate::VirLayoutId::new(90),
            }
        } else {
            VirMemoryAccess::core_u64()
        };
        let ty = if boolean {
            LogicType::Bool
        } else {
            LogicType::U64
        };
        if boolean {
            def.logic_observations.clear();
            def.logic_observations.insert((0, 0, access), ty);
            def.logic.existentials[0].ty = ty;
            for expression in def.logic.existentials[0]
                .default
                .iter_mut()
                .chain(def.logic.constraints.iter_mut())
            {
                for node in &mut expression.nodes {
                    node.ty = ty;
                    if let LogicNodeKind::Observe { access: field, .. } = &mut node.kind {
                        *field = access;
                    }
                }
            }
        }
        let id = AbstractAllocationId::new(0);
        let range = ByteRange::new(0, if boolean { 1 } else { 8 }).unwrap();
        let mut input = state();
        input.allocation_mut(id).unwrap().clear_scalar_contents();
        let mut entry = input.clone();
        entry
            .predicate_storage_interface(
                &def,
                &[binding(0)],
                &[None],
                Some((PredicateHolder(0), true)),
            )
            .unwrap();
        assert_eq!(
            entry.closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
        let saved = entry.clone();
        entry.seed_scalar_origins();
        assert_eq!(
            entry, saved,
            "the final entry pass must not rebase captured fields"
        );

        // A checked return can capture the actual current cell. This is a
        // fresh snapshot, never the function-entry identity or an old value.
        let mut returned = input.clone();
        returned
            .import_predicate_interface(&def, &[binding(0)], PredicateHolder(0))
            .unwrap();
        assert_eq!(
            returned.closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
        let allocation = returned.allocation(id).unwrap();
        if boolean {
            assert!(matches!(
                allocation.bool_origin(range, access),
                Some(BoolOrigin::Snapshot(_))
            ));
            assert_ne!(
                allocation.bool_origin(range, access),
                entry.allocation(id).unwrap().bool_origin(range, access)
            );
        } else {
            assert!(matches!(
                allocation
                    .scalar_origin(range, access)
                    .map(|origin| origin.first.root),
                Some(ScalarOriginRoot::Snapshot(_))
            ));
            assert_ne!(
                allocation.scalar_origin(range, access),
                entry.allocation(id).unwrap().scalar_origin(range, access)
            );
        }

        let unknown = if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::new(0, u64::MAX).unwrap())
        };
        entry
            .allocation_mut(id)
            .unwrap()
            .record_scalar_content(range, access, unknown);
        assert_eq!(
            entry.closed_predicate_checks(),
            vec![(PredicateHolder(0), false)],
            "overwriting with the same abstract value must invalidate the snapshot"
        );

        let mut missing = input;
        missing.values.remove(&binding(0).permission);
        let before = missing.clone();
        assert!(
            missing
                .predicate_storage_interface(
                    &def,
                    &[binding(0)],
                    &[None],
                    Some((PredicateHolder(0), true)),
                )
                .is_err()
        );
        assert_eq!(
            missing, before,
            "entry origins cannot survive failed authority import"
        );
    }
}

#[test]
fn repeated_entry_seeding_preserves_refined_and_copied_origins() {
    let mut input = state();
    let id = AbstractAllocationId::new(0);
    let access = VirMemoryAccess::core_u64();
    let cell = ByteRange::new(0, 8).unwrap();
    input.allocation_mut(id).unwrap().record_scalar_content(
        cell,
        access,
        AbstractValue::U64(U64Interval::new(0, 8).unwrap()),
    );
    input.seed_scalar_origins();
    let origin = input
        .allocation(id)
        .unwrap()
        .scalar_origin(cell, access)
        .unwrap();
    let allocation = input.allocation_mut(id).unwrap();
    allocation.record_scalar_content(
        cell,
        access,
        AbstractValue::U64(U64Interval::new(1, 7).unwrap()),
    );
    allocation.set_scalar_origin(cell, access, origin);
    let copy = ByteRange::new(8, 16).unwrap();
    allocation.mark_initialized(copy).unwrap();
    allocation.mark_valid(copy).unwrap();
    allocation.record_scalar_content(
        copy,
        access,
        AbstractValue::U64(U64Interval::new(1, 7).unwrap()),
    );
    allocation.set_scalar_origin(copy, access, origin);
    input.seed_scalar_origins();
    for range in [cell, copy] {
        assert_eq!(
            input.allocation(id).unwrap().scalar_origin(range, access),
            Some(origin)
        );
    }
}

#[test]
fn logical_cfg_aliases_fan_out_intersect_and_never_reappear() {
    use crate::predicate_logic::*;
    for boolean in [false, true] {
        let mut def = logical_definition();
        let ty = if boolean {
            LogicType::Bool
        } else {
            LogicType::Usize
        };
        let value = if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::new(2, 6).unwrap())
        };
        def.logic.parameters.push(LogicParameter {
            position: 1,
            name: "limit".into(),
            ty,
        });
        let mut input = state();
        for id in [90, 91] {
            input.define_value(VirValueId::new(id), value).unwrap();
        }
        let mut effect = explicit_effect(6);
        let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
            unreachable!()
        };
        witnesses.inputs = vec![(ty, WitnessInput::Scalar(VirValueId::new(90)))];
        witnesses.arguments = vec![LogicExpression {
            nodes: vec![LogicNode {
                ty,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            }],
            root: 0,
        }];
        let mut arguments = witnesses.clone();
        arguments.values.clear();
        let sealed = transfer_predicate(&input, &def, 7, &effect).unwrap().output;
        let project = |state: &ResourceState, pairs: &[(u32, u32)]| {
            let renames = [(0, 0), (1, 1)]
                .into_iter()
                .chain(pairs.iter().copied())
                .map(|(a, b)| (VirValueId::new(a), VirValueId::new(b)))
                .collect::<Vec<_>>();
            let mut output = state.project_cfg_edge(&renames);
            for (source, target) in renames {
                output.values.insert(target, *state.value(source).unwrap());
            }
            output
        };
        let matches = |state: &ResourceState, id| {
            let mut actual = arguments.clone();
            actual.inputs[0].1 = WitnessInput::Scalar(VirValueId::new(id));
            state
                .check_predicate_arguments(&def, PredicateHolder(0), &actual)
                .is_ok()
        };
        let fanout = project(&sealed, &[(90, 100), (90, 101)]);
        assert!(matches(&fanout, 100));
        assert!(matches(&fanout, 101));
        assert_eq!(
            fanout.predicates[&PredicateHolder(0)].logical_parameters,
            sealed.predicates[&PredicateHolder(0)].logical_parameters
        );
        // Even if edge admission rejects duplicate targets, the projection
        // primitive itself must never choose one input's identity arbitrarily.
        for pairs in [[(90, 100), (91, 100)], [(91, 100), (90, 100)]] {
            assert!(!matches(&project(&sealed, &pairs), 100));
        }
        let other = project(&sealed, &[(90, 100), (91, 101)]);
        assert!(fanout.same_resource_facts(&other));
        assert!(fanout.same_loop_partition(&other));
        use crate::verifier::guarded::{
            ConditionalResourceState, GuardedReduction, GuardedStateLimits,
        };
        let left = ConditionalResourceState::singleton(fanout.clone());
        let right = ConditionalResourceState::singleton(other.clone());
        let limits = GuardedStateLimits {
            max_cases: 8,
            max_guard_atoms: 8,
        };
        for guarded in [
            left.join(&right, limits, GuardedReduction::Selective)
                .unwrap(),
            left.join_loop(&right, limits).unwrap(),
            left.widen(&right, limits).unwrap(),
        ] {
            assert_eq!(guarded.cases().len(), 1);
            assert!(matches(&guarded.cases()[0], 100));
            assert!(!matches(&guarded.cases()[0], 101));
        }
        let joined = fanout.join(&other).unwrap();
        assert_eq!(joined, other.join(&fanout).unwrap());
        assert!(matches(&joined, 100));
        assert!(!matches(&joined, 101));
        assert_eq!(
            joined.predicates[&PredicateHolder(0)].resources,
            fanout.predicates[&PredicateHolder(0)].resources
        );
        assert!(joined.covers_cfg_case(&fanout));
        assert!(!fanout.covers_cfg_case(&joined));
        let widened = fanout.widen(&joined).unwrap();
        assert!(matches(&widened, 100));
        assert!(!matches(&widened, 101));
        assert!(!matches(&project(&widened, &[(101, 90)]), 90));
        // A closed binder may be renamed when its real live aliases agree;
        // opening and resource responsibility cannot be changed by that rule.
        let mut renamed = joined.clone();
        renamed
            .predicates
            .get_mut(&PredicateHolder(0))
            .unwrap()
            .logic_scope
            .as_mut()
            .unwrap()
            .instance += 1;
        let normalized = joined.join(&renamed).unwrap();
        assert!(matches(&normalized, 100));
        assert!(!matches(&normalized, 101));
        assert!(normalized.covers_cfg_case(&joined));
        assert!(normalized.covers_cfg_case(&renamed));
        for change in 1..4 {
            let mut incompatible = joined.clone();
            let instance = incompatible
                .predicates
                .get_mut(&PredicateHolder(0))
                .unwrap();
            match change {
                0 => instance.logic_scope.as_mut().unwrap().instance += 1,
                1 => instance.opening_action = Some(99),
                2 => instance.folded = !instance.folded,
                _ => instance.resources[0].carrier = None,
            }
            assert_eq!(
                joined.join(&incompatible),
                Err(ResourceJoinError::PredicateStateMismatch)
            );
            assert_eq!(
                joined.widen(&incompatible),
                Err(ResourceJoinError::PredicateStateMismatch)
            );
        }
        let pairs = (0..=MAX_PREDICATE_LOCAL_ALIASES as u32)
            .map(|index| (90, 1000 + index))
            .collect::<Vec<_>>();
        let overflow = project(&sealed, &pairs);
        assert!(
            overflow.predicates[&PredicateHolder(0)]
                .logical_local_aliases
                .is_empty()
        );
        assert!(!matches(&overflow, 1000));
        assert_eq!(
            overflow.predicates[&PredicateHolder(0)].resources,
            fanout.predicates[&PredicateHolder(0)].resources
        );
    }
}

#[test]
fn word_replacement_retires_snapshot_identity_but_narrowing_preserves_it() {
    use crate::predicate_logic::*;
    let id = VirValueId::new(90);
    let other = VirValueId::new(91);
    let range = U64Interval::new(2, 6).unwrap();
    for historical in [false, true] {
        let mut def = logical_definition();
        def.logic.parameters.push(LogicParameter {
            position: 1,
            name: "limit".into(),
            ty: LogicType::Usize,
        });
        let mut input = state();
        for value in [id, other] {
            input
                .define_value(value, AbstractValue::U64(range))
                .unwrap();
        }
        input.set_word_expression(id, AffineExpression::identity(id));
        if historical {
            input.seed_parameter_origins(crate::VirFunctionId::new(1), &[id, other]);
        }
        let mut effect = explicit_effect(6);
        let PredicateEffect::FoldWithWitnesses { witnesses, .. } = &mut effect else {
            unreachable!()
        };
        witnesses.inputs = vec![(LogicType::Usize, WitnessInput::Scalar(id))];
        witnesses.arguments = vec![LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            }],
            root: 0,
        }];
        let mut actual = witnesses.clone();
        actual.values.clear();
        let sealed = transfer_predicate(&input, &def, 7, &effect).unwrap().output;
        let saved = sealed.predicates[&PredicateHolder(0)]
            .logical_parameters
            .clone();
        let mut narrowed = sealed.clone();
        narrowed.narrow_word_interval(id, U64Interval::new(3, 5).unwrap());
        assert_eq!(narrowed.word_origin(id), sealed.word_origin(id));
        assert_eq!(narrowed.word_expression(id), sealed.word_expression(id));
        narrowed
            .check_predicate_arguments(&def, PredicateHolder(0), &actual)
            .unwrap();
        assert_eq!(
            narrowed.predicates[&PredicateHolder(0)].logical_parameters,
            saved
        );
        let mut changed = sealed.clone();
        *changed.value_mut(id).unwrap() = AbstractValue::U64(range);
        assert!(changed.word_origin(id).is_none());
        assert!(changed.word_expression(id).is_none());
        assert!(
            changed
                .check_predicate_arguments(&def, PredicateHolder(0), &actual)
                .is_err()
        );
        assert_eq!(
            changed.predicates[&PredicateHolder(0)].logical_parameters,
            saved
        );
        assert_eq!(
            changed.predicates[&PredicateHolder(0)].resources,
            sealed.predicates[&PredicateHolder(0)].resources
        );
        if historical {
            let target = VirValueId::new(100);
            for unknown in [false, true] {
                let mut source = sealed.clone();
                if unknown {
                    *source.value_mut(other).unwrap() = AbstractValue::U64(range);
                }
                for edges in [
                    [(id, target), (other, target)],
                    [(other, target), (id, target)],
                ] {
                    let projected = source.project_cfg_edge(&edges);
                    assert!(
                        projected.word_origin(target).is_none(),
                        "conflicting or missing origins cannot select a historical input"
                    );
                }
            }
            let same = sealed.project_cfg_edge(&[(id, target), (id, target)]);
            assert_eq!(same.word_origin(target), sealed.word_origin(id));
        }
    }
}

#[test]
fn replacement_cannot_reimport_retired_relations_through_paths_or_expressions() {
    use crate::verifier::relation::{
        RelationComparison,
        difference::{DifferenceLimits, DifferencePremise, word},
    };
    let mut state = ResourceState::new();
    let ids = [VirValueId::new(0), VirValueId::new(1), VirValueId::new(2)];
    for id in ids {
        state
            .define_value(id, AbstractValue::U64(U64Interval::new(0, 8).unwrap()))
            .unwrap();
    }
    state.seed_parameter_origins(crate::VirFunctionId::new(1), &ids);
    let origin = state.word_origin(ids[0]).unwrap();
    state.set_word_origin(ids[1], origin);
    state.set_word_expression(ids[1], AffineExpression::identity(ids[0]));
    state.set_word_expression(ids[2], AffineExpression::identity(ids[2]));
    let retired = PathFact::comparison(crate::VirIntegerPredicate::LessThan, ids[0], ids[2]);
    let retained = PathFact::comparison(crate::VirIntegerPredicate::LessThan, ids[1], ids[2]);
    state.conjoin_path_fact(retired);
    state.conjoin_path_fact(retained);
    state.learn_relations(
        &[DifferencePremise::Compare {
            comparison: RelationComparison::LessThan,
            left: word(ids[0]),
            right: word(ids[2]),
        }],
        DifferenceLimits::default(),
    );
    let mut narrowed = state.clone();
    narrowed.narrow_word_interval(ids[0], U64Interval::new(1, 5).unwrap());
    assert_eq!(narrowed.path_condition(), state.path_condition());
    assert_eq!(
        narrowed.word_expression(ids[1]),
        state.word_expression(ids[1])
    );

    *state.value_mut(ids[0]).unwrap() = AbstractValue::U64(U64Interval::new(0, 8).unwrap());
    assert!(!state.path_condition().implies(retired));
    assert!(state.path_condition().implies(retained));
    assert!(state.word_expression(ids[1]).is_none());
    assert_eq!(
        state.word_expression(ids[2]),
        Some(AffineExpression::identity(ids[2]))
    );
    // The surviving copy still denotes the OLD entry input, without equating
    // it to the replacement or losing its independently established facts.
    assert_eq!(state.word_origin(ids[1]), Some(origin));
    assert!(state.word_origin(ids[0]).is_none());
    assert!(
        state
            .relations()
            .bounds()
            .all(|b| b.left != Some(ids[0]) && b.right != Some(ids[0]))
    );
    let boolean = VirValueId::new(3);
    state
        .define_value(boolean, AbstractValue::Bool(AbstractBool::True))
        .unwrap();
    state.conjoin_path_fact(PathFact::boolean(boolean, true));
    *state.value_mut(boolean).unwrap() = AbstractValue::Bool(AbstractBool::Unknown);
    assert!(
        !state
            .path_condition()
            .implies(PathFact::boolean(boolean, true))
    );
}

#[test]
fn comparison_witnesses_rebind_locally_and_freshen_across_internal_calls() {
    use crate::predicate_logic::*;
    let mut def = definition();
    def.logic.existentials.push(Existential {
        name: "saved".into(),
        ty: LogicType::Bool,
        default: None,
    });
    let mut input = state();
    let ids = [VirValueId::new(90), VirValueId::new(91)];
    for id in ids {
        input
            .define_value(id, AbstractValue::U64(U64Interval::new(0, 8).unwrap()))
            .unwrap();
    }
    input.seed_parameter_origins(crate::VirFunctionId::new(1), &ids);
    let effect = PredicateEffect::FoldWithWitnesses {
        holder: PredicateHolder(0),
        bindings: vec![binding(0)],
        witnesses: WitnessArguments {
            inputs: ids
                .iter()
                .map(|id| (LogicType::Usize, WitnessInput::Scalar(*id)))
                .collect(),
            arguments: vec![],
            values: vec![(
                0,
                LogicExpression {
                    nodes: vec![
                        LogicNode {
                            ty: LogicType::Usize,
                            kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                        },
                        LogicNode {
                            ty: LogicType::Usize,
                            kind: LogicNodeKind::Binder(LogicBinder::Parameter(1)),
                        },
                        LogicNode {
                            ty: LogicType::Bool,
                            kind: LogicNodeKind::Less(0, 1),
                        },
                    ],
                    root: 2,
                },
            )],
        },
    };
    let sealed = transfer_predicate(&input, &def, 7, &effect).unwrap().output;
    let open = transfer_predicate(
        &sealed,
        &def,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 20,
        },
    )
    .unwrap()
    .output;
    let refold = PredicateEffect::FoldWithWitnesses {
        holder: PredicateHolder(0),
        bindings: vec![binding(0)],
        witnesses: WitnessArguments {
            inputs: vec![(
                LogicType::Bool,
                WitnessInput::Opened {
                    action: 20,
                    holder: 0,
                    binder: 0,
                },
            )],
            arguments: vec![],
            values: vec![(
                0,
                LogicExpression {
                    nodes: vec![LogicNode {
                        ty: LogicType::Bool,
                        kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                    }],
                    root: 0,
                },
            )],
        },
    };
    let evidence = transfer_predicate(&open, &def, 7, &refold).unwrap();
    check_predicate_evidence(&open, &evidence).unwrap();
    let local = &evidence.output.predicates[&PredicateHolder(0)];
    let LogicValue::BoolComparison { left, right, .. } = &local.logical_witnesses[0].value else {
        panic!("comparison witness");
    };
    for atom in left.terms.keys().chain(right.terms.keys()) {
        assert!(
            matches!(atom, super::logic::ObservationAtom::Historical {scope, local:true, ..}
            if Some(*scope)==local.logic_scope)
        );
    }
    let binding = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(8),
    };
    let (frame, callee) = enter_predicate_call(&evidence.output, &[binding]).unwrap();
    let foreign = &callee.predicates[&PredicateHolder(8)].logical_witnesses[0].value;
    let LogicValue::BoolComparison { left, right, .. } = foreign else {
        panic!("comparison witness");
    };
    for atom in left.terms.keys().chain(right.terms.keys()) {
        assert!(matches!(
            atom,
            super::logic::ObservationAtom::Historical { local: false, .. }
        ));
    }
    assert_eq!(foreign.bool_equal(&local.logical_witnesses[0].value), None);
    let returned = frame.resume(&callee, &[binding]).unwrap();
    assert_eq!(
        returned.predicates[&PredicateHolder(0)].logical_witnesses[0]
            .value
            .bool_equal(&local.logical_witnesses[0].value),
        None
    );
}

#[test]
fn comparison_parameters_use_consistent_local_path_bounds_without_mutating_snapshots() {
    use crate::predicate_logic::*;
    let mut def = definition();
    def.logic.parameters.push(LogicParameter {
        name: "less".into(),
        position: 1,
        ty: LogicType::Bool,
    });
    let ids = [VirValueId::new(90), VirValueId::new(91)];
    let mut input = state();
    for id in ids {
        input
            .define_value(id, AbstractValue::U64(U64Interval::new(0, 8).unwrap()))
            .unwrap();
    }
    input.seed_parameter_origins(crate::VirFunctionId::new(1), &ids);
    let arguments = WitnessArguments {
        inputs: ids
            .iter()
            .map(|id| (LogicType::Usize, WitnessInput::Scalar(*id)))
            .collect(),
        values: vec![],
        arguments: vec![LogicExpression {
            nodes: vec![
                LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                },
                LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(1)),
                },
                LogicNode {
                    ty: LogicType::Bool,
                    kind: LogicNodeKind::Less(0, 1),
                },
            ],
            root: 2,
        }],
    };
    let sealed = transfer_predicate(
        &input,
        &def,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses: arguments.clone(),
        },
    )
    .unwrap()
    .output;
    let constant = |value| WitnessArguments {
        inputs: vec![],
        values: vec![],
        arguments: vec![LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Bool(value),
            }],
            root: 0,
        }],
    };
    assert!(
        sealed
            .check_predicate_arguments(&def, PredicateHolder(0), &constant(true))
            .is_err()
    );
    let saved = sealed.predicates[&PredicateHolder(0)]
        .logical_parameters
        .clone();
    for (a, b, expected) in [(1, 2, true), (7, 2, false)] {
        let mut path = sealed.clone();
        path.narrow_word_interval(ids[0], U64Interval::exact(a));
        path.narrow_word_interval(ids[1], U64Interval::exact(b));
        path.check_predicate_arguments(&def, PredicateHolder(0), &constant(expected))
            .unwrap();
        assert!(
            path.check_predicate_arguments(&def, PredicateHolder(0), &constant(!expected))
                .is_err()
        );
        assert_eq!(
            path.predicates[&PredicateHolder(0)].logical_parameters,
            saved
        );
        let mut lost = path.clone();
        *lost.value_mut(ids[0]).unwrap() = AbstractValue::U64(U64Interval::exact(a));
        assert!(
            lost.check_predicate_arguments(&def, PredicateHolder(0), &constant(expected))
                .is_err()
        );
        let mut conflict = path.clone();
        let alias = VirValueId::new(92);
        conflict
            .define_value(alias, AbstractValue::U64(U64Interval::exact(8 - a)))
            .unwrap();
        conflict.set_word_origin(alias, path.word_origin(ids[0]).unwrap());
        assert!(
            conflict
                .check_predicate_arguments(&def, PredicateHolder(0), &constant(expected))
                .is_err()
        );
    }
    let mapping = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(8),
    };
    let (frame, callee) = enter_predicate_call(&sealed, &[mapping]).unwrap();
    let mut returned = frame.resume(&callee, &[mapping]).unwrap();
    returned.narrow_word_interval(ids[0], U64Interval::exact(1));
    returned.narrow_word_interval(ids[1], U64Interval::exact(2));
    assert!(
        returned
            .check_predicate_arguments(&def, PredicateHolder(0), &constant(true))
            .is_err()
    );

    // Overlapping intervals do not prove a comparison. The established
    // relational fact must be translated through surviving origins instead.
    use crate::verifier::relation::{
        RelationComparison as C,
        difference::{DifferenceLimits, DifferencePremise, word},
    };
    for (premise, expected) in [
        (C::LessThan, [Some(true), Some(true), Some(false)]),
        (C::LessOrEqual, [None, Some(true), None]),
        (C::Equal, [Some(false), Some(true), Some(true)]),
        (C::NotEqual, [None, None, Some(false)]),
    ] {
        for (kind, expected) in [
            LogicNodeKind::Less(0, 1),
            LogicNodeKind::LessEqual(0, 1),
            LogicNodeKind::Equal(0, 1),
        ]
        .into_iter()
        .zip(expected)
        {
            let mut arguments = arguments.clone();
            arguments.arguments[0].nodes[2].kind = kind;
            let mut path = transfer_predicate(
                &input,
                &def,
                7,
                &PredicateEffect::FoldWithWitnesses {
                    holder: PredicateHolder(0),
                    bindings: vec![binding(0)],
                    witnesses: arguments,
                },
            )
            .unwrap()
            .output;
            let saved = path.predicates[&PredicateHolder(0)]
                .logical_parameters
                .clone();
            path.learn_relations(
                &[DifferencePremise::Compare {
                    comparison: premise,
                    left: word(ids[0]),
                    right: word(ids[1]),
                }],
                DifferenceLimits::default(),
            );
            for actual in [false, true] {
                assert_eq!(
                    path.check_predicate_arguments(&def, PredicateHolder(0), &constant(actual))
                        .is_ok(),
                    expected == Some(actual),
                    "{premise:?}, expected {expected:?}, actual {actual}"
                );
            }
            assert_eq!(
                path.predicates[&PredicateHolder(0)].logical_parameters,
                saved
            );
            // Replacement loses both relational facts and the snapshot alias.
            *path.value_mut(ids[0]).unwrap() = AbstractValue::U64(U64Interval::new(0, 8).unwrap());
            for actual in [false, true] {
                assert!(
                    path.check_predicate_arguments(&def, PredicateHolder(0), &constant(actual))
                        .is_err()
                );
            }
        }
    }
    // x != 4 leaves [0, 8] unchanged; only the established disequality
    // justifies a false equality argument. An equal numeric constant can
    // carry that fact without being an alias of x's historical symbol.
    let constant_id = VirValueId::new(93);
    let mut input = input.clone();
    input
        .define_value(constant_id, AbstractValue::U64(U64Interval::exact(4)))
        .unwrap();
    let mut literal = arguments.clone();
    literal.arguments[0].nodes[1].kind = LogicNodeKind::Word(4);
    literal.arguments[0].nodes[2].kind = LogicNodeKind::Equal(0, 1);
    let mut path = transfer_predicate(
        &input,
        &def,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses: literal,
        },
    )
    .unwrap()
    .output;
    path.learn_relations(
        &[DifferencePremise::Compare {
            comparison: C::NotEqual,
            left: word(ids[0]),
            right: word(constant_id),
        }],
        DifferenceLimits::default(),
    );
    assert_eq!(
        path.value(ids[0]),
        Some(&AbstractValue::U64(U64Interval::new(0, 8).unwrap()))
    );
    path.check_predicate_arguments(&def, PredicateHolder(0), &constant(false))
        .unwrap();
    assert!(
        path.check_predicate_arguments(&def, PredicateHolder(0), &constant(true))
            .is_err()
    );
    // The exact RHS was substituted by the literal 4 when the relation was
    // learned. Replacing that SSA slot cannot invalidate x != 4; replacing x
    // must still invalidate both the relation and its snapshot association.
    *path.value_mut(constant_id).unwrap() = AbstractValue::U64(U64Interval::exact(9));
    path.check_predicate_arguments(&def, PredicateHolder(0), &constant(false))
        .unwrap();
    *path.value_mut(ids[0]).unwrap() = AbstractValue::U64(U64Interval::exact(4));
    assert!(
        path.check_predicate_arguments(&def, PredicateHolder(0), &constant(false))
            .is_err()
    );
}

#[test]
fn abstract_packages_keep_constraint_facts_scoped_through_open_refold_and_calls() {
    use crate::predicate_logic::*;
    let mut def = definition();
    def.logic.existentials.push(Existential {
        name: "hidden".into(),
        ty: LogicType::U64,
        default: None,
    });
    def.logic.constraints.push(LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::U64,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
            },
            LogicNode {
                ty: LogicType::U64,
                kind: LogicNodeKind::Word(4),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::LessEqual(0, 1),
            },
        ],
        root: 2,
    });
    let mut sealed = state();
    sealed
        .import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            false,
        )
        .unwrap();
    assert_eq!(
        sealed.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let mapping = PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(8),
    };
    let (frame, callee) = enter_predicate_call(&sealed, &[mapping]).unwrap();
    assert_eq!(
        callee.closed_predicate_checks(),
        vec![(PredicateHolder(8), true)]
    );
    let returned = frame.resume(&callee, &[mapping]).unwrap();
    assert_eq!(
        returned.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_ne!(
        sealed.predicates[&PredicateHolder(0)].logical_witnesses,
        returned.predicates[&PredicateHolder(0)].logical_witnesses
    );
    // Copying a witness from another invocation cannot reuse this package's fact.
    let mut foreign = returned.clone();
    foreign
        .predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .logical_witnesses = sealed.predicates[&PredicateHolder(0)]
        .logical_witnesses
        .clone();
    assert_eq!(
        foreign.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    assert_eq!(
        transfer_predicate(
            &returned,
            &def,
            7,
            &PredicateEffect::UnfoldNamed {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
                action: 42,
            }
        ),
        Err(PredicateError::MissingHolder)
    );
    let opened = open_internal_named(&returned, &def, PredicateHolder(0), binding(10), 42);
    let explicit = WitnessArguments {
        inputs: vec![(
            LogicType::U64,
            WitnessInput::Opened {
                action: 42,
                holder: 0,
                binder: 0,
            },
        )],
        arguments: vec![],
        values: vec![(
            0,
            LogicExpression {
                nodes: vec![LogicNode {
                    ty: LogicType::U64,
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                }],
                root: 0,
            },
        )],
    };
    let effect = PredicateEffect::FoldWithWitnesses {
        holder: PredicateHolder(0),
        bindings: vec![binding(10)],
        witnesses: explicit.clone(),
    };
    let evidence = transfer_predicate(&opened, &def, 7, &effect).unwrap();
    check_predicate_evidence(&opened, &evidence).unwrap();
    assert_eq!(
        evidence.output.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let mut bad = explicit;
    bad.values[0].1.nodes[0].kind = LogicNodeKind::Word(5);
    assert!(
        transfer_predicate(
            &opened,
            &def,
            7,
            &PredicateEffect::FoldWithWitnesses {
                holder: PredicateHolder(0),
                bindings: vec![binding(10)],
                witnesses: bad,
            }
        )
        .is_err()
    );
    let mut occupied = opened.clone();
    assert_eq!(
        occupied.import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            false,
        ),
        Err(PredicateError::HolderOccupied)
    );
    assert_eq!(occupied, opened);
    // A local fold cannot create the hidden witness or assume this constraint.
    assert!(
        transfer_predicate(
            &state(),
            &def,
            7,
            &PredicateEffect::Fold {
                holder: PredicateHolder(0),
                bindings: vec![binding(10)],
            }
        )
        .is_err()
    );
}

#[test]
fn imported_constraint_facts_do_not_survive_unrelated_unknown_memory_writes() {
    use crate::predicate_logic::*;
    let mut def = definition();
    let access = VirMemoryAccess::core_u64();
    def.logic_observations
        .insert((0, 0, access), LogicType::U64);
    def.logic.existentials.push(Existential {
        name: "saved".into(),
        ty: LogicType::U64,
        default: None,
    });
    def.logic.constraints.push(LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::U64,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
            },
            LogicNode {
                ty: LogicType::U64,
                kind: LogicNodeKind::Observe {
                    resource: 0,
                    offset: 0,
                    access,
                    time: ObservationTime::Current,
                },
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::LessEqual(0, 1),
            },
        ],
        root: 2,
    });
    let mut imported = state();
    let id = AbstractAllocationId::new(0);
    let bytes = ByteRange::new(0, 8).unwrap();
    imported.allocation_mut(id).unwrap().record_scalar_content(
        bytes,
        access,
        AbstractValue::U64(U64Interval::new(0, 8).unwrap()),
    );
    imported
        .import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            true,
        )
        .unwrap();
    assert_eq!(
        imported.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    let origin = imported
        .allocation(id)
        .unwrap()
        .scalar_origin(bytes, access)
        .unwrap();
    imported.allocation_mut(id).unwrap().record_scalar_content(
        bytes,
        access,
        AbstractValue::U64(U64Interval::new(0, 8).unwrap()),
    );
    assert_eq!(
        imported.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    imported
        .allocation_mut(id)
        .unwrap()
        .set_scalar_origin(bytes, access, origin);
    assert_eq!(
        imported.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
}

#[test]
fn abstract_constraint_substitution_budget_is_shared_and_import_is_atomic() {
    use crate::predicate_logic::*;
    let mut expression = LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::U64,
            kind: LogicNodeKind::Word(0),
        }],
        root: 0,
    };
    for _ in 0..28 {
        let previous = expression.root;
        let literal = expression.nodes.len() as u32;
        expression.nodes.push(LogicNode {
            ty: LogicType::U64,
            kind: LogicNodeKind::Word(0),
        });
        expression.root = expression.nodes.len() as u32;
        expression.nodes.push(LogicNode {
            ty: LogicType::U64,
            kind: LogicNodeKind::Add(previous, literal),
        });
    }
    let previous = expression.root;
    let literal = expression.nodes.len() as u32;
    expression.nodes.push(LogicNode {
        ty: LogicType::U64,
        kind: LogicNodeKind::Word(0),
    });
    expression.root = expression.nodes.len() as u32;
    expression.nodes.push(LogicNode {
        ty: LogicType::Bool,
        kind: LogicNodeKind::Equal(previous, literal),
    });
    for count in [1, 32] {
        let mut def = definition();
        def.logic.constraints = vec![expression.clone(); count];
        assert!(
            def.logic
                .validate(&["p"], &|_, _, _, _| None, &|_, _| None)
                .is_ok()
        );
        let mut input = state();
        let before = input.clone();
        let result = input.import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            false,
        );
        if count == 1 {
            result.unwrap();
            assert_eq!(
                input.closed_predicate_checks(),
                vec![(PredicateHolder(0), true)]
            );
        } else {
            assert_eq!(result, Err(PredicateError::Budget));
            assert_eq!(input, before);
        }
    }
}

#[test]
fn borrowed_packages_preserve_hidden_choices_and_return_updated_logical_parameters() {
    use crate::predicate_logic::*;
    let mut def = definition();
    def.logic.parameters.push(LogicParameter {
        name: "limit".into(),
        position: 1,
        ty: LogicType::Usize,
    });
    def.logic.existentials.push(Existential {
        name: "used".into(),
        ty: LogicType::Usize,
        default: None,
    });
    def.logic.constraints.push(LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
            },
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::LessEqual(0, 1),
            },
        ],
        root: 2,
    });
    let word = |n| LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Usize,
            kind: LogicNodeKind::Word(n),
        }],
        root: 0,
    };
    let actual = |n| WitnessArguments {
        inputs: vec![],
        values: vec![],
        arguments: vec![word(n)],
    };
    let mut state = state();
    state
        .import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &actual(4),
            false,
        )
        .unwrap();
    let saved = state.predicates[&PredicateHolder(0)]
        .logical_witnesses
        .clone();
    let loan = crate::VirLoanId::new(9);
    let range = ByteRange::new(0, 16).unwrap();
    let effect = crate::VirLoanEffect {
        loan,
        kind: crate::VirLoanKind::Mutable,
        region: crate::VirBorrowRegionId::new(0),
        parent: None,
        source_pointer: binding(0).pointer,
        source_permission: binding(0).permission,
        reference: VirMemoryAccess::core_u64(),
        range: crate::VirLoanRange {
            start_bytes: 0,
            end_bytes: 16,
        },
        origin: crate::VirOriginId::new(0),
    };
    assert_eq!(
        state.prepare_predicate_borrow(effect, 16),
        Some(PredicateHolder(0))
    );
    let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
    state.values.insert(
        binding(2).pointer,
        *state.value(binding(0).pointer).unwrap(),
    );
    state.values.insert(
        binding(2).permission,
        AbstractValue::Permission(
            AbstractPermission::new(
                provenance,
                AbstractByteRange::Exact(range),
                AccessPermission::Write,
                FreeCapability::No,
            )
            .with_authority(PermissionAuthority::Loan(loan)),
        ),
    );
    state
        .define_loan(
            loan,
            AbstractLoan::new(
                provenance,
                range,
                crate::VirLoanKind::Mutable,
                crate::VirBorrowRegionId::new(0),
                None,
                LoanActivity::Active,
            )
            .with_authority(binding(2).permission)
            .with_footprint(Some(MemoryFootprint {
                provenance,
                access: VirMemoryAccess::core_u64(),
                stride_bytes: 8,
                range: AbstractByteRange::Exact(range),
                envelope: range,
            })),
        )
        .unwrap();
    state
        .seal_predicate_borrow(PredicateHolder(0), loan, binding(2))
        .unwrap();
    let child = *state
        .predicates
        .keys()
        .find(|holder| **holder != PredicateHolder(0))
        .unwrap();
    assert_ne!(state.predicates[&child].logical_witnesses, saved);
    state
        .check_predicate_arguments(&def, child, &actual(4))
        .unwrap();
    let opened = transfer_predicate(
        &state,
        &def,
        7,
        &PredicateEffect::UnfoldInPlace {
            holder: child,
            bindings: vec![binding(2)],
        },
    )
    .unwrap()
    .output;
    let mut updated = actual(8);
    updated.values.push((0, word(7)));
    let mut returned = transfer_predicate(
        &opened,
        &def,
        7,
        &PredicateEffect::FoldWithWitnesses {
            holder: child,
            bindings: vec![binding(2)],
            witnesses: updated,
        },
    )
    .unwrap()
    .output;
    assert_eq!(
        returned
            .prepare_predicate_restore(loan, binding(2))
            .unwrap(),
        Some(PredicateHolder(0))
    );
    returned
        .check_predicate_arguments(&def, PredicateHolder(0), &actual(8))
        .unwrap();
    assert!(
        returned
            .check_predicate_arguments(&def, PredicateHolder(0), &actual(4))
            .is_err()
    );
    assert!(
        returned
            .restore_predicate_lender(PredicateHolder(0), loan)
            .is_err()
    );
    assert!(
        matches!(returned.value(binding(0).permission), Some(AbstractValue::Permission(permission))
        if permission.availability() == PermissionAvailability::Consumed)
    );
    let Some(AbstractValue::Permission(permission)) = returned.value_mut(binding(2).permission)
    else {
        unreachable!()
    };
    permission.mark_consumed();
    returned
        .loan_mut(loan)
        .unwrap()
        .remove_authority(binding(2).permission);
    returned
        .loan_mut(loan)
        .unwrap()
        .set_activity(LoanActivity::Ended);
    returned
        .restore_predicate_lender(PredicateHolder(0), loan)
        .unwrap();
    returned
        .check_predicate_boundary(&[PredicateHolder(0)])
        .unwrap();
}

#[test]
fn logical_prefixes_use_real_initialization_and_import_only_the_actual_count() {
    use crate::predicate_logic::*;
    let expression = |kind| LogicExpression {
        nodes: vec![LogicNode {
            ty: LogicType::Usize,
            kind,
        }],
        root: 0,
    };
    let mut def = definition();
    def.resources[0].initialized.clear();
    def.scalar_constraints.clear();
    def.logic.parameters.push(LogicParameter {
        name: "n".into(),
        position: 1,
        ty: LogicType::Usize,
    });
    def.logical_prefixes
        .push(crate::PredicateInitializedPrefix {
            resource: 0,
            array_offset: 0,
            element: VirMemoryAccess::core_u64(),
            length: 2,
            stride: 8,
            count: crate::PredicatePrefixCount::Logical(expression(LogicNodeKind::Binder(
                LogicBinder::Parameter(0),
            ))),
        });
    for n in [0, 1, 2, 3] {
        let args = WitnessArguments {
            arguments: vec![expression(LogicNodeKind::Word(n))],
            ..Default::default()
        };
        let input = state();
        let result = transfer_predicate(
            &input,
            &def,
            7,
            &PredicateEffect::FoldWithWitnesses {
                holder: PredicateHolder(0),
                bindings: vec![binding(0)],
                witnesses: args,
            },
        );
        assert_eq!(
            result.is_ok(),
            n <= 1,
            "one actual initialized element, count={n}"
        );
        if let Ok(evidence) = result {
            assert!(evidence.output.closed_predicate_checks()[0].1);
        }
    }
    let id = VirValueId::new(20);
    let allocation = AbstractAllocationId::new(0);
    let mut input = state();
    input
        .define_value(id, AbstractValue::U64(U64Interval::unknown()))
        .unwrap();
    input.seed_parameter_origins(crate::VirFunctionId::new(0), &[id]);
    let args = WitnessArguments {
        inputs: vec![(LogicType::Usize, WitnessInput::Scalar(id))],
        arguments: vec![expression(LogicNodeKind::Binder(LogicBinder::Parameter(0)))],
        values: vec![],
    };
    let mut imported = input.clone();
    imported
        .import_predicate_interface_with_arguments(
            &def,
            &[binding(0)],
            PredicateHolder(0),
            &args,
            true,
        )
        .unwrap();
    assert_eq!(
        imported.value(id),
        Some(&AbstractValue::U64(U64Interval::new(0, 2).unwrap()))
    );
    assert_eq!(
        imported.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    // A contract-selected symbolic prefix does not initialize the whole upper
    // envelope, and cannot be used as a fully initialized ordinary reference.
    assert_ne!(
        imported
            .allocation(allocation)
            .unwrap()
            .initialization()
            .classify(ByteRange::new(0, 16).unwrap()),
        InitializationClass::Initialized
    );
    let mut invalidated = imported.clone();
    invalidated
        .allocation_mut(allocation)
        .unwrap()
        .mark_uninitialized(ByteRange::new(0, 8).unwrap())
        .unwrap();
    assert_eq!(
        invalidated.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    let mut overwritten = imported.clone();
    *overwritten.value_mut(id).unwrap() = AbstractValue::U64(U64Interval::new(0, 2).unwrap());
    assert_eq!(
        overwritten.closed_predicate_checks(),
        vec![(PredicateHolder(0), false)]
    );
    let Some(AbstractValue::Permission(p)) = input.value_mut(binding(0).permission) else {
        unreachable!()
    };
    p.mark_consumed();
    let before = input.clone();
    assert!(
        input
            .import_predicate_interface_with_arguments(
                &def,
                &[binding(0)],
                PredicateHolder(0),
                &args,
                true
            )
            .is_err()
    );
    assert_eq!(input, before);
}

#[test]
fn internal_frames_never_reinterpret_foreign_initialization_prefix_ssa_ids() {
    let allocation = AbstractAllocationId::new(0);
    let scalar = VirValueId::new(50);
    let mut input = state();
    input
        .define_value(scalar, AbstractValue::U64(U64Interval::exact(2)))
        .unwrap();
    let input = fold(&input, 0, 0).unwrap().output;
    let mapping = [PredicateCallBinding {
        caller: PredicateHolder(0),
        callee: PredicateHolder(1),
    }];
    let (frame, mut callee) = enter_predicate_call(&input, &mapping).unwrap();
    // This value happens to have the same number as an unrelated caller SSA.
    callee
        .define_value(scalar, AbstractValue::U64(U64Interval::new(0, 2).unwrap()))
        .unwrap();
    assert!(callee.bind_array_initialization_prefix(
        allocation,
        0,
        VirMemoryAccess::core_u64(),
        2,
        8,
        AffineExpression::identity(scalar)
    ));
    let returned = frame.resume(&callee, &mapping).unwrap();
    let whole = ByteRange::new(0, 16).unwrap();
    assert_ne!(
        returned
            .allocation(allocation)
            .unwrap()
            .initialization()
            .classify(whole),
        InitializationClass::Initialized
    );
    assert!(
        returned
            .initialization_partitions(allocation, VirMemoryAccess::core_u64())
            .iter()
            .all(|p| p
                .initialized
                .bounds()
                .is_none_or(|(_, end)| end.expression().root() != Some(scalar)))
    );
    let (again, next) = enter_predicate_call(
        &returned,
        &[PredicateCallBinding {
            caller: PredicateHolder(0),
            callee: PredicateHolder(2),
        }],
    )
    .unwrap();
    assert!(
        !next
            .initialization_partitions(allocation, VirMemoryAccess::core_u64())
            .iter()
            .any(|p| p
                .initialized
                .bounds()
                .is_some_and(|(_, end)| end.interval().lower() >= 16))
    );
    drop(again);
}

#[test]
fn replacing_a_prefix_count_cannot_reinterpret_already_initialized_bytes() {
    let allocation = AbstractAllocationId::new(0);
    let scalar = VirValueId::new(60);
    let other = VirValueId::new(61);
    let mut input = state();
    for id in [scalar, other] {
        input
            .define_value(id, AbstractValue::U64(U64Interval::new(0, 2).unwrap()))
            .unwrap();
        assert!(input.bind_array_initialization_prefix(
            allocation,
            0,
            VirMemoryAccess::core_u64(),
            2,
            8,
            AffineExpression::identity(id)
        ));
    }
    let mut narrowed = input.clone();
    narrowed.narrow_word_interval(scalar, U64Interval::exact(2));
    assert!(
        narrowed
            .initialization_partitions(allocation, VirMemoryAccess::core_u64())
            .iter()
            .any(|p| p
                .initialized
                .bounds()
                .is_some_and(|(_, end)| end.interval().lower() == 16))
    );
    *input.value_mut(scalar).unwrap() = AbstractValue::U64(U64Interval::exact(2));
    let partitions = input.initialization_partitions(allocation, VirMemoryAccess::core_u64());
    assert!(
        !partitions
            .iter()
            .any(|p| p
                .initialized
                .bounds()
                .is_some_and(|(_, end)| end.expression().root() == Some(scalar)
                    || end.interval().lower() == 16))
    );
    assert!(partitions.iter().any(|p| {
        p.initialized
            .bounds()
            .is_some_and(|(_, end)| end.expression().root() == Some(other))
    }));
    assert_eq!(
        input
            .allocation(allocation)
            .unwrap()
            .initialization()
            .classify(ByteRange::new(0, 8).unwrap()),
        InitializationClass::Initialized
    );
}

#[test]
fn memory_actual_snapshots_keep_old_contents_and_recheck_current_authority() {
    use crate::predicate_logic::{LogicType, ObservationTime, WitnessArguments, WitnessInput};
    let entry = state();
    let mut current = entry.clone();
    current
        .allocation_mut(AbstractAllocationId::new(0))
        .unwrap()
        .record_scalar_content(
            ByteRange::new(0, 8).unwrap(),
            VirMemoryAccess::core_u64(),
            AbstractValue::U64(U64Interval::exact(1)),
        );
    let metadata = WitnessArguments {
        inputs: vec![
            (
                LogicType::U64,
                WitnessInput::Memory {
                    base: 0,
                    offset: 0,
                    access: VirMemoryAccess::core_u64(),
                    time: ObservationTime::Entry,
                },
            ),
            (
                LogicType::U64,
                WitnessInput::Memory {
                    base: 0,
                    offset: 0,
                    access: VirMemoryAccess::core_u64(),
                    time: ObservationTime::Current,
                },
            ),
        ],
        ..Default::default()
    };
    let before = current.clone();
    current
        .with_predicate_input_snapshots(
            &entry,
            &[binding(0).pointer],
            &metadata,
            |candidate, inputs, normalized| {
                let WitnessInput::Scalar(old) = normalized.inputs[0].1 else {
                    panic!("old observation was not captured");
                };
                assert_eq!(
                    candidate.value(inputs[old as usize]),
                    Some(&AbstractValue::U64(U64Interval::exact(0)))
                );
                let WitnessInput::Memory {
                    base,
                    offset,
                    access,
                    time,
                } = normalized.inputs[1].1
                else {
                    panic!("current observation was replaced with old contents");
                };
                assert_eq!(time, ObservationTime::Current);
                assert_eq!(
                    candidate
                        .predicate_memory_snapshot(
                            LogicType::U64,
                            inputs[base as usize],
                            offset,
                            access
                        )?
                        .0,
                    AbstractValue::U64(U64Interval::exact(1))
                );
                Ok(())
            },
        )
        .unwrap();
    assert_eq!(
        current, before,
        "temporary pointers and values must not escape"
    );
    for failure in 0..3 {
        let mut invalid = current.clone();
        match failure {
            0 => invalid
                .allocation_mut(AbstractAllocationId::new(0))
                .unwrap()
                .mark_dead(),
            1 => invalid
                .allocation_mut(AbstractAllocationId::new(0))
                .unwrap()
                .mark_uninitialized(ByteRange::new(0, 8).unwrap())
                .unwrap(),
            2 => {
                let Some(AbstractValue::Permission(permission)) =
                    invalid.value_mut(binding(0).permission)
                else {
                    unreachable!()
                };
                permission.mark_consumed();
            }
            _ => unreachable!(),
        }
        assert!(
            invalid
                .predicate_memory_snapshot(
                    LogicType::U64,
                    binding(0).pointer,
                    0,
                    VirMemoryAccess::core_u64()
                )
                .is_err()
        );
        let original = invalid.clone();
        assert!(
            invalid
                .with_predicate_input_snapshots(
                    &entry,
                    &[binding(0).pointer],
                    &metadata,
                    |candidate, inputs, normalized| {
                        let WitnessInput::Memory {
                            base,
                            offset,
                            access,
                            ..
                        } = normalized.inputs[1].1
                        else {
                            unreachable!()
                        };
                        candidate.predicate_memory_snapshot(
                            LogicType::U64,
                            inputs[base as usize],
                            offset,
                            access,
                        )?;
                        Ok(())
                    }
                )
                .is_err()
        );
        assert_eq!(invalid, original);
    }
}

#[test]
fn opened_spec_observations_preserve_hidden_bounds_and_expire_with_the_opening() {
    let definition = logical_definition();
    let mut input = state();
    input
        .import_predicate_interface_with_arguments(
            &definition,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            true,
        )
        .unwrap();
    assert!(input.opened_predicate_snapshot(41, 0, 0).is_none());
    let opened = transfer_predicate(
        &input,
        &definition,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 41,
        },
    )
    .unwrap()
    .output;
    let before = opened.clone();
    assert_eq!(
        opened.opened_predicate_snapshot(41, 0, 0),
        Some((AbstractValue::U64(U64Interval::new(0, 7).unwrap()), None))
    );
    assert_eq!(opened, before);
    for (action, holder, binder) in [(40, 0, 0), (41, 1, 0), (41, 0, 1)] {
        assert!(
            opened
                .opened_predicate_snapshot(action, holder, binder)
                .is_none()
        );
    }
    let refolded = transfer_predicate(&opened, &definition, 7, &explicit_effect(6))
        .unwrap()
        .output;
    assert!(refolded.opened_predicate_snapshot(41, 0, 0).is_none());
    let reopened = transfer_predicate(
        &refolded,
        &definition,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 42,
        },
    )
    .unwrap()
    .output;
    assert!(reopened.opened_predicate_snapshot(41, 0, 0).is_none());
    assert_eq!(
        reopened.opened_predicate_snapshot(42, 0, 0),
        Some((
            AbstractValue::U64(U64Interval::exact(6)),
            Some(crate::AffineExpression::constant(6))
        ))
    );
    let mut foreign = opened.clone();
    let value = &mut foreign
        .predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .logical_witnesses[0];
    let crate::predicate_logic::LogicValue::Word(word) = &mut value.value else {
        unreachable!()
    };
    let (atom, coefficient) = word.terms.pop_first().unwrap();
    let logic::ObservationAtom::Existential { mut scope, binder } = atom else {
        unreachable!()
    };
    scope.instance += 1;
    word.terms.insert(
        logic::ObservationAtom::Existential { scope, binder },
        coefficient,
    );
    assert_eq!(
        foreign.opened_predicate_snapshot(41, 0, 0),
        Some((AbstractValue::U64(U64Interval::unknown()), None))
    );
    let mut head = ResourceState::new();
    assert!(head.inherit_loop_resources(&opened, &BTreeSet::new()));
    assert_eq!(head.next_predicate_scope, opened.next_predicate_scope);
    assert_eq!(
        head.opened_predicate_snapshot(41, 0, 0),
        opened.opened_predicate_snapshot(41, 0, 0)
    );
    assert!(head.loop_resources_match(&opened, &[]));
    head.predicates
        .get_mut(&PredicateHolder(0))
        .unwrap()
        .opening_action = Some(42);
    assert!(!head.loop_resources_match(&opened, &[]));
}

#[test]
fn opened_symbolic_guarantees_require_actual_aliases_and_matching_comparisons() {
    use crate::predicate_logic::*;
    let mut definition = logical_definition();
    definition.logic.parameters.push(LogicParameter {
        position: 1,
        name: "limit".into(),
        ty: LogicType::Usize,
    });
    definition.logic.constraints[0].nodes[1].kind =
        LogicNodeKind::Binder(LogicBinder::Parameter(0));
    let source = VirValueId::new(100);
    let alias = VirValueId::new(101);
    let mut input = state();
    for id in [source, alias] {
        input
            .define_value(id, AbstractValue::U64(U64Interval::unknown()))
            .unwrap();
    }
    let actuals = WitnessArguments {
        inputs: vec![(LogicType::Usize, WitnessInput::Scalar(source))],
        values: vec![],
        arguments: vec![LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            }],
            root: 0,
        }],
    };
    input
        .import_predicate_interface_with_arguments(
            &definition,
            &[binding(0)],
            PredicateHolder(0),
            &actuals,
            true,
        )
        .unwrap();
    let opened = transfer_predicate(
        &input,
        &definition,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 41,
        },
    )
    .unwrap()
    .output;
    let hidden = OpenedSpecOperand::Opened {
        action: 41,
        holder: 0,
        binder: 0,
    };
    assert_eq!(
        opened.prove_opened_spec_comparison(
            OpenedSpecComparison::LessEqual,
            hidden,
            OpenedSpecOperand::Value(source)
        ),
        Ok(true)
    );
    for comparison in [OpenedSpecComparison::Less, OpenedSpecComparison::Equal] {
        assert_eq!(
            opened.prove_opened_spec_comparison(
                comparison,
                hidden,
                OpenedSpecOperand::Value(source)
            ),
            Ok(false)
        );
    }
    assert_eq!(
        opened.prove_opened_spec_comparison(
            OpenedSpecComparison::LessEqual,
            hidden,
            OpenedSpecOperand::Value(alias)
        ),
        Ok(false)
    );
    let mut projected = opened.project_cfg_edge(&[(source, alias)]);
    projected
        .define_value(alias, *opened.value(source).unwrap())
        .unwrap();
    assert_eq!(
        projected.prove_opened_spec_comparison(
            OpenedSpecComparison::LessEqual,
            hidden,
            OpenedSpecOperand::Value(alias)
        ),
        Ok(true)
    );
    let mut replaced = projected.clone();
    *replaced.value_mut(alias).unwrap() = AbstractValue::U64(U64Interval::unknown());
    assert_eq!(
        replaced.prove_opened_spec_comparison(
            OpenedSpecComparison::LessEqual,
            hidden,
            OpenedSpecOperand::Value(alias)
        ),
        Ok(false)
    );
    assert_eq!(
        opened.prove_opened_spec_comparison(
            OpenedSpecComparison::LessEqual,
            OpenedSpecOperand::Value(source),
            hidden
        ),
        Ok(false)
    );
}

#[test]
fn opened_affine_bounds_use_the_pure_service_without_changing_resource_authority() {
    use crate::predicate_logic::*;
    let mut definition = logical_definition();
    definition.logic.constraints[0] = LogicExpression {
        nodes: vec![
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
            },
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Word(1),
            },
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Add(0, 1),
            },
            LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Word(7),
            },
            LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::LessEqual(2, 3),
            },
        ],
        root: 4,
    };
    let mut input = state();
    input
        .import_predicate_interface_with_arguments(
            &definition,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            true,
        )
        .unwrap();
    let opened = transfer_predicate(
        &input,
        &definition,
        7,
        &PredicateEffect::UnfoldNamed {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            action: 41,
        },
    )
    .unwrap()
    .output;
    let before = opened.clone();
    assert_eq!(
        opened.opened_predicate_snapshot(41, 0, 0),
        Some((AbstractValue::U64(U64Interval::new(0, 6).unwrap()), None))
    );
    let hidden = OpenedSpecOperand::Opened {
        action: 41,
        holder: 0,
        binder: 0,
    };
    assert_eq!(
        opened.prove_opened_spec_comparison(
            OpenedSpecComparison::Less,
            hidden,
            OpenedSpecOperand::Word(7)
        ),
        Ok(true)
    );
    assert_eq!(
        opened.prove_opened_spec_comparison(
            OpenedSpecComparison::Equal,
            hidden,
            OpenedSpecOperand::Word(6)
        ),
        Ok(false)
    );
    assert_eq!(opened, before);
    // Refolding must prove the new witness: a saved relation is not a license
    // to install a different value with invalid arithmetic.
    assert!(transfer_predicate(&opened, &definition, 7, &explicit_effect(7)).is_err());
    let refolded = transfer_predicate(&opened, &definition, 7, &explicit_effect(6))
        .unwrap()
        .output;
    assert_eq!(
        refolded.prove_opened_spec_comparison(
            OpenedSpecComparison::Less,
            hidden,
            OpenedSpecOperand::Word(7)
        ),
        Err(PredicateError::InvalidBinding)
    );
}

#[test]
fn refold_composes_hidden_guarantees_with_surviving_scalar_identity() {
    for historical in [false, true] {
        use crate::predicate_logic::*;
        let mut definition = logical_definition();
        definition.logic.parameters.push(LogicParameter {
            position: 1,
            name: "limit".into(),
            ty: LogicType::Usize,
        });
        definition.logic.existentials.push(Existential {
            name: "high".into(),
            ty: LogicType::Usize,
            default: None,
        });
        definition.logic.constraints = vec![
            LogicExpression {
                nodes: vec![
                    LogicNode {
                        ty: LogicType::Usize,
                        kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
                    },
                    LogicNode {
                        ty: LogicType::Usize,
                        kind: LogicNodeKind::Binder(LogicBinder::Existential(1)),
                    },
                    LogicNode {
                        ty: LogicType::Bool,
                        kind: LogicNodeKind::LessEqual(0, 1),
                    },
                ],
                root: 2,
            },
            LogicExpression {
                nodes: vec![
                    LogicNode {
                        ty: LogicType::Usize,
                        kind: LogicNodeKind::Binder(LogicBinder::Existential(1)),
                    },
                    LogicNode {
                        ty: LogicType::Usize,
                        kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                    },
                    LogicNode {
                        ty: LogicType::Bool,
                        kind: LogicNodeKind::Less(0, 1),
                    },
                ],
                root: 2,
            },
        ];
        let source = VirValueId::new(100);
        let mut input = state();
        input
            .define_value(source, AbstractValue::U64(U64Interval::unknown()))
            .unwrap();
        if historical {
            input.seed_parameter_origins(crate::VirFunctionId::new(1), &[source]);
        }
        let parameter = |index| LogicExpression {
            nodes: vec![LogicNode {
                ty: LogicType::Usize,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(index)),
            }],
            root: 0,
        };
        let mut actuals = WitnessArguments {
            inputs: vec![(LogicType::Usize, WitnessInput::Scalar(source))],
            values: vec![],
            arguments: vec![parameter(0)],
        };
        input
            .import_predicate_interface_with_arguments(
                &definition,
                &[binding(0)],
                PredicateHolder(0),
                &actuals,
                true,
            )
            .unwrap();
        let opened = transfer_predicate(
            &input,
            &definition,
            7,
            &PredicateEffect::WithArguments {
                holder: PredicateHolder(0),
                arguments: actuals.clone(),
                effect: Box::new(PredicateEffect::UnfoldNamed {
                    holder: PredicateHolder(0),
                    bindings: vec![binding(0)],
                    action: 41,
                }),
            },
        )
        .unwrap()
        .output;
        let before = opened.clone();
        assert_eq!(
            opened.prove_opened_spec_comparison(
                OpenedSpecComparison::Less,
                OpenedSpecOperand::Opened {
                    action: 41,
                    holder: 0,
                    binder: 0
                },
                OpenedSpecOperand::Value(source)
            ),
            Ok(true)
        );
        actuals.inputs.push((
            LogicType::Usize,
            WitnessInput::Opened {
                action: 41,
                holder: 0,
                binder: 0,
            },
        ));
        actuals.values = vec![
            (
                0,
                LogicExpression {
                    nodes: vec![LogicNode {
                        ty: LogicType::Usize,
                        kind: LogicNodeKind::Word(0),
                    }],
                    root: 0,
                },
            ),
            (1, parameter(1)),
        ];
        let effect = |witnesses| PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses,
        };
        let refolded = transfer_predicate(&opened, &definition, 7, &effect(actuals.clone()))
            .unwrap()
            .output;
        assert!(refolded.predicate_instances()[&PredicateHolder(0)].is_folded());
        assert!(refolded.opened_predicate_snapshot(41, 0, 0).is_none());
        assert_eq!(opened, before);
        // A second opening/refold keeps the old local snapshot identity, even
        // though both the package scope and the actual CFG SSA number change.
        let target = VirValueId::new(101);
        let edges = [
            (binding(0).pointer, binding(0).pointer),
            (binding(0).permission, binding(0).permission),
            (source, target),
        ];
        let mut projected = refolded.project_cfg_edge(&edges);
        for (from, to) in edges {
            projected.values.insert(to, *refolded.value(from).unwrap());
        }
        let mut next_actuals = actuals.clone();
        next_actuals.inputs.truncate(1);
        next_actuals.inputs[0].1 = WitnessInput::Scalar(target);
        next_actuals.values.clear();
        projected
            .check_predicate_arguments(&definition, PredicateHolder(0), &next_actuals)
            .unwrap();
        let reopened = transfer_predicate(
            &projected,
            &definition,
            7,
            &PredicateEffect::WithArguments {
                holder: PredicateHolder(0),
                arguments: next_actuals.clone(),
                effect: Box::new(PredicateEffect::UnfoldNamed {
                    holder: PredicateHolder(0),
                    bindings: vec![binding(0)],
                    action: 42,
                }),
            },
        )
        .unwrap()
        .output;
        next_actuals.inputs.push((
            LogicType::Usize,
            WitnessInput::Opened {
                action: 42,
                holder: 0,
                binder: 1,
            },
        ));
        next_actuals.values = actuals.values.clone();
        let second = transfer_predicate(&reopened, &definition, 7, &effect(next_actuals.clone()))
            .unwrap()
            .output;
        let mut parameter_actuals = next_actuals.clone();
        parameter_actuals.inputs.truncate(1);
        parameter_actuals.values.clear();
        second
            .check_predicate_arguments(&definition, PredicateHolder(0), &parameter_actuals)
            .unwrap();
        let mut overwritten = reopened.clone();
        *overwritten.value_mut(target).unwrap() = AbstractValue::U64(U64Interval::unknown());
        let joined = reopened.join(&overwritten).unwrap();
        for lost in [&overwritten, &joined] {
            let before = lost.clone();
            assert!(
                transfer_predicate(lost, &definition, 7, &effect(next_actuals.clone())).is_err()
            );
            assert_eq!(*lost, before);
        }
        let mut wrong = actuals.clone();
        wrong.values[1].1 = parameter(0);
        assert!(transfer_predicate(&opened, &definition, 7, &effect(wrong)).is_err());
        let mut replaced = opened.clone();
        *replaced.value_mut(source).unwrap() = AbstractValue::U64(U64Interval::unknown());
        let replaced_before = replaced.clone();
        assert!(transfer_predicate(&replaced, &definition, 7, &effect(actuals)).is_err());
        assert_eq!(replaced, replaced_before);
    }
}

#[test]
fn refold_retains_local_aliases_not_repeated_in_explicit_inputs() {
    use crate::predicate_logic::*;
    for boolean in [false, true] {
        let ty = if boolean {
            LogicType::Bool
        } else {
            LogicType::Usize
        };
        let unknown = if boolean {
            AbstractValue::Bool(AbstractBool::Unknown)
        } else {
            AbstractValue::U64(U64Interval::unknown())
        };
        let mut def = definition();
        def.logic.parameters.push(LogicParameter {
            position: 1,
            name: "value".into(),
            ty,
        });
        def.logic.existentials.push(Existential {
            name: "saved".into(),
            ty,
            default: None,
        });
        def.logic.constraints.push(LogicExpression {
            nodes: vec![
                LogicNode {
                    ty,
                    kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
                },
                LogicNode {
                    ty,
                    kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
                },
                LogicNode {
                    ty: LogicType::Bool,
                    kind: LogicNodeKind::Equal(0, 1),
                },
            ],
            root: 2,
        });
        let parameter = LogicExpression {
            nodes: vec![LogicNode {
                ty,
                kind: LogicNodeKind::Binder(LogicBinder::Parameter(0)),
            }],
            root: 0,
        };
        let source = VirValueId::new(90);
        let mut input = state();
        input.define_value(source, unknown).unwrap();
        assert!(input.word_origin(source).is_none());
        assert!(input.bool_origin(source).is_none());
        let actuals = WitnessArguments {
            inputs: vec![(ty, WitnessInput::Scalar(source))],
            values: vec![],
            arguments: vec![parameter.clone()],
        };
        // Imported existentials need not have the same atom as the parameter.
        // The package's actual equality is sufficient for an opened argument.
        for weak in [false, true] {
            if weak && boolean {
                continue;
            }
            let mut imported_def = def.clone();
            if weak {
                imported_def.logic.constraints[0].nodes[2].kind = LogicNodeKind::LessEqual(1, 0);
            }
            let mut imported = input.clone();
            imported
                .import_predicate_interface_with_arguments(
                    &imported_def,
                    &[binding(0)],
                    PredicateHolder(0),
                    &actuals,
                    true,
                )
                .unwrap();
            let mut opened = transfer_predicate(
                &imported,
                &imported_def,
                7,
                &PredicateEffect::UnfoldNamed {
                    holder: PredicateHolder(0),
                    bindings: vec![binding(0)],
                    action: 9,
                },
            )
            .unwrap()
            .output;
            let mut hidden_actuals = actuals.clone();
            hidden_actuals.inputs[0].1 = WitnessInput::Opened {
                action: 9,
                holder: 0,
                binder: 0,
            };
            let before = opened.clone();
            assert_eq!(
                opened
                    .check_predicate_arguments(&imported_def, PredicateHolder(0), &hidden_actuals,)
                    .is_ok(),
                !weak
            );
            assert_eq!(opened, before);
            let unrelated = VirValueId::new(91);
            opened.define_value(unrelated, unknown).unwrap();
            hidden_actuals.inputs[0].1 = WitnessInput::Scalar(unrelated);
            assert!(
                opened
                    .check_predicate_arguments(&imported_def, PredicateHolder(0), &hidden_actuals,)
                    .is_err()
            );
            hidden_actuals.inputs[0].1 = WitnessInput::Opened {
                action: 8,
                holder: 0,
                binder: 0,
            };
            assert!(
                opened
                    .check_predicate_arguments(&imported_def, PredicateHolder(0), &hidden_actuals,)
                    .is_err()
            );
        }
        let mut witnesses = actuals.clone();
        witnesses.values = vec![(0, parameter.clone())];
        let effect = |witnesses| PredicateEffect::FoldWithWitnesses {
            holder: PredicateHolder(0),
            bindings: vec![binding(0)],
            witnesses,
        };
        let mut current = transfer_predicate(&input, &def, 7, &effect(witnesses))
            .unwrap()
            .output;
        let saved = current.predicates[&PredicateHolder(0)]
            .logical_local_aliases
            .clone();
        for action in [10, 11, 12] {
            current
                .check_predicate_arguments(&def, PredicateHolder(0), &actuals)
                .unwrap();
            let opened = transfer_predicate(
                &current,
                &def,
                7,
                &PredicateEffect::UnfoldNamed {
                    holder: PredicateHolder(0),
                    bindings: vec![binding(0)],
                    action,
                },
            )
            .unwrap()
            .output;
            // No Scalar input appears in this fold. The original SSA remains
            // live and still denotes the parameter captured by the package.
            let witnesses = WitnessArguments {
                inputs: vec![(
                    ty,
                    WitnessInput::Opened {
                        action,
                        holder: 0,
                        binder: 0,
                    },
                )],
                values: vec![(0, parameter.clone())],
                arguments: vec![parameter.clone()],
            };
            current = transfer_predicate(&opened, &def, 7, &effect(witnesses))
                .unwrap()
                .output;
            assert_eq!(
                current.predicates[&PredicateHolder(0)].logical_local_aliases,
                saved
            );
            current
                .check_predicate_arguments(&def, PredicateHolder(0), &actuals)
                .unwrap();
            assert!(current.opened_predicate_snapshot(action, 0, 0).is_none());
        }
        // Local cloning renames both the old capture scope and the new package
        // scope consistently. Foreign calls instead retire all local aliases.
        let mut renamed = current.clone();
        logic::freshen_local_instance(
            renamed.predicates.get_mut(&PredicateHolder(0)).unwrap(),
            &mut renamed.next_predicate_scope,
        )
        .unwrap();
        renamed
            .check_predicate_arguments(&def, PredicateHolder(0), &actuals)
            .unwrap();
        assert_ne!(
            renamed.predicates[&PredicateHolder(0)].logical_local_aliases,
            saved
        );
        assert_eq!(
            renamed.predicates[&PredicateHolder(0)].resources,
            current.predicates[&PredicateHolder(0)].resources
        );
        let mapping = PredicateCallBinding {
            caller: PredicateHolder(0),
            callee: PredicateHolder(7),
        };
        let (frame, callee) = enter_predicate_call(&current, &[mapping]).unwrap();
        assert!(
            callee.predicates[&PredicateHolder(7)]
                .logical_local_aliases
                .is_empty()
        );
        let returned = frame.resume(&callee, &[mapping]).unwrap();
        assert!(
            returned
                .check_predicate_arguments(&def, PredicateHolder(0), &actuals)
                .is_err()
        );
        let mut replaced = current.clone();
        *replaced.value_mut(source).unwrap() = unknown;
        assert!(
            replaced
                .check_predicate_arguments(&def, PredicateHolder(0), &actuals)
                .is_err()
        );
        assert_eq!(
            replaced.predicates[&PredicateHolder(0)].logical_parameters,
            current.predicates[&PredicateHolder(0)].logical_parameters
        );
    }
}

#[test]
fn hidden_prefix_contracts_keep_logical_evidence_without_inventing_ssa_or_upper_bytes() {
    use crate::predicate_logic::*;
    let mut definition = logical_definition();
    definition.logic.constraints[0].nodes[1].kind = LogicNodeKind::Word(1);
    definition.resources[0].initialized.clear();
    definition.scalar_constraints.clear();
    definition
        .logical_prefixes
        .push(crate::PredicateInitializedPrefix {
            resource: 0,
            array_offset: 0,
            element: VirMemoryAccess::core_u64(),
            length: 2,
            stride: 8,
            count: crate::PredicatePrefixCount::Logical(LogicExpression {
                nodes: vec![LogicNode {
                    ty: LogicType::Usize,
                    kind: LogicNodeKind::Binder(LogicBinder::Existential(0)),
                }],
                root: 0,
            }),
        });
    let mut input = state(); // Exactly the first element is initialized.
    let before_values = input.values.clone();
    input
        .import_predicate_interface_with_arguments(
            &definition,
            &[binding(0)],
            PredicateHolder(0),
            &Default::default(),
            true,
        )
        .unwrap();
    assert_eq!(
        input.closed_predicate_checks(),
        vec![(PredicateHolder(0), true)]
    );
    assert_eq!(
        input.values.keys().collect::<Vec<_>>(),
        before_values.keys().collect::<Vec<_>>()
    );
    let allocation = AbstractAllocationId::new(0);
    assert_ne!(
        input
            .allocation(allocation)
            .unwrap()
            .initialization()
            .classify(ByteRange::new(0, 16).unwrap()),
        InitializationClass::Initialized
    );
    // A checked contract supplies a ghost range. Its upper bound does not
    // initialize concrete bytes; an ordinary fold still needs actual evidence.
    for bound in [1, 2] {
        definition.logic.constraints[0].nodes[1].kind = LogicNodeKind::Word(bound);
        let mut uninitialized = state();
        uninitialized
            .allocation_mut(allocation)
            .unwrap()
            .mark_uninitialized(ByteRange::new(0, 16).unwrap())
            .unwrap();
        assert_eq!(
            transfer_predicate(&uninitialized, &definition, 7, &explicit_effect(bound)),
            Err(PredicateError::UnprovedRepresentation)
        );
        uninitialized
            .import_predicate_interface_with_arguments(
                &definition,
                &[binding(0)],
                PredicateHolder(0),
                &Default::default(),
                true,
            )
            .unwrap();
        assert_eq!(
            uninitialized.closed_predicate_checks(),
            vec![(PredicateHolder(0), true)]
        );
        assert_ne!(
            uninitialized
                .allocation(allocation)
                .unwrap()
                .initialization()
                .classify(ByteRange::new(0, 8).unwrap()),
            InitializationClass::Initialized
        );
    }
}

/// Exercise real storage/loan identity across two separate destruction steps.
fn check_split_group_cleanup(input: &ResourceState, holder: PredicateHolder) {
    let mut state = input.clone();
    let resources = state.predicates[&holder].resources.clone();
    assert_eq!(resources.len(), 2);
    let (old_storage, old_key) = resources[1].storage.unwrap();
    let new_storage = AbstractAllocationId::new(5000);
    let new_key = ResourcePayloadKey::new(0, old_key.access());
    state
        .define_allocation(new_storage, AbstractAllocation::new_local(16, 8).unwrap())
        .unwrap();
    let payload = state
        .allocation(old_storage)
        .unwrap()
        .resource_payload(old_key);
    state
        .allocation_mut(old_storage)
        .unwrap()
        .set_resource_payload(old_key, MovePathState::Moved)
        .unwrap();
    state
        .allocation_mut(new_storage)
        .unwrap()
        .set_resource_payload(new_key, payload)
        .unwrap();
    state.move_stored_predicate_carrier(old_storage, old_key, new_storage, new_key);
    if let PermissionAuthority::Loan(id) = resources[1].permission.authority() {
        assert!(state.loan_mut(id).unwrap().move_stored_authority(
            old_storage,
            old_key,
            new_storage,
            new_key
        ));
    }
    let resources = state.predicates[&holder].resources.clone();
    for (index, r) in resources.iter().enumerate() {
        let (storage, key) = r.storage.unwrap();
        let MovePathState::Available(payload) =
            state.allocation(storage).unwrap().resource_payload(key)
        else {
            panic!()
        };
        let scope = BTreeSet::from([(storage, key)]);
        match r.permission.authority() {
            PermissionAuthority::Owner => {
                assert!(
                    state
                        .predicate_owner_to_drop(storage, key, &payload, &scope)
                        .is_some()
                );
                state.allocation_mut(r.allocation).unwrap().mark_dead();
            }
            PermissionAuthority::Loan(id) => {
                assert_eq!(
                    state.predicate_borrowed_to_drop(storage, key, &payload, &scope),
                    Some(holder)
                );
                let loan = state.loan_mut(id).unwrap();
                assert!(loan.remove_stored_authority(storage, key));
                loan.set_activity(LoanActivity::Ended);
            }
            _ => panic!(),
        }
        state
            .allocation_mut(storage)
            .unwrap()
            .set_resource_payload(key, MovePathState::Moved)
            .unwrap();
        assert!(state.advance_dropped_predicate(holder));
        if index == 0 {
            let pending = &state.predicates[&holder];
            assert!(pending.dropping && !pending.folded);
            assert!(state.predicate_cleanup_valid(pending));
            assert!(!state.predicate_representation_valid(pending));
            assert!(pending.logical_facts.is_empty() && pending.logic_scope.is_none());
            assert!(state.check_predicate_boundary(&[holder]).is_err());
            for (parent, before) in &input.predicates {
                if *parent != holder {
                    assert_eq!(&state.predicates[parent], before);
                }
            }
            assert!(state.join(input).is_err());
            let mut broken = state.clone();
            broken
                .allocation_mut(new_storage)
                .unwrap()
                .set_resource_payload(new_key, MovePathState::Unknown)
                .unwrap();
            let before = broken.clone();
            assert!(!broken.advance_dropped_predicate(holder));
            assert_eq!(broken, before);
            let mut incomplete = state.clone();
            assert!(!incomplete.finish_dropped_predicate(holder));
            assert_eq!(incomplete, state);
            assert!(
                transfer_predicate(
                    &state,
                    &pending.definition,
                    pending.definition.module,
                    &PredicateEffect::Move {
                        source: holder,
                        destination: PredicateHolder(8000)
                    }
                )
                .is_err()
            );
        }
    }
    assert!(!state.predicates.contains_key(&holder));
    for (parent, before) in &input.predicates {
        if *parent != holder && !before.borrowed_by.is_empty() {
            assert!(state.predicates[parent].borrowed_by.is_empty());
            assert!(state.predicate_representation_valid(&state.predicates[parent]));
        }
    }
}
