use super::*;
use crate::verifier::vc::VcLimits;

fn id(n: u32) -> VirValueId {
    VirValueId::new(n)
}
fn allocation_id() -> AbstractAllocationId {
    AbstractAllocationId::vir_allocation_site(id(1))
}

fn state() -> ResourceState {
    let mut state = ResourceState::new();
    let allocation = AbstractAllocation::new(VirRegionId::new(0), 16, 8).unwrap();
    state
        .define_allocation(allocation_id(), allocation)
        .unwrap();
    let provenance = AbstractProvenance::Known(allocation_id());
    state
        .define_value(
            id(1),
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
    state
        .define_value(
            id(2),
            AbstractValue::Permission(AbstractPermission::new(
                provenance,
                AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
                AccessPermission::Write,
                FreeCapability::Yes,
            )),
        )
        .unwrap();
    state
}

fn query(authority: bool, initialized: bool) -> SpecMemoryQuery {
    SpecMemoryQuery {
        pointer: id(1),
        authority: authority.then_some(id(2)),
        start: 0,
        end: 8,
        layout: VirMemoryAccess::core_u64(),
        access: AccessPermission::Write,
        initialized,
        valid: authority && initialized,
    }
}

fn check(state: &ResourceState, query: SpecMemoryQuery) -> ObligationStatus {
    let before = state.clone();
    let result = query_spec_memory(
        state,
        &VirMemorySchema::core_u64(),
        query,
        crate::CfgAnalysisConfig::default(),
        &mut VcQueryBudget::new(VcLimits::default()),
    )
    .unwrap_or(ObligationStatus::Unknown);
    assert_eq!(state, &before, "query must not alter resources");
    result
}

#[test]
fn scalar_observation_is_bounded_and_does_not_restore_authority() {
    let mut s = state();
    let access = VirMemoryAccess::core_u64();
    let bytes = ByteRange::new(0, 8).unwrap();
    let a = s.allocation_mut(allocation_id()).unwrap();
    a.mark_initialized(bytes).unwrap();
    a.mark_valid(bytes).unwrap();
    a.record_scalar_content(bytes, access, AbstractValue::U64(U64Interval::exact(42)));
    let historical = s.clone();
    let memory = VirMemorySchema::core_u64();
    let q = query(true, true);
    assert_eq!(check(&s, q), ObligationStatus::Proven);
    assert_eq!(
        spec_scalar_contents(&s, &memory, q, &mut VcQueryBudget::new(VcLimits::default())),
        Some(vec![AbstractValue::U64(U64Interval::exact(42))])
    );
    let mut budget = VcQueryBudget::new(VcLimits {
        max_query_steps: 0,
        ..VcLimits::default()
    });
    assert_eq!(spec_scalar_contents(&s, &memory, q, &mut budget), None);
    assert!(budget.exhausted);
    let mut budget = VcQueryBudget::new(VcLimits {
        max_queries: 0,
        ..VcLimits::default()
    });
    assert_eq!(
        query_contract_memory(&s, &memory, q, access, &mut budget),
        None
    );
    assert!(budget.exhausted);
    assert_eq!(s, historical, "observation cannot mutate state");
    s.allocation_mut(allocation_id()).unwrap().mark_dead();
    assert_eq!(check(&s, q), ObligationStatus::Refuted);
    assert_eq!(
        spec_scalar_contents(&s, &memory, q, &mut VcQueryBudget::new(VcLimits::default())),
        None
    );
    assert_eq!(check(&historical, q), ObligationStatus::Proven);
}

#[test]
fn state_observation_is_not_authority_or_valid_representation() {
    use ObligationStatus::{Proven as P, Refuted as R, Unknown as U};
    let mut s = state();
    assert_eq!(check(&s, query(true, false)), P);
    assert_eq!(check(&s, query(false, true)), R);
    s.allocation_mut(allocation_id())
        .unwrap()
        .mark_initialized(ByteRange::new(0, 8).unwrap())
        .unwrap();
    assert_eq!(check(&s, query(false, true)), P);
    assert_eq!(
        check(&s, query(true, true)),
        U,
        "bytes alone do not prove representation"
    );
    s.allocation_mut(allocation_id())
        .unwrap()
        .mark_valid(ByteRange::new(0, 8).unwrap())
        .unwrap();
    assert_eq!(check(&s, query(true, true)), P);
    mark_permission_consumed(&mut s, id(2)).unwrap();
    assert_eq!(spec_alive(&s, id(1)), P);
    assert_eq!(check(&s, query(false, true)), P);
    assert_eq!(check(&s, query(true, true)), R);
}

#[test]
fn joins_and_reused_allocation_slots_cannot_resurrect_old_facts() {
    use ObligationStatus::{Proven as P, Refuted as R, Unknown as U};
    let mut initialized = state();
    initialized
        .allocation_mut(allocation_id())
        .unwrap()
        .mark_initialized(ByteRange::new(0, 8).unwrap())
        .unwrap();
    initialized
        .allocation_mut(allocation_id())
        .unwrap()
        .mark_valid(ByteRange::new(0, 8).unwrap())
        .unwrap();
    let joined = initialized.join(&state()).unwrap();
    assert_eq!(check(&joined, query(false, true)), U);
    let mut dead = initialized.clone();
    dead.allocation_mut(allocation_id()).unwrap().mark_dead();
    let maybe_live = dead.join(&initialized).unwrap();
    assert_eq!(spec_alive(&maybe_live, id(1)), U);
    assert_eq!(check(&maybe_live, query(true, true)), U);
    assert_eq!(spec_alive(&dead, id(1)), R);
    assert_eq!(
        spec_same_allocation(&dead, id(1), id(1)),
        P,
        "identity alone is not liveness"
    );
    dead.introduce_allocation_instance(
        allocation_id(),
        AbstractAllocation::new(VirRegionId::new(0), 16, 8).unwrap(),
    )
    .unwrap();
    assert_eq!(
        spec_alive(&dead, id(1)),
        U,
        "old pointer was forgotten at instance reuse"
    );
    assert_eq!(spec_same_allocation(&dead, id(1), id(1)), U);
    assert_eq!(check(&dead, query(true, true)), U);
    let other = AbstractAllocationId::vir_allocation_site(id(9));
    initialized
        .define_allocation(
            other,
            AbstractAllocation::new(VirRegionId::new(0), 16, 8).unwrap(),
        )
        .unwrap();
    initialized
        .define_value(
            id(9),
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
    assert_eq!(spec_same_allocation(&initialized, id(1), id(9)), R);
}

#[test]
fn memory_queries_check_typed_ranges_and_fail_closed_on_budgets() {
    let s = state();
    for (start, end, expected) in [
        (0, 16, ObligationStatus::Proven),
        (8, 16, ObligationStatus::Proven),
        (8, 24, ObligationStatus::Refuted),
        (8, 0, ObligationStatus::Refuted),
        (u64::MAX - 7, u64::MAX, ObligationStatus::Unknown),
        (0, 0, ObligationStatus::Proven),
        (16, 16, ObligationStatus::Proven),
        (24, 24, ObligationStatus::Refuted),
    ] {
        let mut q = query(true, false);
        q.start = start;
        q.end = end;
        assert_eq!(check(&s, q), expected, "{start}..{end}");
    }
    for limits in [
        VcLimits {
            max_queries: 0,
            ..VcLimits::default()
        },
        VcLimits {
            max_query_steps: 0,
            ..VcLimits::default()
        },
    ] {
        assert!(
            query_spec_memory(
                &s,
                &VirMemorySchema::core_u64(),
                query(true, false),
                crate::CfgAnalysisConfig::default(),
                &mut VcQueryBudget::new(limits)
            )
            .is_none()
        );
    }
}

#[test]
fn loan_authority_queries_follow_borrow_and_end_without_affecting_transfer() {
    for (source, during_write) in [
        (
            "fn main() -> u64 { let mut x=7; let r=&x; return *r; }",
            ObligationStatus::Refuted,
        ),
        (
            "fn main() -> u64 { let mut x=7; let r=&mut x; return *r; }",
            ObligationStatus::Refuted,
        ),
    ] {
        let output = crate::analyze(&crate::SourceFile::from_text("spec-loan.nera", source));
        let unit = output.vir().unwrap().as_unit();
        let config = crate::CfgAnalysisConfig::default();
        let context = LoanTransferContext {
            borrows: &unit.borrows,
            function: VirFunctionId::new(0),
            limits: LoanTransferLimits {
                max_region_pairs: 256,
                max_active_loans: 256,
                max_aliases_per_loan: 256,
                max_region_constraints: 4096,
                max_reborrow_depth: 64,
            },
        };
        let mut builder = TransferBuilder::new(
            ResourceState::new(),
            ByteSpan::new(0, source.len()).unwrap(),
            &unit.memory,
            None,
            Some(context),
        );
        let mut owner = None;
        let mut checked = 0;
        for instruction in &unit.runtime.functions[0].blocks[0].instructions {
            if let VirInstruction::LoanBegin { effect, .. } = &instruction.instruction {
                owner = Some((effect.source_pointer, effect.source_permission));
            }
            builder.apply(&instruction.instruction).unwrap();
            if let VirInstruction::LoanBegin {
                reference_result,
                permission_result,
                ..
            } = &instruction.instruction
            {
                for access in [AccessPermission::Read, AccessPermission::Write] {
                    let result = query_spec_memory(
                        &builder.state,
                        &unit.memory,
                        SpecMemoryQuery {
                            pointer: reference_result.id,
                            authority: Some(permission_result.id),
                            start: 0,
                            end: 8,
                            layout: VirMemoryAccess::core_u64(),
                            access,
                            initialized: true,
                            valid: true,
                        },
                        config,
                        &mut VcQueryBudget::new(VcLimits::default()),
                    )
                    .unwrap();
                    let expected =
                        if access == AccessPermission::Write && !source.contains("&mut x") {
                            ObligationStatus::Refuted
                        } else {
                            ObligationStatus::Proven
                        };
                    assert_eq!(result, expected, "borrowed {access:?}");
                }
            }
            if let (
                Some((pointer, authority)),
                VirInstruction::LoanBegin { .. } | VirInstruction::LoanEnd { .. },
            ) = (owner, &instruction.instruction)
            {
                let before = builder.state.clone();
                let q = SpecMemoryQuery {
                    pointer,
                    authority: Some(authority),
                    start: 0,
                    end: 8,
                    layout: VirMemoryAccess::core_u64(),
                    access: AccessPermission::Write,
                    initialized: true,
                    valid: true,
                };
                let result = query_spec_memory(
                    &builder.state,
                    &unit.memory,
                    q,
                    config,
                    &mut VcQueryBudget::new(VcLimits::default()),
                )
                .unwrap();
                assert_eq!(
                    result,
                    if matches!(instruction.instruction, VirInstruction::LoanBegin { .. }) {
                        during_write
                    } else {
                        ObligationStatus::Proven
                    }
                );
                assert_eq!(before, builder.state);
                checked += 1;
            }
        }
        assert!(checked >= 2);
        assert!(builder.obligations.iter().all(|o| o.status().is_proven()));
    }
}
