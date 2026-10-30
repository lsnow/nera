use super::*;

fn field_state() -> (ResourceState, PredicateDefinition) {
    field_state_from_source(include_str!(
        "../../../../../spec/cases/verify/predicate-resource-fields.nera"
    ))
}

fn field_state_from_source(source: &str) -> (ResourceState, PredicateDefinition) {
    let output = crate::analyze(&crate::SourceFile::from_text("fields.nera", source));
    let unit = output.vir().unwrap().as_unit();
    let predicate = &unit.specs.predicates()[0];
    let definition = PredicateDefinition::from_vir(&unit.memory, predicate, 0).unwrap();
    let root = predicate.representation.as_ref().unwrap().resources[0].pointee;
    let field = &definition.resource_fields[0][0];
    let mut state = state();
    let storage = AbstractAllocationId::new(0);
    let child = AbstractAllocationId::new(1);
    if let Some(AbstractValue::Pointer(p)) = state.value_mut(binding(0).pointer) {
        *p = p.with_memory_access(Some(root));
    }
    let range = ByteRange::new(0, field.size).unwrap();
    let mut allocation = AbstractAllocation::new(VirRegionId::new(0), field.size, 8).unwrap();
    allocation.mark_initialized(range).unwrap();
    allocation.mark_valid(range).unwrap();
    state.define_allocation(child, allocation).unwrap();
    let pointer = AbstractPointer::new(
        AbstractProvenance::Known(child),
        U64Interval::exact(0),
        GuaranteedAlignment::new(8).unwrap(),
    )
    .with_memory_access(Some(field.pointee));
    let permission = AbstractPermission::new(
        pointer.provenance(),
        AbstractByteRange::Exact(range),
        AccessPermission::Write,
        FreeCapability::Yes,
    );
    state
        .allocation_mut(storage)
        .unwrap()
        .set_resource_payload(
            ResourcePayloadKey::new(field.offset, field.access),
            MovePathState::available(TypedResourcePayload::new(pointer, permission)),
        )
        .unwrap();
    (state, definition)
}

#[test]
fn field_sealing_checks_real_payloads_and_rechecks_liveness() {
    let (state, definition) = field_state();
    let effect = PredicateEffect::Fold {
        holder: PredicateHolder(0),
        bindings: vec![binding(0)],
    };
    let evidence = transfer_predicate(&state, &definition, 0, &effect).unwrap();
    check_predicate_evidence(&state, &evidence).unwrap();
    assert!(
        evidence
            .output
            .predicate_representation_valid(&evidence.output.predicates[&PredicateHolder(0)])
    );
    let field = &definition.resource_fields[0][0];
    let key = ResourcePayloadKey::new(field.offset, field.access);
    for mutation in 0..6 {
        let mut input = state.clone();
        match mutation {
            0 => input
                .allocation_mut(AbstractAllocationId::new(1))
                .unwrap()
                .set_liveness(LivenessState::Dead),
            1 => {
                input
                    .allocation_mut(AbstractAllocationId::new(0))
                    .unwrap()
                    .set_resource_payload(key, MovePathState::Moved)
                    .unwrap();
            }
            2 => {
                input
                    .allocation_mut(AbstractAllocationId::new(1))
                    .unwrap()
                    .forget_initialization(ByteRange::new(0, 8).unwrap())
                    .unwrap();
            }
            3 => {
                input
                    .allocation_mut(AbstractAllocationId::new(1))
                    .unwrap()
                    .forget_validity(ByteRange::new(0, 8).unwrap())
                    .unwrap();
            }
            4 => {
                let MovePathState::Available(payload) = input
                    .allocation(AbstractAllocationId::new(0))
                    .unwrap()
                    .resource_payload(key)
                else {
                    panic!()
                };
                input
                    .define_value(
                        VirValueId::new(99),
                        AbstractValue::Permission(payload.permission()),
                    )
                    .unwrap();
            }
            5 => {
                let MovePathState::Available(payload) = input
                    .allocation(AbstractAllocationId::new(0))
                    .unwrap()
                    .resource_payload(key)
                else {
                    panic!()
                };
                input
                    .allocation_mut(AbstractAllocationId::new(0))
                    .unwrap()
                    .set_resource_payload(
                        key,
                        MovePathState::available(TypedResourcePayload::new(
                            payload
                                .pointer()
                                .with_memory_access(Some(VirMemoryAccess::core_u64())),
                            payload
                                .permission()
                                .with_availability(PermissionAvailability::Consumed),
                        )),
                    )
                    .unwrap();
            }
            _ => unreachable!(),
        }
        assert!(
            transfer_predicate(&input, &definition, 0, &effect).is_err(),
            "mutation {mutation}"
        );
        let mut closed = input;
        closed.predicates = evidence.output.predicates.clone();
        assert!(
            !closed.predicate_representation_valid(&closed.predicates[&PredicateHolder(0)]),
            "mutation {mutation}"
        );
    }
}

#[test]
fn reference_fields_require_the_actual_single_mutable_stored_authority() {
    let (mut state, definition) = field_state_from_source(
        "struct Holder { value:&mut u64, marker:u64, } predicate Held(p:ptr<Holder>) { exists item:ptr<u64> = p.value; owns(p); item==p.value; } fn main()->u64{return 0;}",
    );
    let field = &definition.resource_fields[0][0];
    let storage = AbstractAllocationId::new(0);
    let key = ResourcePayloadKey::new(field.offset, field.access);
    let MovePathState::Available(payload) =
        state.allocation(storage).unwrap().resource_payload(key)
    else {
        panic!()
    };
    let loan = crate::VirLoanId::new(0);
    let range = ByteRange::new(0, field.size).unwrap();
    let permission = AbstractPermission::new(
        payload.pointer().provenance(),
        AbstractByteRange::Exact(range),
        AccessPermission::Write,
        FreeCapability::No,
    )
    .with_authority(PermissionAuthority::Loan(loan));
    let mut fact = AbstractLoan::new(
        payload.pointer().provenance(),
        range,
        crate::VirLoanKind::Mutable,
        crate::VirBorrowRegionId::new(0),
        None,
        LoanActivity::Active,
    )
    .with_footprint(Some(crate::verifier::MemoryFootprint {
        provenance: payload.pointer().provenance(),
        access: field.pointee,
        stride_bytes: field.size,
        range: AbstractByteRange::Exact(range),
        envelope: range,
    }));
    fact.add_stored_authority(storage, key);
    state.define_loan(loan, fact).unwrap();
    state
        .allocation_mut(storage)
        .unwrap()
        .set_resource_payload(
            key,
            MovePathState::available(TypedResourcePayload::new(payload.pointer(), permission)),
        )
        .unwrap();
    let effect = PredicateEffect::Fold {
        holder: PredicateHolder(0),
        bindings: vec![binding(0)],
    };
    let evidence = transfer_predicate(&state, &definition, 0, &effect).unwrap();
    check_predicate_evidence(&state, &evidence).unwrap();
    for mutation in 0..4 {
        let mut broken = state.clone();
        match mutation {
            0 => {
                broken
                    .loan_mut(loan)
                    .unwrap()
                    .remove_stored_authority(storage, key);
            }
            1 => {
                broken
                    .loan_mut(loan)
                    .unwrap()
                    .set_activity(LoanActivity::Ended);
            }
            2 => {
                broken
                    .define_value(VirValueId::new(99), AbstractValue::Permission(permission))
                    .unwrap();
                broken
                    .loan_mut(loan)
                    .unwrap()
                    .add_authority(VirValueId::new(99));
            }
            3 => {
                let loan = broken.loan_mut(loan).unwrap();
                *loan = loan.clone().with_footprint(None);
            }
            _ => unreachable!(),
        }
        assert!(transfer_predicate(&broken, &definition, 0, &effect).is_err());
        assert!(check_predicate_evidence(&broken, &evidence).is_err());
    }
}
