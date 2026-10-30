use super::*;
use crate::vir::interpreter::{RuntimeAllocationKind, RuntimeOwnedPayload};

fn allocation(size_bytes: u64) -> Allocation {
    Allocation {
        size_bytes,
        alignment: 8,
        kind: RuntimeAllocationKind::LocalStorage,
        live: true,
        bytes: BTreeMap::new(),
        objects: Vec::new(),
        resource_payloads: BTreeMap::new(),
        raw_payloads: BTreeMap::new(),
    }
}

#[test]
fn stored_call_authorities_roundtrip_and_reject_partial_transfers() {
    for mode in [crate::VirMutability::Const, crate::VirMutability::Mutable] {
        check_stored_call(mode);
    }
}

fn check_stored_call(mode: crate::VirMutability) {
    let output = crate::analyze(&crate::SourceFile::from_text(
        "stored-call.nera",
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/spec/cases/aggregate/owning-abi.nera"
        )),
    ));
    // Internal fixture for exact token mutations; source-call coverage lives in
    // frontend_reference_aggregate and native_acceptance.
    let mut unit = output.vir().unwrap().as_unit().clone();
    for ty in &mut unit.memory.types {
        if let crate::VirMemoryTypeKind::Pointer {
            kind, mutability, ..
        } = &mut ty.kind
            && *kind == crate::VirPointerKind::Own
        {
            *kind = crate::VirPointerKind::Reference;
            *mutability = mode;
        }
    }
    unit.memory.assign_canonical_type_capabilities().unwrap();
    unit.memory.validate().unwrap();
    let function = unit
        .runtime
        .functions
        .iter()
        .find(|f| {
            unit.runtime
                .abis
                .function(f.id)
                .unwrap()
                .signature
                .parameters()
                .iter()
                .any(|b| matches!(b.value(), crate::VirAbiValue::IndirectAggregate { .. }))
        })
        .unwrap();
    let accesses = unit
        .runtime
        .abis
        .function(function.id)
        .unwrap()
        .signature
        .parameters()
        .iter()
        .map(|b| b.value().access().unwrap())
        .collect::<Vec<_>>();
    let entries = crate::vir::plan_parameter_reference_entries(&unit.memory, &accesses).unwrap();
    assert!(entries.len() >= 2);
    unit.borrows = crate::VirBorrowEnvironment::from_tables(
        entries
            .iter()
            .enumerate()
            .map(|(i, e)| crate::VirBorrowRegion {
                id: crate::VirBorrowRegionId::new(i as u32),
                owner: function.id,
                origin: crate::VirBorrowRegionOrigin::ParameterField {
                    index: e.parameter,
                    slot: e.slot,
                },
                scope: crate::VirBorrowRegionScope::Function,
                source_origin: crate::VirOriginId::new(0),
            })
            .collect(),
        vec![],
    );
    let runtime = crate::RuntimeVirView::new(&unit.memory, &unit.borrows, &unit.runtime);
    let block = function
        .blocks
        .iter()
        .find(|b| b.id == function.entry)
        .unwrap();
    let span = ByteSpan::empty();
    let limits = RuntimeLoanLimits {
        active_loans: 16,
        aliases_per_loan: 16,
        reborrow_depth: 16,
    };
    let mut frame = BlockFrame {
        values: BTreeMap::new(),
        consumed_permissions: BTreeSet::new(),
        loan_authorities: BTreeMap::new(),
    };
    let mut caller = RuntimeLoanShadow::new(100);
    let mut allocations = BTreeMap::new();
    let mut locations = Vec::new();
    for (i, e) in entries.iter().enumerate() {
        let storage_id = 100 + u64::from(e.parameter);
        let access = accesses[e.parameter as usize];
        let size = unit.memory.layout(access.layout).unwrap().size_bytes + 8;
        allocations
            .entry(storage_id)
            .or_insert_with(|| allocation(size));
        let storage = VirRuntimePointer {
            allocation: storage_id,
            offset_bytes: 8,
            access,
            paths: crate::VirPointerPaths::default(),
            view_range: None,
            domain: crate::VirPointerDomain::Restricted(VirLoanRange {
                start_bytes: 8,
                end_bytes: size,
            }),
        };
        frame.values.insert(
            block.parameters[e.pointer_slot as usize].id,
            VirRuntimeValue::Pointer(storage),
        );
        frame.values.insert(
            block.parameters[e.permission_slot as usize].id,
            VirRuntimeValue::Permission(VirRuntimePermission {
                allocation: storage_id,
                start_bytes: 8,
                end_bytes: size,
                can_free_when_complete: false,
            }),
        );
        let range = VirLoanRange {
            start_bytes: 0,
            end_bytes: 8,
        };
        let pointer = VirRuntimePointer {
            allocation: 1000 + i as u64,
            offset_bytes: 0,
            access: e.pointee,
            paths: crate::VirPointerPaths::default(),
            view_range: Some(range),
            domain: crate::VirPointerDomain::Restricted(range),
        };
        allocations.insert(pointer.allocation, allocation(8));
        let permission = VirRuntimePermission {
            allocation: pointer.allocation,
            start_bytes: 0,
            end_bytes: 8,
            can_free_when_complete: false,
        };
        let id = VirLoanId::new(i as u32);
        let authority = caller.fresh_authority(id, span).unwrap();
        caller.loans.insert(
            id,
            RuntimeLoan {
                allocation: pointer.allocation,
                range,
                envelope: range,
                kind: if mode == crate::VirMutability::Const {
                    VirLoanKind::Shared
                } else {
                    VirLoanKind::Mutable
                },
                region: crate::VirBorrowRegionId::new(0),
                parent: None,
                pointee: e.pointee,
                activity: RuntimeLoanActivity::Active,
                authorities: BTreeSet::from([authority.token]),
            },
        );
        let key = RuntimeResourcePayloadKey {
            offset_bytes: 8 + e.offset_bytes,
            access: e.reference,
        };
        allocations
            .get_mut(&storage_id)
            .unwrap()
            .resource_payloads
            .insert(
                key,
                RuntimeOwnedPayload {
                    pointer,
                    permission,
                    loan_authority: Some(authority),
                },
            );
        locations.push((storage_id, key));
    }
    let payloads = |objects: &BTreeMap<u64, Allocation>| {
        objects
            .iter()
            .map(|(id, a)| (*id, a.resource_payloads.clone()))
            .collect::<BTreeMap<_, _>>()
    };
    let last = *locations.last().unwrap();
    for mutation in 0..5 {
        let mut objects = allocations.clone();
        let mut budget = limits;
        match mutation {
            0 => {
                objects
                    .get_mut(&last.0)
                    .unwrap()
                    .resource_payloads
                    .get_mut(&last.1)
                    .unwrap()
                    .loan_authority
                    .as_mut()
                    .unwrap()
                    .token
                    .invocation = 99
            }
            1 => {
                objects
                    .get_mut(&last.0)
                    .unwrap()
                    .resource_payloads
                    .remove(&last.1);
            }
            2 => {
                objects
                    .get_mut(&last.0)
                    .unwrap()
                    .resource_payloads
                    .get_mut(&last.1)
                    .unwrap()
                    .permission
                    .can_free_when_complete = true
            }
            3 => budget.active_loans = 1,
            4 => {
                objects
                    .get_mut(&(1000 + entries.len() as u64 - 1))
                    .unwrap()
                    .size_bytes = 4
            }
            _ => unreachable!(),
        }
        let before = payloads(&objects);
        let mut callee = RuntimeLoanShadow::new(101);
        let original = callee.clone();
        assert!(
            callee
                .import_stored_parameters(
                    &caller,
                    &mut objects,
                    &frame,
                    function,
                    runtime,
                    budget,
                    span
                )
                .is_err()
        );
        assert_eq!(callee, original);
        assert_eq!(payloads(&objects), before);
    }
    let original_caller = caller.clone();
    let original_payloads = payloads(&allocations);
    let mut callee = RuntimeLoanShadow::new(101);
    let returns = callee
        .import_stored_parameters(
            &caller,
            &mut allocations,
            &frame,
            function,
            runtime,
            limits,
            span,
        )
        .unwrap();
    assert_eq!(caller, original_caller);
    for ((id, key), record) in locations.iter().zip(&returns) {
        assert_eq!(
            allocations[id].resource_payloads[key].loan_authority,
            Some(record.callee)
        );
        assert_ne!(
            record.caller.token.invocation,
            record.callee.token.invocation
        );
    }
    for mutation in 0..9 {
        let mut objects = allocations.clone();
        let mut source = caller.clone();
        let mut target = callee.clone();
        let mut outgoing_frame = frame.clone();
        let mut records = returns.clone();
        match mutation {
            0 => {
                objects
                    .get_mut(&last.0)
                    .unwrap()
                    .resource_payloads
                    .remove(&last.1);
            }
            1 => {
                let value = objects[&last.0].resource_payloads[&last.1];
                objects.insert(9999, allocation(128));
                objects
                    .get_mut(&9999)
                    .unwrap()
                    .resource_payloads
                    .insert(last.1, value);
            }
            2 => {
                source
                    .loans
                    .get_mut(&returns.last().unwrap().caller.loan)
                    .unwrap()
                    .authorities
                    .clear();
            }
            3 => {
                let id = crate::VirValueId::new(9999);
                outgoing_frame.values.insert(
                    id,
                    VirRuntimeValue::Permission(returns.last().unwrap().permission),
                );
                outgoing_frame
                    .loan_authorities
                    .insert(id, returns.last().unwrap().callee);
            }
            4 => {
                objects
                    .get_mut(&last.0)
                    .unwrap()
                    .resource_payloads
                    .get_mut(&last.1)
                    .unwrap()
                    .permission
                    .end_bytes = 7
            }
            5 => {
                // A unique token in unrelated live storage is not a return.
                let value = objects
                    .get_mut(&last.0)
                    .unwrap()
                    .resource_payloads
                    .remove(&last.1)
                    .unwrap();
                objects.insert(9999, allocation(128));
                objects
                    .get_mut(&9999)
                    .unwrap()
                    .resource_payloads
                    .insert(last.1, value);
            }
            6 => {
                objects
                    .get_mut(&last.0)
                    .unwrap()
                    .resource_payloads
                    .get_mut(&last.1)
                    .unwrap()
                    .pointer
                    .domain = crate::VirPointerDomain::Allocation
            }
            7 => {
                objects
                    .get_mut(&last.0)
                    .unwrap()
                    .resource_payloads
                    .get_mut(&last.1)
                    .unwrap()
                    .pointer
                    .view_range = None
            }
            8 => {
                let source = records[0].source;
                records.last_mut().unwrap().source = source;
            }
            _ => unreachable!(),
        }
        let before = payloads(&objects);
        let source_before = source.clone();
        assert!(
            target
                .restore_stored_parameters(
                    &mut source,
                    &mut objects,
                    &unit.memory,
                    &mut outgoing_frame,
                    &records,
                    &locations.iter().copied().collect(),
                    &[],
                    limits,
                    span
                )
                .is_err()
        );
        assert_eq!(target, callee);
        assert_eq!(source, source_before);
        assert_eq!(payloads(&objects), before);
    }
    // Stored -> SSA transfers the original caller token, including shared
    // authority; no alias is minted and the callee keeps no live carrier.
    for mutation in 0..6 {
        let mut objects = allocations.clone();
        let mut source = caller.clone();
        let mut target = callee.clone();
        let mut outgoing = frame.clone();
        let record = returns.last().unwrap();
        let payload = objects
            .get_mut(&last.0)
            .unwrap()
            .resource_payloads
            .remove(&last.1)
            .unwrap();
        let pointer = VirValueId::new(9000);
        let permission = VirValueId::new(9001);
        let result = VirValueId::new(9002);
        outgoing
            .values
            .insert(pointer, VirRuntimeValue::Pointer(payload.pointer));
        outgoing
            .values
            .insert(permission, VirRuntimeValue::Permission(payload.permission));
        outgoing.set_loan_authority(permission, payload.loan_authority.unwrap());
        let mut exit = RuntimeStoredValueExit {
            source: record.source,
            pointer,
            permission,
            caller_result: result,
        };
        match mutation {
            0 => {}
            1 => {
                objects
                    .get_mut(&last.0)
                    .unwrap()
                    .resource_payloads
                    .insert(last.1, payload);
            }
            2 => {
                exit.source = returns[0].source;
            }
            3 => {
                outgoing.set_loan_authority(permission, record.caller);
            }
            4 => {
                exit.permission = VirValueId::new(9003);
            }
            5 => {
                let mut wrong = payload.pointer;
                wrong.offset_bytes += 1;
                outgoing
                    .values
                    .insert(pointer, VirRuntimeValue::Pointer(wrong));
            }
            _ => unreachable!(),
        }
        let before_objects = payloads(&objects);
        let before_frame = outgoing.loan_authorities.clone();
        let receipt = target.restore_stored_parameters(
            &mut source,
            &mut objects,
            &unit.memory,
            &mut outgoing,
            &returns,
            &locations.iter().copied().collect(),
            &[exit],
            limits,
            span,
        );
        if mutation == 0 {
            let receipts = receipt.unwrap();
            assert_eq!(receipts.len(), 1);
            assert_eq!(receipts[0].value, result);
            assert_eq!(receipts[0].authority, record.caller);
            assert_eq!(receipts[0].permission, record.permission);
            assert_eq!(outgoing.loan_authority(permission), None);
            assert_eq!(
                target.loans[&record.callee.loan].activity,
                RuntimeLoanActivity::Ended
            );
            assert_eq!(source, caller);
        } else {
            assert!(receipt.is_err());
            assert_eq!(source, caller);
            assert_eq!(target, callee);
            assert_eq!(payloads(&objects), before_objects);
            assert_eq!(outgoing.loan_authorities, before_frame);
        }
    }
    // Expansion is derived from a genuine imported shared token. Restoring
    // several carriers must retain unpassed caller aliases and be atomic even
    // when the final alias exceeds the caller budget.
    for mutation in 0..11 {
        let mut objects = allocations.clone();
        let mut source = caller.clone();
        let mut target = callee.clone();
        let mut outgoing = frame.clone();
        let record = returns.last().unwrap();
        let pointer = VirValueId::new(9100);
        let permission = VirValueId::new(9101);
        let result = VirValueId::new(9102);
        let outside = if mode == crate::VirMutability::Const {
            Some(
                source
                    .alias_stored(
                        record.caller,
                        record.pointer,
                        record.reference,
                        limits,
                        span,
                    )
                    .unwrap(),
            )
        } else {
            None
        };
        let alias = if mode == crate::VirMutability::Const {
            target
                .alias_stored(
                    record.callee,
                    record.pointer,
                    record.reference,
                    limits,
                    span,
                )
                .unwrap()
        } else {
            // Corrupt a mutable callee directly: no public operation can mint
            // this second authority, and the return protocol must reject it.
            let forged = target.fresh_authority(record.callee.loan, span).unwrap();
            target
                .loans
                .get_mut(&record.callee.loan)
                .unwrap()
                .authorities
                .insert(forged.token);
            forged
        };
        outgoing
            .values
            .insert(pointer, VirRuntimeValue::Pointer(record.pointer));
        outgoing
            .values
            .insert(permission, VirRuntimeValue::Permission(record.permission));
        outgoing.set_loan_authority(permission, alias);
        let mut destinations = locations.iter().copied().collect::<BTreeSet<_>>();
        let mut budget = limits;
        match mutation {
            0 => {}
            1 => {
                let extra = target.alias_stored(
                    record.callee,
                    record.pointer,
                    record.reference,
                    limits,
                    span,
                );
                if mode == crate::VirMutability::Mutable {
                    assert!(extra.is_err());
                    continue;
                }
                let key = RuntimeResourcePayloadKey {
                    offset_bytes: 0,
                    access: record.reference,
                };
                objects.insert(9999, allocation(8));
                objects.get_mut(&9999).unwrap().resource_payloads.insert(
                    key,
                    RuntimeOwnedPayload {
                        pointer: record.pointer,
                        permission: record.permission,
                        loan_authority: Some(extra.unwrap()),
                    },
                );
                destinations.insert((9999, key));
            }
            2 => outgoing.set_loan_authority(permission, record.callee),
            3 => outgoing.set_loan_authority(permission, record.caller),
            4 => budget.aliases_per_loan = source.loans[&record.caller.loan].authorities.len(),
            5 => {
                destinations.remove(&last);
            }
            6 => {
                let mut changed = record.pointer;
                changed.domain = crate::VirPointerDomain::Allocation;
                outgoing
                    .values
                    .insert(pointer, VirRuntimeValue::Pointer(changed));
            }
            7 => {
                target
                    .loans
                    .get_mut(&record.callee.loan)
                    .unwrap()
                    .authorities
                    .remove(&alias.token);
            }
            8 => {
                outgoing.values.remove(&permission);
            }
            9 => {
                let mut changed = record.pointer;
                changed.paths = crate::VirPointerPaths::root(record.pointer.access);
                outgoing
                    .values
                    .insert(pointer, VirRuntimeValue::Pointer(changed));
            }
            10 => {
                objects.get_mut(&last.0).unwrap().alignment = 1;
            }
            _ => unreachable!(),
        }
        let before_source = source.clone();
        let before_target = target.clone();
        let before_objects = payloads(&objects);
        let before_frame = outgoing.loan_authorities.clone();
        let receipt = target.restore_stored_parameters(
            &mut source,
            &mut objects,
            &unit.memory,
            &mut outgoing,
            &returns,
            &destinations,
            &[RuntimeStoredValueExit {
                source: record.source,
                pointer,
                permission,
                caller_result: result,
            }],
            budget,
            span,
        );
        if mode == crate::VirMutability::Const && mutation < 2 {
            let receipts = receipt.unwrap();
            assert_eq!(receipts.len(), 1);
            assert_eq!(receipts[0].value, result);
            let authorities = &source.loans[&record.caller.loan].authorities;
            assert_eq!(authorities.len(), if mutation == 0 { 3 } else { 4 });
            assert!(authorities.contains(&outside.unwrap().token));
            assert!(authorities.contains(&receipts[0].authority.token));
            let stored = objects[&last.0].resource_payloads[&last.1]
                .loan_authority
                .unwrap();
            assert_ne!(stored.token, receipts[0].authority.token);
            assert_eq!(
                target.loans[&record.callee.loan].activity,
                RuntimeLoanActivity::Ended
            );
            assert_eq!(outgoing.loan_authority(permission), None);
        } else {
            assert!(receipt.is_err(), "mode {mode:?} mutation {mutation}");
            assert_eq!(source, before_source);
            assert_eq!(target, before_target);
            assert_eq!(payloads(&objects), before_objects);
            assert_eq!(outgoing.loan_authorities, before_frame);
        }
    }
    // An ended stored borrow retires the caller's actual token; surviving fields restore theirs.
    let mut ended = callee.clone();
    let mut ended_caller = caller.clone();
    let mut ended_objects = allocations.clone();
    let record = returns.last().unwrap();
    ended
        .end_stored(record.callee, record.pointer, record.reference, span)
        .unwrap();
    ended_objects
        .get_mut(&last.0)
        .unwrap()
        .resource_payloads
        .remove(&last.1);
    ended
        .restore_stored_parameters(
            &mut ended_caller,
            &mut ended_objects,
            &unit.memory,
            &mut frame.clone(),
            &returns,
            &locations.iter().copied().collect(),
            &[],
            limits,
            span,
        )
        .unwrap();
    assert_eq!(
        ended_caller.loans[&record.caller.loan].activity,
        RuntimeLoanActivity::Ended
    );
    assert!(
        ended_caller.loans[&record.caller.loan]
            .authorities
            .is_empty()
    );
    callee
        .restore_stored_parameters(
            &mut caller,
            &mut allocations,
            &unit.memory,
            &mut frame.clone(),
            &returns,
            &locations.iter().copied().collect(),
            &[],
            limits,
            span,
        )
        .unwrap();
    assert_eq!(caller, original_caller);
    assert_eq!(payloads(&allocations), original_payloads);
    assert!(
        callee
            .loans
            .values()
            .all(|l| l.activity == RuntimeLoanActivity::Ended && l.authorities.is_empty())
    );
}
