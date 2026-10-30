//! Canonical field loans leave through checked returned buffers or restored parameter storage.
use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[allow(clippy::too_many_arguments)]
pub(in crate::verifier) fn field_export_statuses(
    state: &ResourceState,
    function: VirFunctionId,
    borrows: &VirBorrowEnvironment,
    abi: &VirAbiSignature,
    memory: &VirMemorySchema,
    inputs: &[VirValueId],
    values: &[VirValueId],
    predicate_payloads: &BTreeSet<AbstractAllocationId>,
) -> Option<BTreeMap<VirLoanId, ObligationStatus>> {
    let regions = borrows
        .regions()
        .iter()
        .filter(|r| {
            r.owner == function && matches!(r.origin, VirBorrowRegionOrigin::ParameterField { .. })
        })
        .collect::<Vec<_>>();
    if regions.is_empty() {
        return Some(BTreeMap::new());
    }
    let accesses = abi
        .parameters()
        .iter()
        .map(|p| p.value().access())
        .collect::<Option<Vec<_>>>()?;
    let entries = crate::vir::plan_parameter_reference_entries(memory, &accesses)?;
    if entries.len() != regions.len() {
        return None;
    }
    let mut destinations = BTreeSet::new();
    // A heap/local payload is not an export by itself. Its exact typed leaf
    // must be inside a caller-supplied parameter or hidden result buffer,
    // returned with a live permission covering that whole object.
    for (parameter, binding) in abi
        .parameters()
        .iter()
        .enumerate()
        .map(|(i, b)| (Some(i), b))
        .chain(abi.results().iter().map(|b| (None, b)))
    {
        let (access, borrowed) = match binding.value() {
            VirAbiValue::IndirectAggregate { access } => (*access, false),
            VirAbiValue::Pointer { pointee, .. } if binding.interface().transfer.is_borrow() => {
                (*pointee, true)
            }
            VirAbiValue::Pointer { pointee, .. }
                if binding.interface().transfer == crate::VirInterfaceTransfer::Move
                    && binding.parameter_slots().is_empty() =>
            {
                (*pointee, false)
            }
            _ => continue,
        };
        let shape = memory.object_shape(access).ok()?;
        if !shape
            .resource_leaves()
            .iter()
            .any(|l| l.kind() == VirPointerKind::Reference)
        {
            continue;
        }
        let (pointer, permission) = match (binding.parameter_slots(), binding.result_slots()) {
            ([pointer, _], [permission]) => (
                inputs.get(*pointer as usize),
                values.get(*permission as usize),
            ),
            ([], [pointer, permission]) => (
                values.get(*pointer as usize),
                values.get(*permission as usize),
            ),
            (_, []) => continue,
            _ => return None,
        };
        let Some(AbstractValue::Permission(permission)) = permission.and_then(|v| state.value(*v))
        else {
            continue;
        };
        // Entry SSA IDs need not survive a CFG edge. A restored borrowed
        // parameter retains its exact imported footprint in the actual loan.
        // Use that identity, never an allocation guessed from a field address.
        let location = match pointer.and_then(|v| state.value(*v)) {
            Some(AbstractValue::Pointer(p)) if p.memory_access() == Some(access) => p
                .offset_bytes()
                .exact_value()
                .map(|base| (p.provenance(), base)),
            _ if borrowed => parameter.and_then(|index| {
                let id = crate::vir::interface_loan_id(index as u32);
                if permission.authority() != PermissionAuthority::Loan(id) {
                    return None;
                }
                let loan = state.loan(id)?;
                let footprint = loan.footprint()?;
                let AbstractByteRange::Exact(range) = footprint.range else {
                    return None;
                };
                (footprint.access == access
                    && range.end() - range.start() == shape.size_bytes()
                    && footprint.provenance == loan.provenance())
                .then_some((loan.provenance(), range.start()))
            }),
            _ => None,
        };
        let Some((provenance @ AbstractProvenance::Known(storage), base)) = location else {
            continue;
        };
        let Some(allocation) = state.allocation(storage) else {
            continue;
        };
        let Some(end) = base.checked_add(shape.size_bytes()) else {
            continue;
        };
        let AbstractByteRange::Exact(range) = permission.range() else {
            continue;
        };
        if !shape.variants().is_empty()
            || allocation.liveness() != LivenessState::Live
            || end > allocation.size_bytes()
            || permission.provenance() != provenance
            || permission.availability() != PermissionAvailability::Available
            || if borrowed {
                match permission.authority() {
                    PermissionAuthority::Loan(id) => {
                        !super::exported_authority(state, id, values, abi)
                    }
                    _ => true,
                }
            } else {
                permission.access() != AccessPermission::Write
                    || permission.authority() != PermissionAuthority::Owner
            }
            || range.start() > base
            || range.end() < end
            || range.end() > allocation.size_bytes()
        {
            continue;
        }
        for leaf in shape
            .resource_leaves()
            .iter()
            .filter(|l| l.kind() == VirPointerKind::Reference)
        {
            destinations.insert((
                storage,
                ResourcePayloadKey::new(
                    base.checked_add(leaf.bytes().start_bytes())?,
                    leaf.access(),
                ),
            ));
        }
    }
    let mut statuses = BTreeMap::new();
    for entry in entries {
        let mut matching = regions.iter().filter(|r| {
            r.origin
                == VirBorrowRegionOrigin::ParameterField {
                    index: entry.parameter,
                    slot: entry.slot,
                }
        });
        let region = matching.next()?;
        if matching.next().is_some() {
            return None;
        }
        let status = if state
            .loan(entry.loan)
            .is_none_or(|loan| loan.region() != region.id || loan.parent().is_some())
        {
            ObligationStatus::Refuted
        } else if let Some(status) = field_value_export_status(
            state,
            memory,
            abi,
            values,
            entry,
            &destinations,
            predicate_payloads,
        ) {
            status
        } else {
            stored_export_status(
                state,
                memory,
                entry.loan,
                entry.pointee,
                &destinations,
                predicate_payloads,
            )
        };
        statuses.insert(entry.loan, status);
    }
    Some(statuses)
}

pub(in crate::verifier) fn stored_export_status(
    state: &ResourceState,
    memory: &VirMemorySchema,
    id: VirLoanId,
    pointee: VirMemoryAccess,
    destinations: &BTreeSet<(AbstractAllocationId, ResourcePayloadKey)>,
    predicate_payloads: &BTreeSet<AbstractAllocationId>,
) -> ObligationStatus {
    carrier_export_status(
        state,
        memory,
        id,
        pointee,
        destinations,
        predicate_payloads,
        &BTreeSet::new(),
    )
}

fn carrier_export_status(
    state: &ResourceState,
    memory: &VirMemorySchema,
    id: VirLoanId,
    pointee: VirMemoryAccess,
    destinations: &BTreeSet<(AbstractAllocationId, ResourcePayloadKey)>,
    predicate_payloads: &BTreeSet<AbstractAllocationId>,
    exported_values: &BTreeSet<VirValueId>,
) -> ObligationStatus {
    let Some(loan) = state.loan(id) else {
        return ObligationStatus::Refuted;
    };
    if state.values().iter().any(|(v, fact)| matches!(fact, AbstractValue::Permission(p)
        if p.authority() == PermissionAuthority::Loan(id) && p.availability() != PermissionAvailability::Consumed) && !exported_values.contains(v))
        || state.loans().values().any(|child| child.parent() == Some(id) && child.activity() != LoanActivity::Ended)
    { return ObligationStatus::Refuted; }
    let mut carriers = Vec::new();
    for (storage, allocation) in state.allocations() {
        for (key, value) in allocation.object_state().resource_payloads() {
            if let MovePathState::Available(payload) = value
                && payload.permission().authority() == PermissionAuthority::Loan(id)
            {
                carriers.push((*storage, *key, payload));
            }
        }
    }
    use crate::verifier::resource::AbstractLoanAuthority as Authority;
    let actual = carriers
        .iter()
        .map(|(a, k, _)| Authority::stored(*a, *k))
        .chain(exported_values.iter().copied().map(Authority::value))
        .collect::<BTreeSet<_>>();
    if actual != *loan.authorities() || (loan.kind() == VirLoanKind::Mutable && actual.len() > 1) {
        return ObligationStatus::Refuted;
    }
    match loan.activity() {
        LoanActivity::Ended if actual.is_empty() => ObligationStatus::Proven,
        LoanActivity::Active if !actual.is_empty() => {
            let mut status = ObligationStatus::Proven;
            for (storage, key, payload) in carriers {
                if !destinations.contains(&(storage, key))
                    || payload.pointer().memory_access() != Some(pointee)
                {
                    return ObligationStatus::Refuted;
                }
                let next = super::super::transfer::aggregate_abi_payload_status(
                    state,
                    memory,
                    key.access(),
                    payload,
                    Some((storage, key)),
                    matches!(payload.pointer().provenance(), AbstractProvenance::Known(a) if predicate_payloads.contains(&a)),
                );
                if next == ObligationStatus::Refuted {
                    return next;
                }
                if !next.is_proven() {
                    status = next;
                }
            }
            status
        }
        LoanActivity::MaybeActive => ObligationStatus::Unknown,
        _ => ObligationStatus::Refuted,
    }
}

/// Match an observed SSA carrier to a declared source, never infer authority
/// from a returned address. Other fields still need Stored/Ended dispositions.
fn field_value_export_status(
    state: &ResourceState,
    memory: &VirMemorySchema,
    abi: &VirAbiSignature,
    values: &[VirValueId],
    entry: crate::vir::ParameterReferenceEntry,
    destinations: &BTreeSet<(AbstractAllocationId, ResourcePayloadKey)>,
    predicate_payloads: &BTreeSet<AbstractAllocationId>,
) -> Option<ObligationStatus> {
    let carriers = state.values().iter().filter_map(|(id, value)|
        matches!(value, AbstractValue::Permission(p) if p.authority() == PermissionAuthority::Loan(entry.loan)
            && p.availability() != PermissionAvailability::Consumed).then_some(*id)
    ).collect::<Vec<_>>();
    if carriers.is_empty() {
        return None;
    }
    let invalid = Some(ObligationStatus::Refuted);
    let [permission] = carriers.as_slice() else {
        return invalid;
    };
    let path = crate::verifier::summary::ResourceName::Input {
        parameter: entry.pointer_slot as usize,
        payload_offsets: vec![entry.offset_bytes],
    };
    let Some((pointer_slot, permission_slot)) =
        crate::verifier::summary::field_return_slots(memory, abi, &path)
    else {
        return invalid;
    };
    if values.get(permission_slot) != Some(permission) {
        return invalid;
    }
    let storage_status = carrier_export_status(
        state,
        memory,
        entry.loan,
        entry.pointee,
        destinations,
        predicate_payloads,
        &BTreeSet::from([*permission]),
    );
    if !storage_status.is_proven() {
        return Some(storage_status);
    }
    let Some(pointer) = values.get(pointer_slot) else {
        return invalid;
    };
    Some(super::super::transfer::reference_ssa_export_status(
        state,
        memory,
        entry.reference,
        *pointer,
        *permission,
    ))
}
