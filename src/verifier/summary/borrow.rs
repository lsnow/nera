//! Loan authority substitution is independent of pointer/address substitution.
//! A body world may export only the actual caller token admitted by the ABI;
//! it cannot activate a parent, introduce a callee-local loan, or mint an owner.
use super::*;
use crate::verifier::{AbstractValue, PermissionAuthority};

/// Physical result slots for an explicitly declared whole field source.
/// The input path is rooted in a physical parameter, not a logical index.
pub(in crate::verifier) fn field_return_slots(
    memory: &crate::VirMemorySchema,
    abi: &crate::VirAbiSignature,
    input: &ResourceName,
) -> Option<(usize, usize)> {
    let parameters = abi
        .parameters()
        .iter()
        .map(|b| b.value().access())
        .collect::<Option<Vec<_>>>()?;
    let results = abi
        .results()
        .iter()
        .map(|b| b.value().access())
        .collect::<Option<Vec<_>>>()?;
    for relation in abi
        .borrow_result()
        .into_iter()
        .chain(abi.borrow_result_alternatives().iter().map(|a| a.relation))
        .filter(|r| r.parameter_field.is_some())
    {
        let entry =
            crate::vir::plan_parameter_field_result(memory, &parameters, &results, relation)?;
        if *input
            != (ResourceName::Input {
                parameter: entry.pointer_slot as usize,
                payload_offsets: vec![entry.offset_bytes],
            })
        {
            continue;
        }
        let [pointer, permission] = abi.results().get(relation.result as usize)?.result_slots()
        else {
            return None;
        };
        return Some((*pointer as usize, *permission as usize));
    }
    None
}

pub(super) fn is_input_location(input: &ResourceName, location: &StoredBorrowLocation) -> bool {
    let ResourceName::Input {
        parameter,
        payload_offsets,
    } = input
    else {
        return false;
    };
    let Some((&offset, parent)) = payload_offsets.split_last() else {
        return false;
    };
    location.offset == offset
        && location.resource
            == (ResourceName::Input {
                parameter: *parameter,
                payload_offsets: parent.to_vec(),
            })
}

/// Resolve each allocation boundary from the physical parameter's canonical
/// layout. Offsets select complete resource leaves, not arbitrary pointer-size
/// byte ranges. Inline aggregate fields are already flattened by object_shape.
pub(super) fn input_payload_field(
    memory: &crate::VirMemorySchema,
    parameters: &[crate::VirType],
    path: &ResourceName,
) -> Option<crate::VirMemoryAccess> {
    let ResourceName::Input {
        parameter,
        payload_offsets,
    } = path
    else {
        return None;
    };
    if payload_offsets.is_empty() || payload_offsets.len() > 16 {
        return None;
    }
    let crate::VirType::Pointer { access } = parameters.get(*parameter)? else {
        return None;
    };
    let mut current = *access;
    for (index, offset) in payload_offsets.iter().enumerate() {
        let shape = memory.object_shape(current).ok()?;
        if !shape.variants().is_empty() {
            return None;
        }
        let mut leaves = shape
            .resource_leaves()
            .iter()
            .filter(|leaf| leaf.bytes().start_bytes() == *offset);
        let leaf = leaves.next()?;
        if leaves.next().is_some() {
            return None;
        }
        let crate::VirMemoryTypeKind::Pointer { kind, pointee, .. } =
            memory.kind(leaf.access().ty)?
        else {
            return None;
        };
        if index + 1 == payload_offsets.len() {
            return (*kind == crate::VirPointerKind::Reference).then_some(leaf.access());
        }
        if *kind == crate::VirPointerKind::Raw {
            return None;
        }
        current = memory.access(*pointee)?;
    }
    None
}

/// A stored loan inhabits a reference leaf of the matching pointee and access
/// strength. A typed pointer slot alone is not evidence of loan authority.
pub(super) fn stored_reference_shape(
    memory: &crate::VirMemorySchema,
    field: crate::VirMemoryAccess,
    pointee_access: Option<crate::VirMemoryAccess>,
    access: AccessPermission,
    free: FreeCapability,
) -> bool {
    let Some(crate::VirMemoryTypeKind::Pointer {
        kind: crate::VirPointerKind::Reference,
        pointee,
        mutability,
    }) = memory.kind(field.ty)
    else {
        return false;
    };
    memory.resolves_access(field)
        && pointee_access.is_some_and(|a| memory.access(*pointee) == Some(a))
        && free == FreeCapability::No
        && access
            == match mutability {
                crate::VirMutability::Mutable => AccessPermission::Write,
                crate::VirMutability::Const => AccessPermission::Read,
            }
}

fn stored_field_fits(
    memory: &crate::VirMemorySchema,
    allocation: &crate::verifier::AbstractAllocation,
    key: crate::verifier::ResourcePayloadKey,
) -> bool {
    memory.resolves_access(key.access())
        && memory.layout(key.access().layout).is_some_and(|layout| {
            key.offset_bytes()
                .checked_add(layout.size_bytes)
                .is_some_and(|end| end <= allocation.size_bytes())
                && key.offset_bytes().is_multiple_of(layout.alignment)
                && allocation.alignment().bytes() >= layout.alignment
        })
}

/// One actual input carrier, not just its loan ID. Shared aliases may have the
/// same loan while each source and destination remains linear.
pub(super) struct FieldExport {
    pub loan: crate::VirLoanId,
    pub source: (
        crate::verifier::AbstractAllocationId,
        crate::verifier::ResourcePayloadKey,
    ),
    pub exit: crate::BoundaryExit<
        (
            crate::verifier::AbstractAllocationId,
            crate::verifier::ResourcePayloadKey,
        ),
        (
            crate::VirValueId,
            crate::verifier::AbstractPointer,
            crate::verifier::AbstractPermission,
        ),
    >,
}

/// Validate every alias against its actual input and declared output before
/// publishing any authority changes. No destination is guessed by loan ID.
pub(super) fn restore_field_group(
    memory: &crate::VirMemorySchema,
    before: &crate::verifier::ResourceState,
    output: &mut crate::verifier::ResourceState,
    exports: &[FieldExport],
) -> bool {
    use crate::verifier::resource::AbstractLoanAuthority as Authority;
    use crate::verifier::{AbstractProvenance, LivenessState, MovePathState};
    use std::collections::{BTreeMap, BTreeSet};
    let mut sources = BTreeSet::new();
    let mut destinations = BTreeSet::new();
    let mut expected = BTreeMap::new();
    let mut pending_values = BTreeSet::new();
    for export in exports {
        let id = export.loan;
        let (storage, key) = export.source;
        let authority = Authority::stored(storage, key);
        let Some(loan) = before.loan(id) else {
            return false;
        };
        if loan.activity() != LoanActivity::Active
            || output.loan(id) != Some(loan)
            || !loan.authorities().contains(&authority)
            || !sources.insert(authority)
            || (loan.kind() == crate::VirLoanKind::Mutable && loan.authorities().len() != 1)
            || output
                .loans()
                .values()
                .any(|child| child.parent() == Some(id) && child.activity() != LoanActivity::Ended)
        {
            return false;
        }
        let Some(container) = before.allocation(storage) else {
            return false;
        };
        let MovePathState::Available(payload) = container.resource_payload(key) else {
            return false;
        };
        let permission = payload.permission();
        if container.liveness() != LivenessState::Live
            || !stored_field_fits(memory, container, key)
            || !stored_reference_shape(
                memory,
                key.access(),
                payload.pointer().memory_access(),
                permission.access(),
                permission.free_capability(),
            )
            || permission.authority() != PermissionAuthority::Loan(id)
            || permission.availability() != PermissionAvailability::Available
            || permission.provenance() != loan.provenance()
            || payload.pointer().provenance() != loan.provenance()
            || permission.range() != loan.actual_range()
            || permission.access()
                != if loan.kind() == crate::VirLoanKind::Shared {
                    AccessPermission::Read
                } else {
                    AccessPermission::Write
                }
            || !matches!(loan.provenance(), AbstractProvenance::Known(referent)
                if output.allocation(referent).is_some_and(|a| a.liveness() == LivenessState::Live))
        {
            return false;
        }
        expected
            .entry(id)
            .or_insert_with(|| loan.authorities().clone())
            .remove(&authority);
    }
    for export in exports {
        let (storage, key) = export.source;
        let MovePathState::Available(source) =
            before.allocation(storage).unwrap().resource_payload(key)
        else {
            return false;
        };
        if matches!(export.exit, crate::BoundaryExit::Shared { .. })
            && (before.loan(export.loan).unwrap().kind() != crate::VirLoanKind::Shared
                || export.exit.stored().len() + export.exit.values().len() < 2)
        {
            return false;
        }
        let targets =
            export.exit.stored().iter().copied().chain(
                matches!(export.exit, crate::BoundaryExit::InPlace).then_some((storage, key)),
            );
        for (allocation, target_key) in targets {
            let Some(container) = output.allocation(allocation) else {
                return false;
            };
            let MovePathState::Available(target) = container.resource_payload(target_key) else {
                return false;
            };
            if container.liveness() != LivenessState::Live
                || !stored_field_fits(memory, container, target_key)
                || !stored_reference_shape(
                    memory,
                    target_key.access(),
                    target.pointer().memory_access(),
                    target.permission().access(),
                    target.permission().free_capability(),
                )
                || !same_field_view(&source, target.pointer(), target.permission())
            {
                return false;
            }
            let receiver = Authority::stored(allocation, target_key);
            if !destinations.insert(receiver)
                || !expected.get_mut(&export.loan).unwrap().insert(receiver)
            {
                return false;
            }
        }
        for &(value, pointer, permission) in export.exit.values() {
            if output.value(value).is_some()
                || !same_field_view(&source, pointer, permission)
                || !pending_values.insert(value)
            {
                return false;
            }
            let receiver = Authority::value(value);
            if !destinations.insert(receiver)
                || !expected.get_mut(&export.loan).unwrap().insert(receiver)
            {
                return false;
            }
        }
    }
    for export in exports {
        let (storage, key) = export.source;
        if !destinations.contains(&Authority::stored(storage, key))
            && output
                .allocation(storage)
                .is_none_or(|a| a.resource_payload(key) != MovePathState::Moved)
        {
            return false;
        }
    }
    // Check exact conservation, including caller aliases outside this call.
    // Pending SSA results are defined by call transfer after this transaction.
    for (&id, authorities) in &expected {
        let mut observed = BTreeSet::new();
        for (allocation, object) in output.allocations() {
            for (key, state) in object.object_state().resource_payloads() {
                if let MovePathState::Available(payload) = state
                    && payload.permission().authority() == PermissionAuthority::Loan(id)
                {
                    observed.insert(Authority::stored(*allocation, *key));
                }
            }
        }
        for (value, fact) in output.values() {
            if matches!(fact, AbstractValue::Permission(p) if p.authority() == PermissionAuthority::Loan(id)
                && p.availability() != PermissionAvailability::Consumed)
            {
                observed.insert(Authority::value(*value));
            }
        }
        let present = authorities
            .iter()
            .copied()
            .filter(|a| !matches!(a, Authority::Value(v) if pending_values.contains(v)))
            .collect::<BTreeSet<_>>();
        if observed != present {
            return false;
        }
        for authority in authorities.iter().filter(|a| !destinations.contains(a)) {
            let unchanged = match *authority {
                Authority::Stored {
                    allocation,
                    payload,
                } => before
                    .allocation(allocation)
                    .zip(output.allocation(allocation))
                    .is_some_and(|(a, b)| {
                        a.liveness() == b.liveness()
                            && a.resource_payload(payload) == b.resource_payload(payload)
                    }),
                Authority::Value(value) => before.value(value) == output.value(value),
            };
            if !unchanged {
                return false;
            }
        }
    }
    let mut next = output.clone();
    let mut ended = BTreeSet::new();
    for (id, authorities) in expected {
        if authorities.is_empty()
            && next.loan(id).unwrap().parent().is_some_and(|parent| {
                next.loan(parent).is_none_or(|p| {
                    !matches!(p.activity(), LoanActivity::Active | LoanActivity::Suspended)
                })
            })
        {
            return false;
        }
        let loan = next.loan_mut(id).unwrap();
        for authority in loan.authorities().clone() {
            match authority {
                Authority::Stored {
                    allocation,
                    payload,
                } => {
                    loan.remove_stored_authority(allocation, payload);
                }
                Authority::Value(value) => {
                    loan.remove_authority(value);
                }
            }
        }
        for authority in authorities {
            match authority {
                Authority::Stored {
                    allocation,
                    payload,
                } => loan.add_stored_authority(allocation, payload),
                Authority::Value(value) => loan.add_authority(value),
            }
        }
        if loan.authorities().is_empty() {
            loan.set_activity(LoanActivity::Ended);
            ended.insert(id);
        }
    }
    for id in &ended {
        if let Some(parent) = next.loan(*id).unwrap().parent()
            && !next
                .loans()
                .values()
                .any(|l| l.parent() == Some(parent) && l.activity() != LoanActivity::Ended)
            && let Some(parent) = next.loan_mut(parent)
            && parent.activity() == LoanActivity::Suspended
        {
            parent.set_activity(LoanActivity::Active);
        }
    }
    if next.restore_ended_predicate_lenders(&ended).is_err() {
        return false;
    }
    *output = next;
    true
}

fn same_field_view(
    source: &crate::verifier::TypedResourcePayload,
    pointer: crate::verifier::AbstractPointer,
    permission: crate::verifier::AbstractPermission,
) -> bool {
    pointer.provenance() == source.pointer().provenance()
        && pointer.offset_bytes().exact_value().is_some()
        && pointer.offset_bytes() == source.pointer().offset_bytes()
        && pointer.domain() == source.pointer().domain()
        && pointer.paths() == source.pointer().paths()
        && pointer.memory_access() == source.pointer().memory_access()
        && permission == source.permission()
}

#[cfg(test)]
fn restore_field_exports(
    memory: &crate::VirMemorySchema,
    before: &crate::verifier::ResourceState,
    output: &mut crate::verifier::ResourceState,
    loans: &std::collections::BTreeSet<crate::VirLoanId>,
    ended: &std::collections::BTreeSet<crate::VirLoanId>,
    values: &std::collections::BTreeMap<
        crate::VirLoanId,
        (
            crate::VirValueId,
            crate::verifier::AbstractPointer,
            crate::verifier::AbstractPermission,
        ),
    >,
) -> bool {
    use crate::verifier::MovePathState;
    use crate::verifier::resource::AbstractLoanAuthority as Authority;
    if !ended.is_subset(loans)
        || values
            .keys()
            .any(|id| !loans.contains(id) || ended.contains(id))
    {
        return false;
    }
    let mut exports = Vec::new();
    for id in loans {
        let Some(loan) = before.loan(*id) else {
            return false;
        };
        let authorities = loan.authorities().iter().copied().collect::<Vec<_>>();
        let [
            Authority::Stored {
                allocation,
                payload,
            },
        ] = authorities.as_slice()
        else {
            return false;
        };
        let source = (*allocation, *payload);
        let exit = if ended.contains(id) {
            crate::BoundaryExit::Ended
        } else if let Some(value) = values.get(id) {
            crate::BoundaryExit::Value(*value)
        } else {
            let targets = output.allocations().iter().flat_map(|(a, object)| object.object_state().resource_payloads().iter().filter_map(move |(k, v)|
                    matches!(v, MovePathState::Available(p) if p.permission().authority() == PermissionAuthority::Loan(*id)).then_some((*a, *k)))).collect::<Vec<_>>();
            let [target] = targets.as_slice() else {
                return false;
            };
            if *target == source {
                crate::BoundaryExit::InPlace
            } else {
                crate::BoundaryExit::Stored(*target)
            }
        };
        exports.push(FieldExport {
            loan: *id,
            source,
            exit,
        });
    }
    restore_field_group(memory, before, output, &exports)
}

#[cfg(test)]
fn restore_stored_exports(
    memory: &crate::VirMemorySchema,
    before: &crate::verifier::ResourceState,
    output: &mut crate::verifier::ResourceState,
    loans: &std::collections::BTreeSet<crate::VirLoanId>,
    ended: &std::collections::BTreeSet<crate::VirLoanId>,
) -> bool {
    restore_field_exports(memory, before, output, loans, ended, &Default::default())
}

pub(super) fn validate_exports(
    world: &ReturnWorld,
    cx: &CallInstantiation<'_>,
    values: &[AbstractValue],
) -> bool {
    let Some(abi) = &cx.target.abi else {
        return world.borrow_restoration.is_empty()
            && !values.iter().any(|v| {
                matches!(v, AbstractValue::Permission(p)
                if matches!(p.authority(), PermissionAuthority::Loan(_)))
            });
    };
    let mut permissions = std::collections::BTreeSet::new();
    let mut export_slots = std::collections::BTreeSet::new();
    for (index, binding) in abi.parameters().iter().enumerate() {
        if !binding.interface().transfer.is_borrow() {
            continue;
        }
        let Some(&slot) = binding.parameter_slots().last() else {
            return false;
        };
        let slot = slot as usize;
        let Some(&argument) = cx.arguments.get(slot) else {
            return false;
        };
        let Some(AbstractValue::Permission(input)) = cx.before.value(argument) else {
            return false;
        };
        let PermissionAuthority::Loan(id) = input.authority() else {
            return false;
        };
        let Some(loan) = cx.before.loan(id) else {
            return false;
        };
        if loan.activity() != LoanActivity::Active
            || !loan.has_value_authority(argument)
            || input.availability() != PermissionAvailability::Available
            || input.free_capability() != FreeCapability::No
        {
            return false;
        }
        permissions.insert(slot);
        let Some(restoration) = world
            .borrow_restoration
            .iter()
            .find(|r| r.input_permission == slot)
        else {
            return false;
        };
        if !matches!(
            restoration.activity,
            LoanActivity::Active | LoanActivity::Suspended
        ) || restoration.permission.authority != SummaryAuthority::InputLoan(slot)
        {
            return false;
        }
        for output in binding.result_slots().iter().copied() {
            export_slots.insert(output as usize);
            let Some(AbstractValue::Permission(returned)) = values.get(output as usize) else {
                return false;
            };
            if returned.authority() != input.authority()
                || returned.provenance() != input.provenance()
                || returned.access() != input.access()
                || returned.free_capability() != FreeCapability::No
                || returned.availability() != PermissionAvailability::Available
                // The current ABI restores the complete imported endpoint.
                // Restricted pointer views do not authorize a larger loan.
                || !cx.queries.contained(cx.before, input.range(), returned.range(), cx.limits).is_proven()
                || !cx.queries.contained(cx.before, returned.range(), input.range(), cx.limits).is_proven()
            {
                return false;
            }
        }
        if abi.borrow_result_parameters().contains(&index) {
            let Some(output) = abi.results()[0].result_slots().last().copied() else {
                return false;
            };
            let Some(AbstractValue::Permission(returned)) = values.get(output as usize) else {
                return false;
            };
            if returned.authority() == input.authority() {
                let projected = abi
                    .borrow_result()
                    .filter(|relation| relation.parameter as usize == index)
                    .is_some_and(|relation| relation.projection != crate::BorrowProjection::Whole);
                export_slots.insert(output as usize);
                if returned.provenance() != input.provenance()
                    || returned.access() != input.access()
                    || returned.free_capability() != FreeCapability::No
                    || returned.availability() != PermissionAvailability::Available
                    || !cx
                        .queries
                        .contained(cx.before, input.range(), returned.range(), cx.limits)
                        .is_proven()
                    || (!projected
                        && !cx
                            .queries
                            .contained(cx.before, returned.range(), input.range(), cx.limits)
                            .is_proven())
                {
                    return false;
                }
            }
        }
    }
    for restore in &world.stored_borrow_restoration {
        for &slot in restore.exit.values() {
            let Some((pointer, permission)) = field_return_slots(cx.memory, abi, &restore.input)
            else {
                return false;
            };
            if permission != slot
                || !matches!(values.get(pointer), Some(AbstractValue::Pointer(_)))
                || !matches!(values.get(slot), Some(AbstractValue::Permission(p))
                    if matches!(p.authority(), PermissionAuthority::Loan(_))
                        && p.availability() == PermissionAvailability::Available
                        && p.free_capability() == FreeCapability::No)
                || !export_slots.insert(slot)
            {
                return false;
            }
        }
    }
    world.borrow_restoration.len() == permissions.len()
        && world
            .borrow_restoration
            .iter()
            .all(|r| permissions.contains(&r.input_permission))
        && values.iter().enumerate().all(|(slot, value)| {
            !matches!(value,
            AbstractValue::Permission(p) if matches!(p.authority(), PermissionAuthority::Loan(_))
                && !export_slots.contains(&slot))
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verifier::relation::audit::QueryLog;
    use crate::{SourceFile, VirInstruction};

    #[test]
    fn shared_field_group_preserves_each_alias_and_unpassed_carrier() {
        use crate::verifier::resource::AbstractLoanAuthority as Authority;
        use crate::verifier::{
            AbstractAllocation, AbstractAllocationId, AbstractByteRange, AbstractLoan,
            AbstractPermission, AbstractPointer, AbstractProvenance, GuaranteedAlignment,
            MovePathState, ResourcePayloadKey, ResourceState, TypedResourcePayload,
        };
        use std::collections::BTreeSet;
        let output = crate::analyze(&SourceFile::from_text(
            "shared-fields.nera",
            "fn read(p:&u64)->u64{return *p;} fn main()->u64{return 0;}",
        ));
        let memory = &output.vir().unwrap().as_unit().memory;
        let reference = memory
            .types
            .iter()
            .find_map(|t| {
                matches!(
                    t.kind,
                    crate::VirMemoryTypeKind::Pointer {
                        kind: crate::VirPointerKind::Reference,
                        mutability: crate::VirMutability::Const,
                        ..
                    }
                )
                .then(|| memory.access(t.id).unwrap())
            })
            .unwrap();
        let crate::VirMemoryTypeKind::Pointer { pointee, .. } = memory.kind(reference.ty).unwrap()
        else {
            unreachable!()
        };
        let pointee = memory.access(*pointee).unwrap();
        let source = AbstractAllocationId::new(40);
        let target = AbstractAllocationId::new(41);
        let referent = AbstractAllocationId::new(42);
        let id = crate::VirLoanId::new(43);
        let outside = crate::VirValueId::new(44);
        let result = crate::VirValueId::new(45);
        let keys = [
            ResourcePayloadKey::new(0, reference),
            ResourcePayloadKey::new(8, reference),
        ];
        let provenance = AbstractProvenance::Known(referent);
        let range = ByteRange::new(0, 8).unwrap();
        let pointer = AbstractPointer::new(
            provenance,
            U64Interval::exact(0),
            GuaranteedAlignment::new(8).unwrap(),
        )
        .with_memory_access(Some(pointee));
        let permission = AbstractPermission::new(
            provenance,
            AbstractByteRange::Exact(range),
            AccessPermission::Read,
            FreeCapability::No,
        )
        .with_authority(PermissionAuthority::Loan(id));
        let payload = TypedResourcePayload::new(pointer, permission);
        let mut before = ResourceState::new();
        for (allocation, size) in [(source, 16), (target, 16), (referent, 8)] {
            before
                .define_allocation(allocation, AbstractAllocation::new_local(size, 8).unwrap())
                .unwrap();
        }
        let mut loan = AbstractLoan::new(
            provenance,
            range,
            crate::VirLoanKind::Shared,
            crate::VirBorrowRegionId::new(0),
            None,
            LoanActivity::Active,
        )
        .with_authority(outside)
        .with_footprint(Some(crate::verifier::MemoryFootprint {
            provenance,
            access: pointee,
            stride_bytes: 8,
            range: AbstractByteRange::Exact(range),
            envelope: range,
        }));
        for key in keys {
            before
                .allocation_mut(source)
                .unwrap()
                .set_resource_payload(key, MovePathState::available(payload))
                .unwrap();
            loan.add_stored_authority(source, key);
        }
        before
            .define_value(outside, AbstractValue::Permission(permission))
            .unwrap();
        before.define_loan(id, loan).unwrap();
        for mode in 0..10 {
            let mut state = before.clone();
            for key in keys {
                state
                    .allocation_mut(source)
                    .unwrap()
                    .set_resource_payload(key, MovePathState::Moved)
                    .unwrap();
            }
            let mut exports = vec![
                FieldExport {
                    loan: id,
                    source: (source, keys[0]),
                    exit: crate::BoundaryExit::Value((result, pointer, permission)),
                },
                FieldExport {
                    loan: id,
                    source: (source, keys[1]),
                    exit: crate::BoundaryExit::Ended,
                },
            ];
            match mode {
                0 => {}
                1 => {
                    for (index, key) in keys.into_iter().enumerate() {
                        state
                            .allocation_mut(target)
                            .unwrap()
                            .set_resource_payload(key, MovePathState::available(payload))
                            .unwrap();
                        exports[index].exit = crate::BoundaryExit::Stored((target, key));
                    }
                }
                2 => {
                    exports[0].exit = crate::BoundaryExit::Ended;
                }
                3 => {
                    exports[1].source = exports[0].source;
                }
                4 => {
                    exports[1].exit = crate::BoundaryExit::Value((result, pointer, permission));
                }
                5 => {
                    state
                        .allocation_mut(target)
                        .unwrap()
                        .set_resource_payload(keys[0], MovePathState::available(payload))
                        .unwrap();
                }
                6..=9 => {
                    state
                        .allocation_mut(target)
                        .unwrap()
                        .set_resource_payload(keys[0], MovePathState::available(payload))
                        .unwrap();
                    exports[0].exit = crate::BoundaryExit::Shared {
                        stored: vec![(target, keys[0])],
                        values: vec![(result, pointer, permission)],
                    };
                    if let crate::BoundaryExit::Shared { stored, values } = &mut exports[0].exit {
                        match mode {
                            7 => {
                                stored.push(stored[0]);
                            }
                            8 => {
                                stored.clear();
                            }
                            9 => {
                                values.push(values[0]);
                            }
                            _ => {}
                        }
                    }
                }
                _ => unreachable!(),
            }
            let snapshot = state.clone();
            let accepted = restore_field_group(memory, &before, &mut state, &exports);
            if mode < 3 || mode == 6 {
                assert!(accepted);
                let mut expected = BTreeSet::from([Authority::value(outside)]);
                if mode == 0 || mode == 6 {
                    expected.insert(Authority::value(result));
                }
                if mode == 6 {
                    expected.insert(Authority::stored(target, keys[0]));
                }
                if mode == 1 {
                    for key in keys {
                        expected.insert(Authority::stored(target, key));
                    }
                }
                assert_eq!(state.loan(id).unwrap().authorities(), &expected);
                assert_eq!(state.loan(id).unwrap().activity(), LoanActivity::Active);
            } else {
                assert!(!accepted);
                assert_eq!(state, snapshot);
            }
        }
    }

    #[test]
    fn input_payload_paths_follow_typed_allocation_boundaries() {
        let output = crate::analyze(&SourceFile::from_text(
            "payload-paths.nera",
            "struct Leaf {tag:u64,view:&mut u64,}
             struct Root {prefix:u64,owned:Own<Leaf>,link:ptr<Leaf>,inline:Leaf,items:[Leaf;2],}
             fn main()->u64{return 0;} fn identity(p:Own<Root>)->Own<Root>{return p;}",
        ));
        let memory = &output.vir().unwrap().as_unit().memory;
        let root = memory
            .types
            .iter()
            .find_map(|ty| match &ty.kind {
                crate::VirMemoryTypeKind::Struct { fields } if fields.len() == 5 => Some(ty.id),
                _ => None,
            })
            .unwrap();
        let reference = memory
            .types
            .iter()
            .find_map(|ty| match &ty.kind {
                crate::VirMemoryTypeKind::Struct { fields } if fields.len() == 2 => {
                    memory.access(memory.field(fields[1])?.ty)
                }
                _ => None,
            })
            .unwrap();
        let parameters = [crate::VirType::Pointer {
            access: memory.access(root).unwrap(),
        }];
        let resolve = |offsets| {
            input_payload_field(
                memory,
                &parameters,
                &ResourceName::Input {
                    parameter: 0,
                    payload_offsets: offsets,
                },
            )
        };
        // Root layout: prefix=0, owned=8, link=16, inline=24, items=40.
        // Leaf.view is at byte 8. Inline fields and array elements do not
        // introduce an extra dereference into the payload path.
        for path in [vec![8, 8], vec![32], vec![48], vec![64]] {
            assert_eq!(resolve(path), Some(reference));
        }
        for path in [
            vec![],
            vec![0],
            vec![8],
            vec![16, 8],
            vec![9, 8],
            vec![24, 8],
            vec![32, 0],
            vec![u64::MAX],
            vec![0; 17],
        ] {
            assert_eq!(resolve(path), None);
        }
        assert_eq!(
            input_payload_field(
                memory,
                &[crate::VirType::Permission],
                &ResourceName::Input {
                    parameter: 0,
                    payload_offsets: vec![32]
                }
            ),
            None
        );
        assert_eq!(
            input_payload_field(memory, &parameters, &ResourceName::Fresh(0)),
            None
        );
        assert_eq!(
            input_payload_field(
                memory,
                &parameters,
                &ResourceName::Input {
                    parameter: 1,
                    payload_offsets: vec![32]
                }
            ),
            None
        );
    }

    #[test]
    fn stored_reference_shapes_distinguish_owners_raw_links_and_mutability() {
        let output = crate::analyze(&SourceFile::from_text(
            "stored-reference-shape.nera",
            "fn inspect(a:&u64,b:&mut u64,c:&mut bool,o:Own<u64>,p:ptr<u64>)->u64{free(o);return 0;} fn main()->u64{return 0;}",
        ));
        let memory = &output.vir().unwrap().as_unit().memory;
        let mut seen = [false; 4];
        for ty in &memory.types {
            let crate::VirMemoryTypeKind::Pointer {
                kind,
                pointee,
                mutability,
            } = ty.kind
            else {
                continue;
            };
            let field = memory.access(ty.id).unwrap();
            let pointee = memory.access(pointee).unwrap();
            let expected = if mutability == crate::VirMutability::Mutable {
                AccessPermission::Write
            } else {
                AccessPermission::Read
            };
            for access in [
                AccessPermission::Read,
                AccessPermission::Write,
                AccessPermission::MaybeWrite,
            ] {
                assert_eq!(
                    stored_reference_shape(
                        memory,
                        field,
                        Some(pointee),
                        access,
                        FreeCapability::No
                    ),
                    kind == crate::VirPointerKind::Reference && access == expected
                );
            }
            assert!(!stored_reference_shape(
                memory,
                field,
                None,
                expected,
                FreeCapability::No
            ));
            assert!(!stored_reference_shape(
                memory,
                field,
                Some(field),
                expected,
                FreeCapability::No
            ));
            for free in [FreeCapability::Yes, FreeCapability::Maybe] {
                assert!(!stored_reference_shape(
                    memory,
                    field,
                    Some(pointee),
                    expected,
                    free
                ));
            }
            seen[match (kind, mutability) {
                (crate::VirPointerKind::Own, _) => 0,
                (crate::VirPointerKind::Raw, _) => 1,
                (crate::VirPointerKind::Reference, crate::VirMutability::Const) => 2,
                (crate::VirPointerKind::Reference, crate::VirMutability::Mutable) => 3,
            }] = true;
        }
        assert_eq!(seen, [true; 4]);
    }

    #[test]
    fn stored_exports_move_real_loans_atomically_and_reject_lost_or_duplicate_payloads() {
        use crate::verifier::resource::AbstractLoanAuthority;
        use crate::verifier::{
            AbstractAllocation, AbstractAllocationId, AbstractByteRange, AbstractLoan,
            AbstractPermission, AbstractPointer, AbstractProvenance, GuaranteedAlignment,
            MovePathState, ResourcePayloadKey, ResourceState, TypedResourcePayload,
        };
        let output = crate::analyze(&SourceFile::from_text(
            "stored-shape.nera",
            "fn read(p:&mut u64)->u64{return *p;} fn read_index(p:&mut usize)->usize{return *p;} fn main()->u64{return 0;}",
        ));
        let memory = &output.vir().unwrap().as_unit().memory;
        let (reference, pointee) = memory
            .types
            .iter()
            .find_map(|ty| match ty.kind {
                crate::VirMemoryTypeKind::Pointer {
                    kind: crate::VirPointerKind::Reference,
                    pointee,
                    ..
                } => Some((
                    memory.access(ty.id).unwrap(),
                    memory.access(pointee).unwrap(),
                )),
                _ => None,
            })
            .unwrap();
        let mut before = ResourceState::new();
        let source = AbstractAllocationId::new(10);
        let destination = AbstractAllocationId::new(11);
        for id in [source, destination] {
            before
                .define_allocation(id, AbstractAllocation::new_local(16, 8).unwrap())
                .unwrap();
        }
        let mut payloads = Vec::new();
        let mut loans = std::collections::BTreeSet::new();
        for index in 0..2 {
            let referent = AbstractAllocationId::new(index);
            before
                .define_allocation(referent, AbstractAllocation::new_local(8, 8).unwrap())
                .unwrap();
            let provenance = AbstractProvenance::Known(referent);
            let range = ByteRange::new(0, 8).unwrap();
            let id = crate::VirLoanId::new(index);
            let key = ResourcePayloadKey::new(u64::from(index) * 8, reference);
            let payload = TypedResourcePayload::new(
                AbstractPointer::new(
                    provenance,
                    U64Interval::exact(0),
                    GuaranteedAlignment::new(8).unwrap(),
                )
                .with_memory_access(Some(pointee)),
                AbstractPermission::new(
                    provenance,
                    AbstractByteRange::Exact(range),
                    AccessPermission::Write,
                    FreeCapability::No,
                )
                .with_authority(PermissionAuthority::Loan(id)),
            );
            let mut loan = AbstractLoan::new(
                provenance,
                range,
                crate::VirLoanKind::Mutable,
                crate::VirBorrowRegionId::new(0),
                None,
                LoanActivity::Active,
            );
            loan = loan.with_footprint(Some(crate::verifier::MemoryFootprint {
                provenance,
                access: pointee,
                stride_bytes: 8,
                range: AbstractByteRange::Exact(range),
                envelope: range,
            }));
            loan.add_stored_authority(source, key);
            before.define_loan(id, loan).unwrap();
            before
                .allocation_mut(source)
                .unwrap()
                .set_resource_payload(key, MovePathState::available(payload))
                .unwrap();
            payloads.push((id, key, payload));
            loans.insert(id);
        }
        let mut post = before.clone();
        for (_, key, payload) in &payloads {
            post.allocation_mut(source)
                .unwrap()
                .set_resource_payload(*key, MovePathState::Moved)
                .unwrap();
            post.allocation_mut(destination)
                .unwrap()
                .set_resource_payload(*key, MovePathState::available(*payload))
                .unwrap();
        }
        for mutation in 0..5 {
            let mut changed = post.clone();
            let (id, key, payload) = payloads[1];
            changed
                .allocation_mut(destination)
                .unwrap()
                .set_resource_payload(key, MovePathState::Moved)
                .unwrap();
            let result = crate::VirValueId::new(901);
            let mut pointer = payload.pointer();
            let mut permission = payload.permission();
            match mutation {
                0 => {}
                1 => {
                    changed
                        .allocation_mut(destination)
                        .unwrap()
                        .set_resource_payload(key, MovePathState::available(payload))
                        .unwrap();
                }
                2 => {
                    pointer = pointer.with_memory_access(Some(reference));
                }
                3 => {
                    permission = permission.with_authority(PermissionAuthority::Owner);
                }
                4 => {
                    changed
                        .define_value(result, AbstractValue::Permission(permission))
                        .unwrap();
                }
                _ => unreachable!(),
            }
            let snapshot = changed.clone();
            let accepted = restore_field_exports(
                memory,
                &before,
                &mut changed,
                &loans,
                &Default::default(),
                &std::collections::BTreeMap::from([(id, (result, pointer, permission))]),
            );
            if mutation == 0 {
                assert!(accepted);
                assert_eq!(
                    changed.loan(id).unwrap().authorities(),
                    &std::collections::BTreeSet::from([AbstractLoanAuthority::value(result)])
                );
                assert_eq!(
                    changed.allocation(source).unwrap().resource_payload(key),
                    MovePathState::Moved
                );
            } else {
                assert!(!accepted);
                assert_eq!(changed, snapshot);
            }
        }
        for mutation in 0..3 {
            let mut changed = post.clone();
            let (_, key, payload) = payloads[1];
            changed
                .allocation_mut(destination)
                .unwrap()
                .set_resource_payload(key, MovePathState::Moved)
                .unwrap();
            let (new_key, pointer) = match mutation {
                0 => (
                    key,
                    AbstractPointer::new(
                        payload.pointer().provenance(),
                        U64Interval::exact(1),
                        GuaranteedAlignment::one(),
                    )
                    .with_memory_access(Some(pointee)),
                ),
                1 => (
                    key,
                    payload
                        .pointer()
                        .with_domain(crate::VirPointerDomain::Restricted(
                            AbstractByteRange::Exact(ByteRange::new(0, 4).unwrap()),
                        )),
                ),
                2 => (ResourcePayloadKey::new(12, reference), payload.pointer()),
                _ => unreachable!(),
            };
            changed
                .allocation_mut(destination)
                .unwrap()
                .set_resource_payload(
                    new_key,
                    MovePathState::available(TypedResourcePayload::new(
                        pointer,
                        payload.permission(),
                    )),
                )
                .unwrap();
            let original = changed.clone();
            assert!(!restore_stored_exports(
                memory,
                &before,
                &mut changed,
                &loans,
                &Default::default()
            ));
            assert_eq!(changed, original);
        }
        let mut duplicate_ssa = post.clone();
        duplicate_ssa
            .define_value(
                crate::VirValueId::new(900),
                AbstractValue::Permission(payloads[0].2.permission()),
            )
            .unwrap();
        let original_duplicate = duplicate_ssa.clone();
        assert!(!restore_stored_exports(
            memory,
            &before,
            &mut duplicate_ssa,
            &loans,
            &Default::default()
        ));
        assert_eq!(duplicate_ssa, original_duplicate);

        let mut wrong_type = post.clone();
        let (_, key, payload) = payloads[1];
        wrong_type
            .allocation_mut(destination)
            .unwrap()
            .set_resource_payload(key, MovePathState::Moved)
            .unwrap();
        wrong_type
            .allocation_mut(destination)
            .unwrap()
            .set_resource_payload(
                ResourcePayloadKey::new(key.offset_bytes(), pointee),
                MovePathState::available(payload),
            )
            .unwrap();
        let original_wrong_type = wrong_type.clone();
        assert!(!restore_stored_exports(
            memory,
            &before,
            &mut wrong_type,
            &loans,
            &Default::default()
        ));
        assert_eq!(wrong_type, original_wrong_type);
        // Matching pointer width and permissions cannot change &mut u64 to
        // &mut usize: the actual caller loan still has its original pointee.
        let (other_reference, other_pointee) = memory
            .types
            .iter()
            .find_map(|ty| match ty.kind {
                crate::VirMemoryTypeKind::Pointer {
                    kind: crate::VirPointerKind::Reference,
                    pointee: other,
                    mutability: crate::VirMutability::Mutable,
                } if other != pointee.ty => {
                    Some((memory.access(ty.id).unwrap(), memory.access(other).unwrap()))
                }
                _ => None,
            })
            .unwrap();
        let mut retargeted = post.clone();
        let storage = retargeted.allocation_mut(destination).unwrap();
        storage
            .set_resource_payload(key, MovePathState::Moved)
            .unwrap();
        storage
            .set_resource_payload(
                ResourcePayloadKey::new(key.offset_bytes(), other_reference),
                MovePathState::available(TypedResourcePayload::new(
                    payload.pointer().with_memory_access(Some(other_pointee)),
                    payload.permission(),
                )),
            )
            .unwrap();
        let original_retargeted = retargeted.clone();
        assert!(!restore_stored_exports(
            memory,
            &before,
            &mut retargeted,
            &loans,
            &Default::default()
        ));
        assert_eq!(retargeted, original_retargeted);
        for duplicate in [false, true] {
            let mut broken = post.clone();
            let (_, key, payload) = payloads[1];
            if duplicate {
                broken
                    .allocation_mut(source)
                    .unwrap()
                    .set_resource_payload(key, MovePathState::available(payload))
                    .unwrap();
            } else {
                broken
                    .allocation_mut(destination)
                    .unwrap()
                    .set_resource_payload(key, MovePathState::Moved)
                    .unwrap();
            }
            let original = broken.clone();
            assert!(!restore_stored_exports(
                memory,
                &before,
                &mut broken,
                &loans,
                &Default::default()
            ));
            assert_eq!(broken, original);
        }
        let mut dropped = before.clone();
        for (_, key, _) in &payloads {
            dropped
                .allocation_mut(source)
                .unwrap()
                .set_resource_payload(*key, MovePathState::Moved)
                .unwrap();
        }
        let original = dropped.clone();
        // Missing carriers alone do not authorize a loan end.
        assert!(!restore_stored_exports(
            memory,
            &before,
            &mut dropped,
            &loans,
            &Default::default()
        ));
        assert_eq!(dropped, original);
        let mut child_live = dropped.clone();
        let child = crate::VirLoanId::new(9);
        let first = before.loan(payloads[0].0).unwrap();
        child_live
            .define_loan(
                child,
                AbstractLoan::new(
                    first.provenance(),
                    first.range(),
                    crate::VirLoanKind::Mutable,
                    crate::VirBorrowRegionId::new(0),
                    Some(payloads[0].0),
                    LoanActivity::Active,
                ),
            )
            .unwrap();
        let original_child = child_live.clone();
        assert!(!restore_stored_exports(
            memory,
            &before,
            &mut child_live,
            &loans,
            &loans
        ));
        assert_eq!(child_live, original_child);
        assert!(restore_stored_exports(
            memory,
            &before,
            &mut dropped,
            &loans,
            &loans
        ));
        for (id, _, _) in &payloads {
            assert_eq!(dropped.loan(*id).unwrap().activity(), LoanActivity::Ended);
            assert!(dropped.loan(*id).unwrap().authorities().is_empty());
            assert_eq!(
                dropped
                    .allocation(AbstractAllocationId::new(id.get()))
                    .unwrap()
                    .liveness(),
                crate::verifier::LivenessState::Live
            );
        }
        // Actual reborrow completion resumes a suspended parent only after
        // all of its real children have ended.
        let mut nested_before = before.clone();
        let parent_id = crate::VirLoanId::new(20);
        let first = before.loan(payloads[0].0).unwrap();
        nested_before
            .define_loan(
                parent_id,
                AbstractLoan::new(
                    first.provenance(),
                    first.range(),
                    crate::VirLoanKind::Mutable,
                    crate::VirBorrowRegionId::new(0),
                    None,
                    LoanActivity::Suspended,
                ),
            )
            .unwrap();
        // Parent links are immutable; construct the child with the actual
        // storage authority instead of changing its identity after the fact.
        let mut nested = AbstractLoan::new(
            first.provenance(),
            first.range(),
            crate::VirLoanKind::Mutable,
            crate::VirBorrowRegionId::new(0),
            Some(parent_id),
            LoanActivity::Active,
        );
        nested = nested.with_footprint(first.footprint());
        nested.add_stored_authority(source, payloads[0].1);
        *nested_before.loan_mut(payloads[0].0).unwrap() = nested;
        let mut nested_after = nested_before.clone();
        for (_, key, _) in &payloads {
            nested_after
                .allocation_mut(source)
                .unwrap()
                .set_resource_payload(*key, MovePathState::Moved)
                .unwrap();
        }
        assert!(restore_stored_exports(
            memory,
            &nested_before,
            &mut nested_after,
            &loans,
            &loans
        ));
        assert_eq!(
            nested_after.loan(parent_id).unwrap().activity(),
            LoanActivity::Active
        );
        assert!(restore_stored_exports(
            memory,
            &before,
            &mut post,
            &loans,
            &Default::default()
        ));
        for (id, key, _) in payloads {
            assert_eq!(
                post.loan(id).unwrap().authorities(),
                &std::collections::BTreeSet::from([AbstractLoanAuthority::stored(
                    destination,
                    key
                )])
            );
            assert_eq!(post.loan(id).unwrap().activity(), LoanActivity::Active);
        }
    }

    #[test]
    fn equal_addresses_do_not_substitute_a_different_loan_or_wider_authority() {
        let source =
            "fn main()->u64 { let value=21; let a=&value; let b=&value; return pair(a,b); }
            fn pair(a:&u64,b:&u64)->u64 { return *a+*b; }";
        let output = crate::analyze(&SourceFile::from_text("borrow-substitution.nera", source));
        let unit = output.vir().unwrap().resolve().unwrap();
        let report = crate::verify_program(&unit, Default::default()).unwrap();
        assert!(report.is_memory_checked_core0());
        let caller = &unit.runtime().functions[0];
        let callee = &unit.runtime().functions[1];
        let summary = report.functions()[&callee.id].summary();
        let Knowledge::Known(alternatives) = &summary.normal_returns else {
            panic!();
        };
        let world = &alternatives[0].worlds[0];
        let (block, index, target, arguments) = caller
            .blocks
            .iter()
            .find_map(|b| {
                b.instructions
                    .iter()
                    .enumerate()
                    .find_map(|(i, instruction)| {
                        if let VirInstruction::Call {
                            target, arguments, ..
                        } = &instruction.instruction
                        {
                            Some((b, i, target, arguments))
                        } else {
                            None
                        }
                    })
            })
            .unwrap();
        let analysis = &report.functions()[&caller.id].cfg().blocks()[&block.id];
        let before = if index == 0 {
            analysis.entry_state().unwrap()
        } else {
            &analysis.instruction_states().unwrap()[index - 1]
        };
        let queries = QueryLog::default();
        let cx = CallInstantiation {
            results: &[],
            loss: &std::cell::Cell::new(None),
            before,
            consumed: before,
            arguments,
            memory: unit.runtime().memory,
            site: 99,
            target,
            queries: &queries,
            limits: Default::default(),
        };
        let outcomes = super::super::instantiate(summary, cx).unwrap().unwrap();
        let original = &outcomes[0].values;
        let abi = target.abi.as_ref().unwrap();
        let a = abi.parameters()[0].result_slots()[0] as usize;
        let b = abi.parameters()[1].result_slots()[0] as usize;
        let AbstractValue::Permission(first) = original[a] else {
            panic!();
        };
        let AbstractValue::Permission(second) = original[b] else {
            panic!();
        };
        assert_eq!(first.provenance(), second.provenance());
        assert_eq!(first.range(), second.range());
        assert_ne!(
            first.authority(),
            second.authority(),
            "same bytes, distinct live shared tokens"
        );
        let cx = CallInstantiation {
            results: &[],
            loss: &std::cell::Cell::new(None),
            before,
            consumed: before,
            arguments,
            memory: unit.runtime().memory,
            site: 99,
            target,
            queries: &queries,
            limits: Default::default(),
        };
        assert!(validate_exports(world, &cx, original));
        for changed in [
            first.with_authority(second.authority()),
            first.with_authority(PermissionAuthority::Owner),
            first.with_availability(PermissionAvailability::Consumed),
            crate::AbstractPermission::new(
                first.provenance(),
                crate::AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
                first.access(),
                FreeCapability::No,
            )
            .with_authority(first.authority()),
        ] {
            let mut values = original.clone();
            values[a] = AbstractValue::Permission(changed);
            assert!(!validate_exports(world, &cx, &values));
        }
    }
}
