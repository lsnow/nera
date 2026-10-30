//! Transfer real stored authorities between invocation-local loan tables.
use super::super::{Allocation, RuntimeResourcePayloadKey};
use super::*;

#[cfg(test)]
mod tests;

impl RuntimeLoanShadow {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::vir::interpreter) fn import_stored_parameters(
        &mut self,
        caller: &Self,
        allocations: &mut BTreeMap<u64, Allocation>,
        frame: &BlockFrame,
        function: &crate::VirFunction,
        runtime: crate::RuntimeVirView<'_>,
        limits: RuntimeLoanLimits,
        span: ByteSpan,
    ) -> Result<Vec<RuntimeStoredBorrowReturn>, VirExecutionError> {
        let regions: Vec<_> = runtime
            .borrows
            .regions()
            .iter()
            .filter(|region| {
                region.owner == function.id
                    && matches!(
                        region.origin,
                        crate::VirBorrowRegionOrigin::ParameterField { .. }
                    )
            })
            .collect();
        if regions.is_empty() {
            return Ok(Vec::new());
        }
        let invalid = || error(VirExecutionErrorKind::InvalidRuntimeState, span);
        let abi = &runtime
            .abis
            .function(function.id)
            .ok_or_else(invalid)?
            .signature;
        let accesses = abi
            .parameters()
            .iter()
            .map(|binding| binding.value().access())
            .collect::<Option<Vec<_>>>()
            .ok_or_else(invalid)?;
        let entries = crate::vir::plan_parameter_reference_entries(runtime.memory, &accesses)
            .ok_or_else(invalid)?;
        if entries.len() != regions.len() {
            return Err(invalid());
        }
        let block = function
            .blocks
            .iter()
            .find(|block| block.id == function.entry)
            .ok_or_else(invalid)?;
        let mut next = self.clone();
        let mut patches = Vec::new();
        let mut returns = Vec::new();
        let mut sources = BTreeSet::new();
        for entry in entries {
            let mut matching = regions.iter().filter(|region| {
                region.origin
                    == crate::VirBorrowRegionOrigin::ParameterField {
                        index: entry.parameter,
                        slot: entry.slot,
                    }
            });
            let region = matching.next().ok_or_else(invalid)?;
            if matching.next().is_some() {
                return Err(invalid());
            }
            let pointer_id = block
                .parameters
                .get(entry.pointer_slot as usize)
                .ok_or_else(invalid)?
                .id;
            let storage = pointer_value(frame, pointer_id, span)?;
            let permission_id = block
                .parameters
                .get(entry.permission_slot as usize)
                .ok_or_else(invalid)?
                .id;
            let permission = frame.permission(permission_id, span)?;
            let key = RuntimeResourcePayloadKey {
                offset_bytes: storage
                    .offset_bytes
                    .checked_add(entry.offset_bytes)
                    .ok_or_else(invalid)?,
                access: entry.reference,
            };
            let object = allocations
                .get(&storage.allocation)
                .filter(|object| object.live)
                .ok_or_else(invalid)?;
            let end = key
                .offset_bytes
                .checked_add(
                    runtime
                        .memory
                        .layout(key.access.layout)
                        .ok_or_else(invalid)?
                        .size_bytes,
                )
                .ok_or_else(invalid)?;
            if permission.allocation != storage.allocation
                || permission.start_bytes > key.offset_bytes
                || permission.end_bytes < end
                || object.size_bytes < end
            {
                return Err(invalid());
            }
            let payload = *object.resource_payloads.get(&key).ok_or_else(invalid)?;
            let authority = payload.loan_authority.ok_or_else(invalid)?;
            if !sources.insert((authority.loan, authority.token)) {
                return Err(invalid());
            }
            let kind = if entry.mutability == crate::VirMutability::Const {
                VirLoanKind::Shared
            } else {
                VirLoanKind::Mutable
            };
            caller.validate_import(
                RuntimeBorrowImport {
                    parameter: entry.parameter,
                    authority,
                    pointer: payload.pointer,
                    permission: payload.permission,
                },
                payload.pointer,
                payload.permission,
                kind,
                permission_id,
                span,
            )?;
            if payload.pointer.access != entry.pointee
                || allocations
                    .get(&payload.pointer.allocation)
                    .is_none_or(|a| !a.live || payload.permission.end_bytes > a.size_bytes)
            {
                return Err(invalid());
            }
            let range = VirLoanRange {
                start_bytes: payload.permission.start_bytes,
                end_bytes: payload.permission.end_bytes,
            };
            next.check_source_range(entry.loan, payload.pointer, payload.permission, range, span)?;
            if next.loans.contains_key(&entry.loan) {
                return Err(error(
                    VirExecutionErrorKind::LoanAlreadyDefined { loan: entry.loan },
                    span,
                ));
            }
            if next.active_count() >= limits.active_loans || limits.aliases_per_loan == 0 {
                return Err(error(
                    VirExecutionErrorKind::ActiveLoanLimitExceeded {
                        limit: limits.active_loans,
                    },
                    span,
                ));
            }
            let callee = next.fresh_authority(entry.loan, span)?;
            next.loans.insert(
                entry.loan,
                RuntimeLoan {
                    allocation: payload.pointer.allocation,
                    range,
                    envelope: range,
                    kind,
                    region: region.id,
                    parent: None,
                    pointee: entry.pointee,
                    activity: RuntimeLoanActivity::Active,
                    authorities: BTreeSet::from([callee.token]),
                },
            );
            patches.push((storage.allocation, key, callee));
            returns.push(RuntimeStoredBorrowReturn {
                source: crate::BoundarySource::ParameterField {
                    index: entry.parameter,
                    field: entry.slot,
                },
                caller: authority,
                callee,
                pointer: payload.pointer,
                permission: payload.permission,
                reference: entry.reference,
            });
        }
        for (allocation, key, authority) in patches {
            allocations
                .get_mut(&allocation)
                .unwrap()
                .resource_payloads
                .get_mut(&key)
                .unwrap()
                .loan_authority = Some(authority);
        }
        *self = next;
        Ok(returns)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Keep boundary identities, state, evidence and shared budget explicit at the resource adapter"
    )]
    pub(in crate::vir::interpreter) fn restore_stored_parameters(
        &mut self,
        caller: &mut Self,
        allocations: &mut BTreeMap<u64, Allocation>,
        memory: &crate::VirMemorySchema,
        frame: &mut BlockFrame,
        returns: &[RuntimeStoredBorrowReturn],
        destinations: &BTreeSet<(u64, RuntimeResourcePayloadKey)>,
        value_exits: &[RuntimeStoredValueExit],
        limits: RuntimeLoanLimits,
        span: ByteSpan,
    ) -> Result<Vec<RuntimeBorrowReturn>, VirExecutionError> {
        if returns.is_empty() {
            return Ok(Vec::new());
        }
        let invalid = || error(VirExecutionErrorKind::InvalidRuntimeState, span);
        let mut next = self.clone();
        let mut restored = caller.clone();
        let mut patches = Vec::new();
        let mut exported = Vec::new();
        let mut exported_ids = BTreeSet::new();
        let mut result_ids = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut sources = BTreeSet::new();
        for record in returns {
            let binding = record.binding();
            if !matches!(binding.source, crate::BoundarySource::ParameterField { .. })
                || !sources.insert(binding.source)
            {
                return Err(invalid());
            }
            if !seen.insert(record.callee.loan) {
                return Err(invalid());
            }
            let loan = next.loan(record.callee.loan, span)?;
            restored.validate_import(
                RuntimeBorrowImport {
                    parameter: 0,
                    authority: binding.authority,
                    pointer: binding.view.0,
                    permission: binding.view.1,
                },
                record.pointer,
                record.permission,
                loan.kind,
                VirValueId::new(u32::MAX),
                span,
            )?;
            let source = restored.loan(record.caller.loan, span)?;
            if source.activity != RuntimeLoanActivity::Active
                || !source.authorities.contains(&record.caller.token)
                || next.has_active_child(record.callee.loan)
            {
                return Err(invalid());
            }
            let mut stored = Vec::new();
            let mut observed = BTreeSet::new();
            for (id, allocation) in allocations.iter() {
                for (key, payload) in &allocation.resource_payloads {
                    let Some(authority) = payload.loan_authority else {
                        continue;
                    };
                    if authority.loan != record.callee.loan
                        || authority.token.invocation != next.invocation
                    {
                        continue;
                    }
                    if !observed.insert(authority.token)
                        || !destinations.contains(&(*id, *key))
                        || !allocation.live
                        || !memory.resolves_access(key.access)
                        || !matches!(memory.kind(key.access.ty), Some(crate::VirMemoryTypeKind::Pointer {
                            kind: crate::VirPointerKind::Reference, pointee, mutability,
                        }) if memory.access(*pointee) == Some(record.pointer.access)
                            && (*mutability == crate::VirMutability::Const) == (loan.kind == VirLoanKind::Shared))
                        || memory.layout(key.access.layout).is_none_or(|layout| {
                            allocation.alignment < layout.alignment
                                || key.offset_bytes % layout.alignment != 0
                                || key
                                    .offset_bytes
                                    .checked_add(layout.size_bytes)
                                    .is_none_or(|end| end > allocation.size_bytes)
                        })
                        || !loan.authorities.contains(&authority.token)
                        || payload.permission != record.permission
                        || payload.pointer.allocation != record.pointer.allocation
                        || payload.pointer.offset_bytes != record.pointer.offset_bytes
                        || payload.pointer.access != record.pointer.access
                        || payload.pointer.domain != record.pointer.domain
                        || payload.pointer.paths != record.pointer.paths
                        || payload.pointer.view_range != record.pointer.view_range
                    {
                        return Err(invalid());
                    }
                    stored.push((*id, *key));
                }
            }
            let ssa = frame
                .values
                .keys()
                .copied()
                .filter(|id| {
                    frame
                        .loan_authority(*id)
                        .is_some_and(|a| a.loan == record.callee.loan)
                })
                .collect::<Vec<_>>();
            let mut returned_values = Vec::new();
            for permission in ssa {
                let mut matches = value_exits
                    .iter()
                    .filter(|exit| exit.source == record.source && exit.permission == permission);
                let exit = matches.next().ok_or_else(invalid)?;
                if matches.next().is_some()
                    || loan.activity != RuntimeLoanActivity::Active
                    || !exported_ids.insert(exit.permission)
                    || !result_ids.insert(exit.caller_result)
                {
                    return Err(invalid());
                }
                let authority =
                    next.require_authority(frame, record.callee.loan, permission, span)?;
                let pointer = pointer_value(frame, exit.pointer, span)?;
                if !observed.insert(authority.token)
                    || frame.permission(permission, span)? != record.permission
                    || pointer.allocation != record.pointer.allocation
                    || pointer.offset_bytes != record.pointer.offset_bytes
                    || pointer.access != record.pointer.access
                    || pointer.domain != record.pointer.domain
                    || pointer.paths != record.pointer.paths
                    || pointer.view_range != record.pointer.view_range
                {
                    return Err(invalid());
                }
                returned_values.push(exit);
            }
            if observed != loan.authorities
                || (observed.len() > 1 && loan.kind != VirLoanKind::Shared)
            {
                return Err(invalid());
            }
            if loan.activity == RuntimeLoanActivity::Ended && observed.is_empty() {
                restored.end_stored(binding.authority, binding.view.0, record.reference, span)?;
                continue;
            }
            if loan.activity != RuntimeLoanActivity::Active
                || observed.is_empty()
                || loan.allocation != record.pointer.allocation
                || loan.pointee != record.pointer.access
                || loan.range
                    != (VirLoanRange {
                        start_bytes: record.permission.start_bytes,
                        end_bytes: record.permission.end_bytes,
                    })
                || allocations.get(&loan.allocation).is_none_or(|a| !a.live)
            {
                return Err(invalid());
            }
            // The imported caller token supplies the first carrier. Additional
            // actual shared carriers get fresh aliases of that same authority,
            // only in the transaction's private caller table.
            let mut first = true;
            let mut next_authority = || {
                if first {
                    first = false;
                    Ok(binding.authority)
                } else {
                    restored.alias_stored(
                        binding.authority,
                        binding.view.0,
                        record.reference,
                        limits,
                        span,
                    )
                }
            };
            for (allocation, key) in stored {
                patches.push((allocation, key, next_authority()?));
            }
            for value in returned_values {
                exported.push(RuntimeBorrowReturn {
                    value: value.caller_result,
                    authority: next_authority()?,
                    permission: record.permission,
                    callee_loan: None,
                    projected_pointee: None,
                });
            }
            let loan = next.loans.get_mut(&record.callee.loan).unwrap();
            loan.activity = RuntimeLoanActivity::Ended;
            loan.authorities.clear();
        }
        for (allocation, key, authority) in patches {
            allocations
                .get_mut(&allocation)
                .unwrap()
                .resource_payloads
                .get_mut(&key)
                .unwrap()
                .loan_authority = Some(authority);
        }
        for id in exported_ids {
            frame.loan_authorities.remove(&id);
        }
        *self = next;
        *caller = restored;
        Ok(exported)
    }
}
