//! Signature-derived loan authority and borrowed value guarantees.
//! Predicate parameters import only their declared representation; ordinary
//! references still require complete referents on entry and export.

pub(super) mod stored;

use super::relation::difference::{DifferenceLimits, DifferencePremise, word};
use super::relation::{RelationComparison, RelationTerm};
use super::resource::*;
use super::transfer::{ObligationStatus, ResourceObligation, ResourceObligationKind};
use crate::vir::*;

pub(super) fn install_entry(
    state: &mut ResourceState,
    function: &VirFunction,
    abi: &VirAbiSignature,
    borrows: &VirBorrowEnvironment,
    memory: &VirMemorySchema,
    contract: &super::contract::InstantiatedContract,
) -> Option<()> {
    // Aggregate field loans are installed with their typed payloads by CFG
    // entry construction, after direct parameter bindings are established.
    let entry = function
        .blocks
        .iter()
        .find(|block| block.id == function.entry)?;
    for region in borrows
        .regions()
        .iter()
        .filter(|region| region.owner == function.id)
    {
        let VirBorrowRegionOrigin::Parameter { index } = region.origin else {
            continue;
        };
        let binding = abi.parameters().get(index as usize)?;
        let kind = if binding.interface().transfer == VirInterfaceTransfer::BorrowShared {
            VirLoanKind::Shared
        } else {
            VirLoanKind::Mutable
        };
        let (pointee, size) = match binding.value() {
            VirAbiValue::Pointer { pointee, .. } => {
                (*pointee, memory.layout(pointee.layout)?.size_bytes)
            }
            VirAbiValue::Slice { element, .. } => {
                let stride = memory.object_shape(*element).ok()?.size_bytes();
                if stride == 0 {
                    return None;
                }
                (*element, (u64::MAX / stride) * stride)
            }
            _ => return None,
        };
        let pointer = entry
            .parameters
            .get(*binding.parameter_slots().first()? as usize)?
            .id;
        let permission = entry
            .parameters
            .get(*binding.parameter_slots().last()? as usize)?
            .id;
        let allocation_id =
            AbstractAllocationId::abi_entry_payload(function.id.get(), index, u32::MAX);
        let provenance = AbstractProvenance::Known(allocation_id);
        let alignment = memory.layout(pointee.layout)?.alignment;
        let mut allocation = AbstractAllocation::new_local(size.max(1), alignment).ok()?;
        let range = ByteRange::new(0, size).ok()?;
        let slice = matches!(binding.value(), VirAbiValue::Slice { .. });
        // A predicate parameter exposes its declared representation, not an
        // additional implicit guarantee that every byte of T is initialized.
        // The checked predicate entry import below installs that minimum.
        let predicate_value = !slice
            && binding.interface().transfer == VirInterfaceTransfer::BorrowMutable
            && contract.predicates.iter().any(|interface| {
                !interface.metadata.ensures
                    && interface.metadata.bindings.iter().any(|(p, q)| {
                        binding.parameter_slots().first() == Some(p)
                            && binding.parameter_slots().last() == Some(q)
                    })
            });
        if predicate_value && size != 0 {
            // Undeclared bytes are unknown, not definitely uninitialized.
            // Otherwise the summary would reject a caller with extra contents
            // and contradict a symbolic initialized-prefix guarantee.
            allocation.forget_initialization(range).ok()?;
        }
        if size != 0 {
            let shape = memory.object_shape(pointee).ok()?;
            if ((slice || crate::vir::predicate_resource_fields(memory, pointee).is_none())
                && shape
                    .resource_leaves()
                    .iter()
                    .any(|leaf| leaf.kind() != VirPointerKind::Raw))
                || !shape.variants().is_empty()
            {
                return None;
            }
            if slice {
                // Signature-owned virtual extent, not a concrete allocation.
                // Every admitted element is complete; actual access remains
                // bounded by the symbolic permission tied to the length SSA.
                allocation.mark_initialized(range).ok()?;
                allocation.mark_valid(range).ok()?;
            } else if !predicate_value {
                for bytes in shape.value_bytes() {
                    let bytes = ByteRange::new(bytes.start_bytes(), bytes.end_bytes()).ok()?;
                    allocation.mark_initialized(bytes).ok()?;
                    allocation.mark_valid(bytes).ok()?;
                }
            }
        }
        state.define_allocation(allocation_id, allocation).ok()?;
        let loan_id = interface_loan_id(index);
        let actual_range = if slice {
            let length = entry
                .parameters
                .get(*binding.parameter_slots().get(1)? as usize)?
                .id;
            let stride = memory.object_shape(pointee).ok()?.size_bytes();
            let interval = U64Interval::new(0, u64::MAX / stride).ok()?;
            let interval = match state.value(length)? {
                AbstractValue::U64(current) => current.intersection(interval)?,
                _ => return None,
            };
            state.narrow_word_interval(length, interval);
            AbstractByteRange::from_bounds(
                SymbolicRangeBound::constant(0),
                SymbolicRangeBound::new(
                    AffineExpression::identity(length).checked_scale(stride)?,
                    U64Interval::new(
                        interval.lower().checked_mul(stride)?,
                        interval.upper().checked_mul(stride)?,
                    )
                    .ok()?,
                ),
            )
        } else {
            AbstractByteRange::Exact(range)
        };
        let footprint = MemoryFootprint {
            provenance,
            access: pointee,
            stride_bytes: memory.object_shape(pointee).ok()?.size_bytes(),
            range: actual_range,
            envelope: range,
        };
        let pointer_fact = AbstractPointer::new(
            provenance,
            U64Interval::exact(0),
            GuaranteedAlignment::new(alignment).ok()?,
        )
        .with_memory_access(Some(pointee))
        .with_paths(crate::VirPointerPaths::parameter(
            pointee,
            function.id,
            index,
        ))
        .with_domain(crate::VirPointerDomain::Restricted(actual_range))
        .with_slice_footprint(
            matches!(binding.value(), VirAbiValue::Slice { .. }).then_some(footprint),
        );
        let permission_fact = AbstractPermission::new(
            provenance,
            actual_range,
            if kind == VirLoanKind::Shared {
                AccessPermission::Read
            } else {
                AccessPermission::Write
            },
            FreeCapability::No,
        )
        .with_authority(PermissionAuthority::Loan(loan_id));
        *state.value_mut(pointer)? = AbstractValue::Pointer(pointer_fact);
        *state.value_mut(permission)? = AbstractValue::Permission(permission_fact);
        state
            .define_loan(
                loan_id,
                AbstractLoan::new(
                    provenance,
                    range,
                    kind,
                    region.id,
                    None,
                    LoanActivity::Active,
                )
                .with_footprint(Some(footprint))
                .with_authority(permission),
            )
            .ok()?;
    }
    install_projection_preconditions(state, entry, abi)?;
    Some(())
}

/// Projected slice results are verified modularly: the body is checked under
/// the range relation published by its ABI, and every call independently
/// discharges the same relation for its actual arguments.
fn install_projection_preconditions(
    state: &mut ResourceState,
    entry: &VirBasicBlock,
    abi: &VirAbiSignature,
) -> Option<()> {
    let Some(relation) = abi.borrow_result() else {
        return Some(());
    };
    let Some((start, end)) = relation.projection.slice_bounds() else {
        return Some(());
    };
    let source = abi.parameters().get(relation.parameter as usize)?;
    let length = if let Some(length) = relation.projection.array_length() {
        RelationTerm::Constant(length)
    } else {
        let length_slot = *source.parameter_slots().get(1)? as usize;
        word(entry.parameters.get(length_slot)?.id)
    };
    let term = |bound| match bound {
        crate::BorrowSliceBound::ReturnedLength | crate::BorrowSliceBound::ReturnedOffset => None,
        crate::BorrowSliceBound::Constant(value) => Some(RelationTerm::Constant(value)),
        crate::BorrowSliceBound::Parameter(parameter) => {
            let binding = abi.parameters().get(parameter as usize)?;
            let slot = *binding.parameter_slots().first()? as usize;
            Some(word(entry.parameters.get(slot)?.id))
        }
        crate::BorrowSliceBound::SourceLength => Some(length),
    };
    state.learn_relations(
        &[
            DifferencePremise::Compare {
                comparison: RelationComparison::LessOrEqual,
                left: term(start)?,
                right: term(end)?,
            },
            DifferencePremise::Compare {
                comparison: RelationComparison::LessOrEqual,
                left: term(end)?,
                right: length,
            },
        ],
        DifferenceLimits::default(),
    );
    Some(())
}

pub(super) fn exported_authority(
    state: &ResourceState,
    loan_id: VirLoanId,
    values: &[VirValueId],
    abi: &VirAbiSignature,
) -> bool {
    let Some(loan) = state.loan(loan_id) else {
        return false;
    };
    let mut exports = std::collections::BTreeSet::new();
    if let Some(parent) = loan.parent() {
        if loan.activity() != LoanActivity::Active
            || !abi
                .borrow_result_parameters()
                .iter()
                .any(|index| interface_loan_id(*index as u32) == parent)
        {
            return false;
        }
        let Some(slot) = abi.results()[0].result_slots().last().copied() else {
            return false;
        };
        let Some(value) = values.get(slot as usize).copied() else {
            return false;
        };
        if matches!(state.value(value), Some(AbstractValue::Permission(permission)) if permission.authority() == PermissionAuthority::Loan(loan_id) && permission.availability() == PermissionAvailability::Available)
        {
            exports.insert(AbstractLoanAuthority::value(value));
        }
        return !exports.is_empty() && &exports == loan.authorities();
    }
    if !matches!(
        loan.activity(),
        LoanActivity::Active | LoanActivity::Suspended
    ) {
        return false;
    }
    for (index, binding) in abi.parameters().iter().enumerate() {
        if !binding.interface().transfer.is_borrow() || interface_loan_id(index as u32) != loan_id {
            continue;
        }
        for slot in binding.result_slots().iter().copied() {
            let Some(value) = values.get(slot as usize).copied() else {
                return false;
            };
            if !matches!(state.value(value), Some(AbstractValue::Permission(permission)) if permission.authority() == PermissionAuthority::Loan(loan_id) && permission.availability() == PermissionAvailability::Available)
            {
                return false;
            }
            let Some(AbstractValue::Permission(permission)) = state.value(value) else {
                return false;
            };
            if permission.provenance() != loan.provenance()
                || permission.range() != loan.actual_range()
                || permission.free_capability() != FreeCapability::No
                || permission.access()
                    != if loan.kind() == VirLoanKind::Mutable {
                        AccessPermission::Write
                    } else {
                        AccessPermission::Read
                    }
            {
                return false;
            }
            exports.insert(AbstractLoanAuthority::value(value));
        }
        if abi.borrow_result_parameters().contains(&index) {
            let Some(slot) = abi.results()[0].result_slots().last().copied() else {
                return false;
            };
            let Some(value) = values.get(slot as usize).copied() else {
                return false;
            };
            if matches!(state.value(value), Some(AbstractValue::Permission(permission)) if permission.authority() == PermissionAuthority::Loan(loan_id) && permission.availability() == PermissionAvailability::Available)
            {
                exports.insert(AbstractLoanAuthority::value(value));
            }
        }
    }
    let selected_child = state.loans().iter().any(|(child_id, child)| {
        child.parent() == Some(loan_id)
            && child.activity() == LoanActivity::Active
            && exported_authority(state, *child_id, values, abi)
    });
    !exports.is_empty()
        && &exports == loan.authorities()
        && (loan.activity() == LoanActivity::Active || selected_child)
}

/// Value restoration is independent of authority export. A live loan is not
/// evidence that the callee restored an initialized, valid referent.
pub(super) fn export_value_obligations(
    state: &ResourceState,
    loan_id: VirLoanId,
    abi: &VirAbiSignature,
    memory: &VirMemorySchema,
    span: crate::ByteSpan,
) -> Vec<ResourceObligation> {
    let mut obligations = Vec::new();
    for (index, binding) in abi.parameters().iter().enumerate() {
        if interface_loan_id(index as u32) != loan_id || !binding.interface().transfer.is_borrow() {
            continue;
        }
        if let VirAbiValue::Slice { element, .. } = binding.value() {
            let loan = state.loan(loan_id);
            let id = loan.and_then(|loan| match loan.provenance() {
                AbstractProvenance::Known(id) => Some(id),
                _ => None,
            });
            let allocation = id.and_then(|id| state.allocation(id));
            let range = loan.map(AbstractLoan::range);
            let initialized =
                allocation
                    .zip(range)
                    .map_or(ObligationStatus::Unknown, |(allocation, range)| {
                        if allocation.liveness() != LivenessState::Live {
                            return ObligationStatus::Unknown;
                        }
                        match allocation.initialization().classify(range) {
                            InitializationClass::Initialized => ObligationStatus::Proven,
                            InitializationClass::Uninitialized => ObligationStatus::Refuted,
                            InitializationClass::MaybeInitialized => ObligationStatus::Unknown,
                        }
                    });
            let valid = allocation.zip(range).is_some_and(|(allocation, range)| {
                allocation.liveness() == LivenessState::Live
                    && allocation.valid_value_bytes().contains(range)
            });
            obligations.push(ResourceObligation::new(
                ResourceObligationKind::ObjectValueBytesInitialized {
                    allocation: id,
                    access: range,
                    object: *element,
                },
                initialized,
                span,
            ));
            obligations.push(ResourceObligation::new(
                ResourceObligationKind::ObjectRepresentationValid {
                    allocation: id,
                    access: range,
                    object: *element,
                },
                if valid {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
                span,
            ));
            continue;
        }
        let VirAbiValue::Pointer { pointee, .. } = binding.value() else {
            continue;
        };
        let id = state
            .loan(loan_id)
            .and_then(|loan| match loan.provenance() {
                AbstractProvenance::Known(id) => Some(id),
                AbstractProvenance::Unknown => None,
            });
        let allocation = id.and_then(|id| state.allocation(id));
        let shape = memory.object_shape(*pointee).ok();
        if let Some(fields) = crate::vir::predicate_resource_fields(memory, *pointee) {
            for field in fields {
                let valid = id.is_some_and(|id| state.bounded_field_payload(id, &field).is_ok());
                obligations.push(ResourceObligation::new(
                    ResourceObligationKind::AggregateAbiPayloadValid {
                        allocation: id,
                        offset_bytes: Some(field.offset),
                        access: field.access,
                    },
                    if valid {
                        ObligationStatus::Proven
                    } else {
                        ObligationStatus::Unknown
                    },
                    span,
                ));
            }
        }
        let range = shape
            .as_ref()
            .and_then(|shape| ByteRange::new(0, shape.size_bytes()).ok());
        let initialized = shape.as_ref().zip(allocation).map_or(
            ObligationStatus::Unknown,
            |(shape, allocation)| {
                if allocation.liveness() != LivenessState::Live {
                    return ObligationStatus::Unknown;
                }
                let mut status = ObligationStatus::Proven;
                for bytes in shape.value_bytes() {
                    let Ok(range) = ByteRange::new(bytes.start_bytes(), bytes.end_bytes()) else {
                        return ObligationStatus::Unknown;
                    };
                    match allocation.initialization().classify(range) {
                        InitializationClass::Initialized => {}
                        InitializationClass::Uninitialized => return ObligationStatus::Refuted,
                        InitializationClass::MaybeInitialized => status = ObligationStatus::Unknown,
                    }
                }
                status
            },
        );
        let valid = shape
            .as_ref()
            .zip(allocation)
            .is_some_and(|(shape, allocation)| {
                allocation.liveness() == LivenessState::Live
                    && shape.value_bytes().iter().all(|bytes| {
                        ByteRange::new(bytes.start_bytes(), bytes.end_bytes())
                            .is_ok_and(|range| allocation.valid_value_bytes().contains(range))
                    })
            });
        obligations.push(ResourceObligation::new(
            ResourceObligationKind::ObjectValueBytesInitialized {
                allocation: id,
                access: range,
                object: *pointee,
            },
            initialized,
            span,
        ));
        obligations.push(ResourceObligation::new(
            ResourceObligationKind::ObjectRepresentationValid {
                allocation: id,
                access: range,
                object: *pointee,
            },
            if valid {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
            span,
        ));
    }
    obligations
}

/// The independently validated SSA view pairs the returned pointer and length.
/// Resource transfer still has to establish its actual footprint and authority.
pub(super) fn returned_slice_obligation(
    state: &ResourceState,
    values: &[VirValueId],
    abi: &VirAbiSignature,
    span: crate::ByteSpan,
) -> Option<ResourceObligation> {
    let relation = abi.borrow_result()?;
    if !matches!(
        relation.projection,
        crate::BorrowProjection::ArraySlice {
            end: crate::BorrowSliceBound::ReturnedLength,
            ..
        }
    ) {
        return None;
    }
    let facts = values
        .iter()
        .map(|id| state.value(*id).copied())
        .collect::<Option<Vec<_>>>();
    let valid =
        facts.is_some_and(|facts| normalize_returned_slice(state, values, &facts, abi).is_some());
    Some(ResourceObligation::new(
        ResourceObligationKind::BorrowProjectionRangeWithinSource {
            source_parameter: relation.parameter,
        },
        if valid {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Unknown
        },
        span,
    ))
}

/// Normalize only a checked return view. SSA validation establishes len=end-start;
/// this adapter conserves the observed start/end intervals and original authority.
/// It neither modifies the executable state nor imports a declared range as fact.
pub(super) fn normalize_returned_slice(
    state: &ResourceState,
    ids: &[VirValueId],
    facts: &[AbstractValue],
    abi: &VirAbiSignature,
) -> Option<Vec<AbstractValue>> {
    let Some(relation) = abi.borrow_result() else {
        return Some(facts.to_vec());
    };
    let crate::BorrowProjection::ArraySlice {
        offset_bytes,
        length,
        stride_bytes,
        start: start_coordinate,
        end: crate::BorrowSliceBound::ReturnedLength,
    } = relation.projection
    else {
        return Some(facts.to_vec());
    };
    let slots = abi.results().get(relation.result as usize)?.result_slots();
    let pointer_slot = *slots.first()? as usize;
    let length_slot = *slots.get(1)? as usize;
    let permission_slot = *slots.get(2)? as usize;
    let AbstractValue::Pointer(pointer) = *facts.get(pointer_slot)? else {
        return None;
    };
    let AbstractValue::U64(actual_length) = *facts.get(length_slot)? else {
        return None;
    };
    let AbstractValue::Permission(permission) = *facts.get(permission_slot)? else {
        return None;
    };
    let footprint = pointer.slice_footprint()?;
    let (start, end) = footprint.range.bounds()?;
    let stride = u64::from(stride_bytes);
    let extent = ByteRange::from_start_and_length(
        u64::from(offset_bytes),
        u64::from(length).checked_mul(stride)?,
    )
    .ok()?;
    let pointer_expression = pointer
        .offset_bytes()
        .exact_value()
        .map(AffineExpression::constant)
        .or(pointer.offset_expression())?;
    if footprint.provenance != pointer.provenance()
        || permission.provenance() != pointer.provenance()
        || footprint.range != permission.range()
        || !extent.contains(footprint.envelope)
        || actual_length.upper() > u64::from(length)
        || start.interval() != pointer.offset_bytes()
        || start.expression() != pointer_expression
    {
        return None;
    }
    let length_expression = actual_length
        .exact_value()
        .map(AffineExpression::constant)
        .or_else(|| state.word_expression(*ids.get(length_slot)?))?;
    // This fresh offset is scoped to the actual returned pointer, not to a
    // later load of the heap cursor. The independent SSA check certifies the
    // paired length; the checks above retain the actual storage/permission.
    let start = if start_coordinate == crate::BorrowSliceBound::ReturnedOffset {
        SymbolicRangeBound::new(
            AffineExpression::identity(*ids.get(pointer_slot)?),
            start.interval(),
        )
    } else {
        start
    };
    let normalized_end = start
        .expression()
        .checked_add(length_expression.checked_scale(stride)?)?;
    let range = AbstractByteRange::from_bounds(
        start,
        SymbolicRangeBound::new(normalized_end, end.interval()),
    );
    let mut values = facts.to_vec();
    values[pointer_slot] = AbstractValue::Pointer(
        pointer
            .with_offset_expression(Some(start.expression()))
            .with_slice_footprint(Some(MemoryFootprint { range, ..footprint }))
            .with_domain(match pointer.domain() {
                crate::VirPointerDomain::Restricted(old) if old == footprint.range => {
                    crate::VirPointerDomain::Restricted(range)
                }
                domain => domain,
            }),
    );
    values[permission_slot] = AbstractValue::Permission(
        AbstractPermission::new(
            permission.provenance(),
            range,
            permission.access(),
            permission.free_capability(),
        )
        .with_authority(permission.authority())
        .with_availability(permission.availability()),
    );
    Some(values)
}
