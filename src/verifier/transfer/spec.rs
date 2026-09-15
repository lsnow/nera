//! Read-only Spec adapter over the existing access/initialization/loan rules.
//! Never applies a runtime instruction, defines an SSA value, or commits state.
use super::*;
use crate::verifier::vc::VcQueryBudget;
mod symbolic;
pub(in crate::verifier) use symbolic::{SymbolicSpecMemoryQuery, query_symbolic_spec_memory};
#[cfg(test)]
mod tests;

#[derive(Clone, Copy)]
pub(in crate::verifier) struct SpecMemoryQuery {
    pub pointer: VirValueId,
    /// None observes initialization without claiming authority.
    pub authority: Option<VirValueId>,
    pub start: u64,
    pub end: u64,
    pub layout: VirMemoryAccess,
    pub access: AccessPermission,
    pub initialized: bool,
    pub valid: bool,
}

/// Contents only, never evidence that reading is permitted. The caller must
/// first prove query_spec_memory for this exact selected range and authority.
pub(in crate::verifier) fn spec_scalar_contents(
    state: &ResourceState,
    memory: &VirMemorySchema,
    query: SpecMemoryQuery,
    budget: &mut VcQueryBudget,
) -> Option<Vec<AbstractValue>> {
    let pointer = pointer_fact(state, query.pointer).ok()?;
    let AbstractProvenance::Known(id) = pointer.provenance() else {
        return None;
    };
    let allocation = state.allocation(id)?;
    let width = memory.object_shape(query.layout).ok()?.size_bytes();
    let length = query.end.checked_sub(query.start)?;
    if width == 0 || length == 0 || length % width != 0 || length / width > 4096 {
        return None;
    }
    let start = pointer
        .offset_bytes()
        .exact_value()?
        .checked_add(query.start)?;
    let mut values = Vec::new();
    for i in 0..length / width {
        budget.charge(1)?;
        let range =
            ByteRange::from_start_and_length(start.checked_add(i.checked_mul(width)?)?, width)
                .ok()?;
        values.push(allocation.scalar_content(range, query.layout)?);
    }
    Some(values)
}

/// A successfully checked claim's selected bytes, never its authority's entire
/// envelope. Used only in the per-Prove resource-use ledger.
#[derive(Clone, Copy, Debug)]
pub(in crate::verifier) struct SpecFootprint {
    pub provenance: AbstractProvenance,
    pub range: AbstractByteRange,
    pub access: AccessPermission,
}

pub(in crate::verifier) fn spec_footprint(
    state: &ResourceState,
    query: SpecMemoryQuery,
) -> Option<SpecFootprint> {
    query.authority?;
    spec_range_footprint(state, query)
}

pub(in crate::verifier) fn spec_range_footprint(
    state: &ResourceState,
    query: SpecMemoryQuery,
) -> Option<SpecFootprint> {
    let pointer = pointer_fact(state, query.pointer).ok()?;
    let length = query.end.checked_sub(query.start)?;
    let low = pointer.offset_bytes().lower().checked_add(query.start)?;
    let high = pointer.offset_bytes().upper().checked_add(query.start)?;
    high.checked_add(length)?;
    let selected = shifted_pointer(pointer, query.start, low, high);
    Some(SpecFootprint {
        provenance: selected.provenance(),
        range: crate::verifier::relation::range::access_range(selected, length),
        access: query.access,
    })
}

/// Geometry of two independently well-defined ranges. Does not read contents
/// or consume an access occurrence, even when both ranges use the same owner.
pub(in crate::verifier) fn query_spec_disjoint(
    state: &ResourceState,
    memory: &VirMemorySchema,
    left: SpecMemoryQuery,
    right: SpecMemoryQuery,
    config: crate::CfgAnalysisConfig,
    budget: &mut VcQueryBudget,
) -> Option<ObligationStatus> {
    for query in [left, right] {
        let status = query_spec_memory(state, memory, query, config, budget)?;
        if !status.is_proven() {
            return Some(status);
        }
    }
    let left = spec_range_footprint(state, left)?;
    let right = spec_range_footprint(state, right)?;
    // Borrow entry identities name symbolic views, not necessarily distinct
    // backing allocations. Until cross-input alias premises are represented,
    // their different names cannot establish physical disjointness.
    if let (
        AbstractProvenance::Known(a @ AbstractAllocationId::AbiEntryPayload { leaf: u32::MAX, .. }),
        AbstractProvenance::Known(b @ AbstractAllocationId::AbiEntryPayload { leaf: u32::MAX, .. }),
    ) = (left.provenance, right.provenance)
        && a != b
    {
        return Some(ObligationStatus::Unknown);
    }
    budget.begin_query()?;
    Some(budget.relations.disjoint(
        state,
        left.provenance,
        left.range,
        right.provenance,
        right.range,
        budget.relation_limits,
    ))
}

pub(in crate::verifier) fn spec_alive(
    state: &ResourceState,
    pointer: VirValueId,
) -> ObligationStatus {
    let Some(AbstractValue::Pointer(pointer)) = state.value(pointer) else {
        return ObligationStatus::Unknown;
    };
    let AbstractProvenance::Known(id) = pointer.provenance() else {
        return ObligationStatus::Unknown;
    };
    state
        .allocation(id)
        .map_or(ObligationStatus::Unknown, |a| liveness_status(a.liveness()))
}

pub(in crate::verifier) fn spec_same_allocation(
    state: &ResourceState,
    left: VirValueId,
    right: VirValueId,
) -> ObligationStatus {
    let (Some(AbstractValue::Pointer(a)), Some(AbstractValue::Pointer(b))) =
        (state.value(left), state.value(right))
    else {
        return ObligationStatus::Unknown;
    };
    let (AbstractProvenance::Known(a), AbstractProvenance::Known(b)) =
        (a.provenance(), b.provenance())
    else {
        return ObligationStatus::Unknown;
    };
    // Retired instances are renamed/forgotten by ResourceState; never compare
    // concrete addresses or infer identity from source names.
    if state.allocation(a).is_none() || state.allocation(b).is_none() {
        return ObligationStatus::Unknown;
    }
    if a == b {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Refuted
    }
}

pub(in crate::verifier) fn query_spec_memory(
    state: &ResourceState,
    memory: &VirMemorySchema,
    query: SpecMemoryQuery,
    config: crate::CfgAnalysisConfig,
    budget: &mut VcQueryBudget,
) -> Option<ObligationStatus> {
    let pointer = pointer_fact(state, query.pointer).ok()?;
    query_spec_memory_pointer(state, memory, query, pointer, config, budget)
}

/// Typed ABI/field/index resolution must establish the selected access and
/// offset before calling this adapter. It retains provenance, domain and loan
/// identity; all ordinary bounds/alignment/authority checks still run.
pub(in crate::verifier) fn query_contract_memory(
    state: &ResourceState,
    memory: &VirMemorySchema,
    query: SpecMemoryQuery,
    source: VirMemoryAccess,
    budget: &mut VcQueryBudget,
) -> Option<ObligationStatus> {
    let pointer = pointer_fact(state, query.pointer).ok()?;
    if pointer.memory_access() != Some(source) {
        return None;
    }
    query_spec_memory_pointer(
        state,
        memory,
        query,
        pointer.with_memory_access(Some(query.layout)),
        crate::CfgAnalysisConfig {
            relation_limits: budget.relation_limits,
            ..Default::default()
        },
        budget,
    )
}

fn query_spec_memory_pointer(
    state: &ResourceState,
    memory: &VirMemorySchema,
    query: SpecMemoryQuery,
    pointer: AbstractPointer,
    config: crate::CfgAnalysisConfig,
    budget: &mut VcQueryBudget,
) -> Option<ObligationStatus> {
    budget.begin_query()?;
    if !state.path_condition().is_reachable() {
        return None;
    }
    let shape = memory.object_shape(query.layout).ok()?;
    // First points-to profile: repeated Bool/U64 scalar cells. No padding,
    // enum payload, resource leaf, arbitrary ghost load, or unbounded unfolding.
    if !matches!(
        memory.kind(query.layout.ty),
        Some(
            VirMemoryTypeKind::Bool
                | VirMemoryTypeKind::Integer(
                    crate::VirIntegerType::U64 | crate::VirIntegerType::Usize
                )
        )
    ) {
        return None;
    }
    let stride = shape.size_bytes();
    let Some(length) = query.end.checked_sub(query.start) else {
        return Some(ObligationStatus::Refuted);
    };
    if stride == 0 || length % stride != 0 {
        return None;
    }
    let count = usize::try_from(length / stride).ok()?;
    budget.charge(count.max(1).checked_mul(16)?)?;
    // Keep host work finite even if a custom VC budget is exceptionally large.
    if count > 4096 {
        return None;
    }
    let mut builder = TransferBuilder::new(state.clone(), ByteSpan::new(0, 0)?, memory, None, None);
    builder.relation_limits = config.relation_limits;
    builder.relations.limit = config.max_region_pairs_per_instruction;
    builder.relations.queries = std::mem::take(&mut budget.relations);
    let result = (|| {
        for index in 0..count.max(1) {
            budget.begin_query()?;
            let delta = query
                .start
                .checked_add((index as u64).checked_mul(stride)?)?;
            let low = pointer.offset_bytes().lower().checked_add(delta)?;
            let high = pointer.offset_bytes().upper().checked_add(delta)?;
            // Preserve domain, paths and provenance. Use the canonical offset
            // operation so object/alignment/affine metadata is not invented.
            let selected = shifted_pointer(pointer, delta, low, high);
            let width = if length == 0 { 0 } else { stride };
            let object = if let Some(authority) = query.authority.filter(|_| length != 0) {
                builder
                    .object_access_facts_for_pointer(
                        query.pointer,
                        authority,
                        query.layout,
                        query.access,
                        selected,
                    )
                    .ok()?
            } else {
                let allocation_id = match selected.provenance() {
                    AbstractProvenance::Known(id) => Some(id),
                    _ => None,
                };
                let allocation = allocation_id.and_then(|id| builder.state.allocation(id).cloned());
                builder.require(
                    ResourceObligationKind::ObjectAllocationLive {
                        pointer: query.pointer,
                        allocation: allocation_id,
                    },
                    spec_alive(&builder.state, query.pointer),
                );
                builder.require(
                    ResourceObligationKind::ObjectWithinBounds {
                        pointer: query.pointer,
                        allocation: allocation_id,
                        access: access_envelope(selected.offset_bytes(), width),
                        size_bytes: width,
                    },
                    allocation.as_ref().map_or(ObligationStatus::Unknown, |a| {
                        object_bounds_status(selected.offset_bytes(), width, a.size_bytes())
                    }),
                );
                builder.require(
                    ResourceObligationKind::PointerMemoryAccessMatches {
                        pointer: query.pointer,
                        expected: query.layout,
                        found: selected.memory_access(),
                    },
                    memory_access_status(selected.memory_access(), query.layout),
                );
                ObjectAccessFacts {
                    pointer: selected,
                    allocation_id,
                    allocation,
                    envelope: access_envelope(selected.offset_bytes(), width),
                    shape: shape.clone(),
                }
            };
            if query.authority.is_none() {
                // Geometry/initialization observations have no authority, but
                // still cannot escape a slice or subobject's declared domain.
                builder.require_domain_access(query.pointer, selected, width);
            }
            if length == 0 {
                // An empty claim has no cell to load/initialize, but is not a
                // source of authority: check the live in-bounds point and the
                // original permission (including consumed/ended loan checks).
                if let Some(authority) = query.authority {
                    builder.require_domain_access(query.pointer, selected, 0);
                    builder.require(
                        ResourceObligationKind::ObjectAligned {
                            pointer: query.pointer,
                            required_alignment: shape.alignment(),
                        },
                        object
                            .allocation
                            .as_ref()
                            .map_or(ObligationStatus::Unknown, |a| {
                                object_alignment_status(selected, a, shape.alignment())
                            }),
                    );
                    let permission = permission_fact(&builder.state, authority).ok()?;
                    builder.permission_access_obligations(
                        authority,
                        permission,
                        PermissionAccessContext {
                            allocation: object.allocation_id,
                            envelope: object.envelope,
                            pointer: selected,
                            required_access: query.access,
                            access_bytes: 0,
                        },
                    );
                }
                continue;
            }
            if let Some(allocation) = &object.allocation
                && query.valid
            {
                builder
                    .active_variant_access_obligations(
                        query.pointer,
                        selected,
                        allocation,
                        query.layout,
                        stride,
                    )
                    .ok()?;
            }
            let bytes = ByteSet::single(ByteRange::new(0, stride).ok()?);
            if query.initialized {
                builder.require_object_initialization(
                    &object,
                    &bytes,
                    InitializationRequirement::Initialized,
                );
            }
            if query.valid {
                builder.require_object_validity(&object, &bytes);
            }
        }
        Some(
            builder
                .obligations
                .iter()
                .fold(ObligationStatus::Proven, |status, o| {
                    combine_statuses([status, o.status()])
                }),
        )
    })();
    budget.relations = std::mem::take(&mut builder.relations.queries);
    result
}

fn shifted_pointer(pointer: AbstractPointer, delta: u64, low: u64, high: u64) -> AbstractPointer {
    // Offset construction follows pointer_offset, without a runtime SSA result.
    AbstractPointer::new(
        pointer.provenance(),
        U64Interval::new(low, high).expect("checked monotone offset"),
        offset_alignment(pointer.alignment(), U64Interval::exact(delta)),
    )
    .with_memory_access(pointer.memory_access())
    .with_paths(pointer.paths())
    .with_domain(pointer.domain())
    .with_slice_footprint(pointer.slice_footprint())
    .with_offset_expression(
        pointer
            .offset_expression()
            .and_then(|e| e.checked_add_constant(delta)),
    )
    .with_object_offsets(pointer.object_offsets().offset_by_exact(delta))
}
