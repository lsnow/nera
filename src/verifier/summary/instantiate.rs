//! Transactional substitution of a private closed interface. Never visits a body.
use super::effects::{EffectEvent, EffectKind};
use super::*;
use crate::verifier::{
    AbstractAllocation, AbstractAllocationId, AbstractByteRange, AbstractPermission,
    AbstractPointer, AbstractProvenance, AbstractValue, ActiveVariantState, AffineExpression,
    GuaranteedAlignment, MovePathState, ObjectStateKey, PermissionAuthority, ResourcePayloadKey,
    ResourceState, TransferError, TypedResourcePayload,
};
use crate::{VirMemorySchema, VirNominalPath, VirPointerDomain, VirPointerPaths, VirValueId};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) struct Instantiation {
    pub audit: audit::WorldInstantiation,
    pub state: ResourceState,
    pub values: Vec<AbstractValue>,
    pub expressions: BTreeMap<usize, AffineExpression>,
    pub origins: BTreeMap<usize, crate::verifier::resource::ScalarOrigin>,
    pub bool_origins: BTreeMap<usize, crate::verifier::resource::BoolOrigin>,
    pub preserved: BTreeSet<AbstractAllocationId>,
    pub events: Vec<EffectEvent>,
}
#[derive(Clone, Copy)]
struct ResourceMapping {
    id: AbstractAllocationId,
    base: u64,
    size: u64,
    anchor: Option<AbstractPointer>,
    // A proved scalar slice: preserve initialization, never materialize its envelope.
    relational_initialization: bool,
}
struct Substitution<'a> {
    before: &'a ResourceState,
    arguments: &'a [VirValueId],
    results: &'a [crate::VirValue],
    names: BTreeMap<ResourceName, ResourceMapping>,
    input_pointers: BTreeMap<ResourceName, SummaryPointer>,
    memory: &'a VirMemorySchema,
}

pub(crate) struct CallInstantiation<'a> {
    pub loss: &'a std::cell::Cell<Option<audit::MappingLoss>>,
    pub before: &'a ResourceState,
    pub consumed: &'a ResourceState,
    pub arguments: &'a [VirValueId],
    pub results: &'a [crate::VirValue],
    pub memory: &'a VirMemorySchema,
    pub site: u64,
    pub target: &'a crate::VirCallTarget,
    pub queries: &'a crate::verifier::relation::audit::QueryLog,
    pub limits: crate::verifier::relation::difference::DifferenceLimits,
}

pub(crate) fn instantiate(
    summary: &FunctionSummary,
    cx: CallInstantiation<'_>,
) -> Result<Option<Vec<Instantiation>>, TransferError> {
    let Knowledge::Known(alternatives) = &summary.normal_returns else {
        return Ok(None);
    };
    let mut outcomes = Vec::new();
    for (index, alternative) in alternatives.iter().enumerate() {
        let Some(restricted) = super::guards::restrict(&alternative.guard, &cx) else {
            cx.loss.set(Some(audit::MappingLoss::Guard));
            return Ok(None);
        };
        if !restricted.path_condition().is_reachable() {
            continue;
        }
        for world in &alternative.worlds {
            let Some(outcome) = instantiate_world(summary, world, &cx, &restricted)? else {
                return Ok(None);
            };
            let WorldResult::Applied(outcome) = outcome else {
                continue;
            };
            let mut outcome = *outcome;
            outcome.audit.alternative = index;
            outcome.audit.guard = alternative.guard.clone();
            outcomes.push(outcome);
        }
    }
    // Missing/contradictory mappings do not prove that the call cannot return.
    Ok((!outcomes.is_empty()).then_some(outcomes))
}

// A checked entry-cell equation can refute a complete return world even
// when its source branch guard could not be projected. This is distinct
// from a failed mapping, which must still make the entire call unknown.
enum WorldResult {
    Applied(Box<Instantiation>),
    Impossible,
}

fn instantiate_world(
    summary: &FunctionSummary,
    world: &ReturnWorld,
    cx: &CallInstantiation<'_>,
    restricted: &ResourceState,
) -> Result<Option<WorldResult>, TransferError> {
    if let Some(result) = instantiate_world_mode(summary, world, cx, restricted, false)? {
        return Ok(Some(result));
    }
    if !cx
        .before
        .allocations()
        .iter()
        .any(|(id, a)| !a.heap_prefixes().is_empty() || cx.before.has_logical_initialization(*id))
    {
        return Ok(None);
    }
    instantiate_world_mode(summary, world, cx, restricted, true)
}

fn instantiate_world_mode(
    summary: &FunctionSummary,
    world: &ReturnWorld,
    cx: &CallInstantiation<'_>,
    restricted: &ResourceState,
    relational: bool,
) -> Result<Option<WorldResult>, TransferError> {
    let CallInstantiation {
        arguments,
        memory,
        site,
        ..
    } = *cx;
    // Retry the whole transaction, including effects and results. An input map
    // can succeed while the virtual slice's effect extent still cannot map.
    let input = if relational { restricted } else { cx.before };
    let Some(mut sub) = Substitution::inputs(summary, input, arguments, memory, cx, relational)
    else {
        return Ok(None);
    };
    sub.results = cx.results;
    let mut state = restricted.clone();
    for resource in &world.resources {
        if let ResourceName::Fresh(index) = resource.name {
            if resource.storage != ResourceStorage::Heap {
                return Ok(None);
            }
            let id = AbstractAllocationId::SummaryInstance {
                call_site: site,
                // Return-world binders must not collide when different arms
                // allocate differently shaped objects at the same call site.
                resource: u32::try_from(world.return_evidence)
                    .ok()
                    .filter(|world| *world < 65536)
                    .zip(u32::try_from(index).ok().filter(|index| *index < 65536))
                    .and_then(|(world, index)| world.checked_mul(65536)?.checked_add(index))
                    .ok_or(TransferError::InvalidDerivedRange)?,
            };
            let Some(region) = resource.region else {
                return Ok(None);
            };
            let allocation = AbstractAllocation::new(region, resource.size, resource.alignment)?;
            state.introduce_allocation_instance(id, allocation)?;
            sub.names.insert(
                resource.name.clone(),
                ResourceMapping {
                    id,
                    base: 0,
                    size: resource.size,
                    anchor: None,
                    relational_initialization: false,
                },
            );
        }
    }
    let Some((writes, frees, mut events)) = sub.effects(&world.effects) else {
        return Ok(None);
    };
    if world
        .resources
        .iter()
        .any(|r| matches!(r.name, ResourceName::Fresh(_)))
    {
        events.push(EffectEvent {
            kind: EffectKind::Allocate,
            pointer: None,
            range: AbstractByteRange::Unknown,
        });
    }
    // Distinct formal resources are NOT an alias proof. Admit shared reads or
    // exact disjoint views; conflicting/unknown aliasing uses the skeleton.
    let inputs = summary.input_resources.iter().collect::<Vec<_>>();
    for (i, left) in inputs.iter().enumerate() {
        for right in inputs.iter().skip(i + 1) {
            let a = sub.names[&left.name];
            let b = sub.names[&right.name];
            if a.id != b.id {
                continue;
            }
            let Some(ar) = ByteRange::from_start_and_length(a.base, a.size).ok() else {
                return Ok(None);
            };
            let Some(br) = ByteRange::from_start_and_length(b.base, b.size).ok() else {
                return Ok(None);
            };
            if ar.overlaps(br)
                && (writes.contains_key(&left.name)
                    || writes.contains_key(&right.name)
                    || frees.contains(&left.name)
                    || frees.contains(&right.name))
            {
                cx.loss.set(Some(audit::MappingLoss::AliasFrame));
                return Ok(None);
            }
        }
    }
    for resource in &world.resources {
        let Some(mapping) = sub.names.get(&resource.name).copied() else {
            return Ok(None);
        };
        let fresh = matches!(resource.name, ResourceName::Fresh(_));
        let mut changed = writes.get(&resource.name).cloned().unwrap_or_default();
        if fresh {
            changed = vec![
                ByteRange::new(0, resource.size).map_err(|_| TransferError::InvalidDerivedRange)?,
            ];
        }
        let Some(allocation) = state.allocation_mut(mapping.id) else {
            return Ok(None);
        };
        if frees.contains(&resource.name) {
            // A proven normal-return liveness is a must fact, even when a
            // syntactic conditional drop contributed an overapproximated may-free.
            allocation.set_liveness(resource.liveness);
        }
        if fresh
            || summary
                .input_resources
                .iter()
                .any(|r| r.name == resource.name && r.ownership == OwnershipState::Owned)
        {
            allocation.set_ownership(resource.ownership);
        }
        if mapping.relational_initialization {
            // The independently checked borrowed ABI restores every actual
            // element. Outside the actual slice the callee has no authority.
            // Thus old initialized/valid bytes survive; no may-write envelope
            // becomes a new must-initialized range.
            let whole =
                ByteRange::new(0, resource.size).map_err(|_| TransferError::InvalidDerivedRange)?;
            if frees.contains(&resource.name)
                || resource.liveness != crate::verifier::LivenessState::Live
                || !resource.initialization.initialized().contains(whole)
                || !resource.validity.contains(whole)
                || !resource.payloads.is_empty()
                || !resource.variants.is_empty()
            {
                return Ok(None);
            }
            for relative in &changed {
                let absolute =
                    shift(*relative, mapping.base).ok_or(TransferError::InvalidDerivedRange)?;
                if relative.end() > mapping.size || absolute.end() > allocation.size_bytes() {
                    return Ok(None);
                }
                allocation.forget_preserved_slice_contents(absolute)?;
            }
            continue;
        }
        for relative in &changed {
            let absolute =
                shift(*relative, mapping.base).ok_or(TransferError::InvalidDerivedRange)?;
            if relative.end() > mapping.size || absolute.end() > allocation.size_bytes() {
                return Ok(None);
            }
            allocation.forget_initialization(absolute)?;
            allocation.forget_validity(absolute)?;
            allocation.forget_object_state(absolute)?;
            for range in resource.initialization.initialized().ranges() {
                if let Some(part) = range.intersection(*relative) {
                    allocation.mark_initialized(
                        shift(part, mapping.base).ok_or(TransferError::InvalidDerivedRange)?,
                    )?;
                }
            }
            for range in resource.initialization.uninitialized().ranges() {
                if let Some(part) = range.intersection(*relative) {
                    allocation.mark_uninitialized(
                        shift(part, mapping.base).ok_or(TransferError::InvalidDerivedRange)?,
                    )?;
                }
            }
            for range in resource.validity.ranges() {
                if let Some(part) = range.intersection(*relative) {
                    allocation.mark_valid(
                        shift(part, mapping.base).ok_or(TransferError::InvalidDerivedRange)?,
                    )?;
                }
            }
        }
        // Scalar observations carry no authority and are installed only after
        // the real initialization/validity transfer. No unknown cell is filled.
        for (range, access, value) in &resource.scalar_contents {
            if range.end() > mapping.size {
                return Ok(None);
            }
            let absolute = shift(*range, mapping.base).ok_or(TransferError::InvalidDerivedRange)?;
            allocation.record_scalar_content(absolute, *access, *value);
        }
        for (bytes, access, origin) in &resource.bool_origins {
            let Some((computed, history)) = sub.bool_origin(origin) else {
                return Ok(None);
            };
            let target = shift(*bytes, mapping.base).ok_or(TransferError::InvalidDerivedRange)?;
            let Some(AbstractValue::Bool(output)) = allocation.scalar_content(target, *access)
            else {
                return Ok(None);
            };
            let Some(value) = intersect_bool(output, computed) else {
                return Ok(Some(WorldResult::Impossible));
            };
            allocation.record_scalar_content(target, *access, AbstractValue::Bool(value));
            if let Some(origin) = history {
                allocation.set_bool_origin(target, *access, origin);
            }
        }
        for (bytes, access, origin) in &resource.scalar_origins {
            let Some((computed, history)) = sub.scalar_origin(origin) else {
                return Ok(None);
            };
            let target_bytes =
                shift(*bytes, mapping.base).ok_or(TransferError::InvalidDerivedRange)?;
            if let Some(computed) = computed
                && let Some(AbstractValue::U64(output)) =
                    allocation.scalar_content(target_bytes, *access)
            {
                let Some(refined) = output.intersection(computed) else {
                    return Ok(Some(WorldResult::Impossible));
                };
                allocation.record_scalar_content(
                    target_bytes,
                    *access,
                    AbstractValue::U64(refined),
                );
            }
            if let Some(origin) = history {
                allocation.set_scalar_origin(target_bytes, *access, origin);
            }
        }

        // Typed post-state is installed only inside a proven may-write region.
        for payload in &resource.payloads {
            let size = memory.layout(payload.access.layout).unwrap().size_bytes;
            let Some(range) = ByteRange::from_start_and_length(payload.offset, size).ok() else {
                return Ok(None);
            };
            if !changed.iter().any(|r| r.contains(range)) {
                continue;
            }
            let value = match &payload.state {
                SummaryMovePath::Moved => MovePathState::Moved,
                SummaryMovePath::Unknown => MovePathState::Unknown,
                SummaryMovePath::Available {
                    pointer,
                    permission,
                } => {
                    let Some(p) = sub.pointer(pointer) else {
                        return Ok(None);
                    };
                    let Some(q) = sub.permission(permission) else {
                        return Ok(None);
                    };
                    MovePathState::available(TypedResourcePayload::new(p, q))
                }
            };
            let key = ResourcePayloadKey::new(
                mapping
                    .base
                    .checked_add(payload.offset)
                    .ok_or(TransferError::InvalidDerivedRange)?,
                payload.access,
            );
            state
                .allocation_mut(mapping.id)
                .unwrap()
                .set_resource_payload(key, value)?;
        }
        for variant in &resource.variants {
            let Some(range) = ByteRange::from_start_and_length(
                variant.offset,
                memory.layout(variant.access.layout).unwrap().size_bytes,
            )
            .ok() else {
                return Ok(None);
            };
            if !changed.iter().any(|r| r.contains(range)) {
                continue;
            }
            let active = match &variant.alternatives {
                Knowledge::Known(tags) if tags.len() == 1 => ActiveVariantState::Exact(tags[0]),
                _ => ActiveVariantState::Unknown,
            };
            state
                .allocation_mut(mapping.id)
                .unwrap()
                .set_active_variant(
                    ObjectStateKey::new(
                        mapping
                            .base
                            .checked_add(variant.offset)
                            .ok_or(TransferError::InvalidDerivedRange)?,
                        variant.access,
                    ),
                    active,
                )?;
        }
    }
    let mut values = Vec::new();
    let mut expressions = BTreeMap::new();
    let mut origins = BTreeMap::new();
    let mut bool_origins = BTreeMap::new();
    for (index, mapping) in world.values.iter().enumerate() {
        let Some(mut value) = sub.value(&mapping.value) else {
            return Ok(None);
        };
        if let Some(origin) = &world.bool_value_origins[index] {
            let Some((computed, history)) = sub.bool_origin(origin) else {
                return Ok(None);
            };
            let AbstractValue::Bool(output) = value else {
                return Ok(None);
            };
            let Some(refined) = intersect_bool(output, computed) else {
                return Ok(Some(WorldResult::Impossible));
            };
            value = AbstractValue::Bool(refined);
            if let Some(origin) = history {
                bool_origins.insert(index, origin);
            }
        }
        if let Some(origin) = &world.value_origins[index] {
            let Some((computed, history)) = sub.scalar_origin(origin) else {
                return Ok(None);
            };
            if let Some(computed) = computed
                && let AbstractValue::U64(output) = value
            {
                let Some(refined) = output.intersection(computed) else {
                    return Ok(Some(WorldResult::Impossible));
                };
                value = AbstractValue::U64(refined);
            }
            if let Some(origin) = history {
                origins.insert(index, origin);
            }
        }

        values.push(value);
        if let SummaryValue::Word {
            expression: Some(bound),
            ..
        } = &mapping.value
            && let Some(expr) = sub.expression(bound)
        {
            expressions.insert(index, expr);
        }
        // A checked scalar forwarding equation can preserve the caller's
        // historical cell even when the callee itself has no heap parameter.
        if !origins.contains_key(&index)
            && let SummaryValue::Word {
                expression: Some(bound),
                ..
            } = &mapping.value
            && bound.result_terms.is_empty()
            && bound.result_offset_terms.is_empty()
            && let [(slot, 1)] = bound.terms.as_slice()
            && let Some(id) = sub.arguments.get(*slot)
            && let Some(AbstractValue::U64(input)) = sub.before.value(*id)
            && input.upper().checked_add(bound.addend).is_some()
            && let Some(origin) = sub
                .before
                .word_origin(*id)
                .and_then(|o| o.add(bound.addend))
        {
            origins.insert(index, origin);
        }
    }
    if !super::borrow::validate_exports(world, cx, &values) {
        return Ok(None);
    }
    let mut field_exports = Vec::new();
    for resource in &summary.input_resources {
        for payload in &resource.payloads {
            let SummaryMovePath::Available { permission, .. } = &payload.state else {
                continue;
            };
            let SummaryAuthority::InputPayloadLoan(path) = &permission.authority else {
                continue;
            };
            let mut restorations = world
                .stored_borrow_restoration
                .iter()
                .filter(|r| &r.input == path);
            let Some(restoration) = restorations.next() else {
                return Ok(None);
            };
            if restorations.next().is_some() {
                return Ok(None);
            }
            let Some(permission) = sub.permission(permission) else {
                return Ok(None);
            };
            let PermissionAuthority::Loan(loan) = permission.authority() else {
                return Ok(None);
            };
            let Some(mapped) = sub.names.get(&resource.name) else {
                return Ok(None);
            };
            let Some(offset) = mapped.base.checked_add(payload.offset) else {
                return Ok(None);
            };
            let source = (mapped.id, ResourcePayloadKey::new(offset, payload.access));
            let map_stored = |destination: &StoredBorrowLocation| {
                let mapped = sub.names.get(&destination.resource)?;
                Some((
                    mapped.id,
                    ResourcePayloadKey::new(
                        mapped.base.checked_add(destination.offset)?,
                        destination.access,
                    ),
                ))
            };
            let map_value = |slot: &usize| {
                let abi = cx.target.abi.as_ref()?;
                let (pointer_slot, permission_slot) =
                    super::borrow::field_return_slots(memory, abi, path)?;
                let (
                    Some(AbstractValue::Pointer(pointer)),
                    Some(AbstractValue::Permission(permission)),
                    Some(result),
                ) = (
                    values.get(pointer_slot),
                    values.get(*slot),
                    cx.results.get(*slot),
                )
                else {
                    return None;
                };
                (*slot == permission_slot
                    && permission.authority() == PermissionAuthority::Loan(loan))
                .then_some((result.id, *pointer, *permission))
            };
            let exit = match &restoration.exit {
                crate::BoundaryExit::Ended => Some(crate::BoundaryExit::Ended),
                crate::BoundaryExit::InPlace => Some(crate::BoundaryExit::InPlace),
                crate::BoundaryExit::Stored(destination) => {
                    map_stored(destination).map(crate::BoundaryExit::Stored)
                }
                crate::BoundaryExit::Value(slot) => map_value(slot).map(crate::BoundaryExit::Value),
                crate::BoundaryExit::Shared { stored, values } => stored
                    .iter()
                    .map(map_stored)
                    .collect::<Option<Vec<_>>>()
                    .zip(values.iter().map(map_value).collect::<Option<Vec<_>>>())
                    .map(|(stored, values)| crate::BoundaryExit::Shared { stored, values }),
            };
            let Some(exit) = exit else {
                return Ok(None);
            };
            field_exports.push(super::borrow::FieldExport { loan, source, exit });
        }
    }
    if world.stored_borrow_restoration.len() != field_exports.len()
        || !super::borrow::restore_field_group(memory, input, &mut state, &field_exports)
    {
        return Ok(None);
    }
    Ok(Some(WorldResult::Applied(Box::new(Instantiation {
        audit: audit::WorldInstantiation {
            alternative: 0,
            return_evidence: world.return_evidence,
            guard: Vec::new(),
            resources: sub
                .names
                .iter()
                .map(|(formal, r)| audit::ResourceSubstitution {
                    formal: formal.clone(),
                    allocation: r.id,
                    base: r.base,
                    size: r.size,
                })
                .collect(),
            effects: world.effects.clone(),
            results: values.clone(),
        },
        state,
        values,
        expressions,
        origins,
        bool_origins,
        preserved: sub.names.values().map(|r| r.id).collect(),
        events,
    }))))
}

fn shift(range: ByteRange, base: u64) -> Option<ByteRange> {
    ByteRange::new(
        range.start().checked_add(base)?,
        range.end().checked_add(base)?,
    )
    .ok()
}
impl<'a> Substitution<'a> {
    /// Substitute only real call-entry cells. Missing history loses the
    /// equation; missing namespace mapping fails the whole call mapping.
    fn bool_origin(
        &self,
        origin: &SummaryScalarRoot,
    ) -> Option<(AbstractBool, Option<crate::verifier::resource::BoolOrigin>)> {
        match origin {
            SummaryScalarRoot::Parameter(slot) => {
                let id = *self.arguments.get(*slot)?;
                let AbstractValue::Bool(value) = *self.before.value(id)? else {
                    return None;
                };
                Some((value, self.before.bool_origin(id)))
            }
            SummaryScalarRoot::Cell {
                resource,
                bytes,
                access,
            } => {
                let mapping = self.names.get(resource)?;
                if bytes.end() > mapping.size {
                    return None;
                }
                let bytes = shift(*bytes, mapping.base)?;
                let allocation = self.before.allocation(mapping.id)?;
                let AbstractValue::Bool(value) = allocation.scalar_content(bytes, *access)? else {
                    return None;
                };
                Some((value, allocation.bool_origin(bytes, *access)))
            }
        }
    }
    fn scalar_origin(
        &self,
        origin: &SummaryScalarOrigin,
    ) -> Option<(
        Option<U64Interval>,
        Option<crate::verifier::resource::ScalarOrigin>,
    )> {
        let mut interval = Some(U64Interval::exact(origin.addend));
        let mut history: Option<crate::verifier::resource::ScalarOrigin> = None;
        let mut history_complete = true;
        let mut constant = Some(origin.addend);
        for source in origin.sources() {
            let (value, cell) = match source.root {
                SummaryScalarRoot::Parameter(slot) => {
                    let id = *self.arguments.get(slot)?;
                    let value = match self.before.value(id) {
                        Some(AbstractValue::U64(value)) => Some(*value),
                        _ => return None,
                    };
                    (value, self.before.word_origin(id))
                }
                SummaryScalarRoot::Cell {
                    ref resource,
                    bytes,
                    access,
                } => {
                    let mapping = self.names.get(resource)?;
                    let bytes = shift(bytes, mapping.base)?;
                    let allocation = self.before.allocation(mapping.id);
                    let value = match allocation.and_then(|a| a.scalar_content(bytes, access)) {
                        Some(AbstractValue::U64(value)) => Some(value),
                        _ => None,
                    };
                    (
                        value,
                        allocation.and_then(|a| a.scalar_origin(bytes, access)),
                    )
                }
            };
            interval = interval.zip(value).and_then(|(a, b)| {
                U64Interval::new(
                    a.lower()
                        .checked_add(b.lower().checked_mul(source.scale)?)?,
                    a.upper()
                        .checked_add(b.upper().checked_mul(source.scale)?)?,
                )
                .ok()
            });
            if let Some(cell) = cell.and_then(|o| o.scale(source.scale)) {
                history = match history {
                    None => Some(cell),
                    Some(previous) => previous.sum(cell),
                };
                history_complete &= history.is_some();
            } else if let Some(value) = value.and_then(|v| v.exact_value()) {
                constant = constant.and_then(|c| c.checked_add(value.checked_mul(source.scale)?));
            } else {
                history_complete = false;
            }
        }
        Some((
            interval,
            history_complete
                .then_some(history)
                .flatten()
                .and_then(|o| o.add(constant?)),
        ))
    }

    fn inputs(
        summary: &FunctionSummary,
        before: &'a ResourceState,
        arguments: &'a [VirValueId],
        memory: &'a VirMemorySchema,
        cx: &CallInstantiation<'_>,
        allow_relational: bool,
    ) -> Option<Self> {
        let mut sub = Self {
            before,
            arguments,
            results: &[],
            names: BTreeMap::new(),
            input_pointers: BTreeMap::new(),
            memory,
        };
        for resource in &summary.input_resources {
            let ResourceName::Input {
                parameter,
                payload_offsets,
            } = &resource.name
            else {
                return None;
            };
            let (mut id, mut base, mut anchor) = match before.value(*arguments.get(*parameter)?)? {
                AbstractValue::Pointer(p) => (
                    known(p.provenance())?,
                    p.offset_bytes().exact_value()?,
                    Some(*p),
                ),
                AbstractValue::Permission(p) => (known(p.provenance())?, 0, None),
                _ => return None,
            };
            for offset in payload_offsets {
                let at = base.checked_add(*offset)?;
                let payloads = before
                    .allocation(id)?
                    .object_state()
                    .resource_payloads()
                    .iter()
                    .filter(|(k, _)| k.offset_bytes() == at)
                    .collect::<Vec<_>>();
                let [(_, MovePathState::Available(payload))] = payloads.as_slice() else {
                    return None;
                };
                id = known(payload.pointer().provenance())?;
                base = payload.pointer().offset_bytes().exact_value()?;
                anchor = Some(payload.pointer());
            }
            sub.names.insert(
                resource.name.clone(),
                ResourceMapping {
                    id,
                    base,
                    size: resource.size,
                    anchor,
                    relational_initialization: false,
                },
            );
            if payload_offsets.is_empty()
                && let SummaryValue::Pointer(pointer) = &summary.inputs.get(*parameter)?.value
            {
                sub.input_pointers
                    .insert(resource.name.clone(), (**pointer).clone());
            } else if let Some((&offset, parent)) = payload_offsets.split_last() {
                // Stored inputs also have an immutable entry pointer. Preserve
                // its actual caller domain only when the exported pointer is
                // exactly this checked formal value, never merely the same
                // resource name or address interval.
                let parent = ResourceName::Input {
                    parameter: *parameter,
                    payload_offsets: parent.to_vec(),
                };
                let container = summary.input_resources.iter().find(|r| r.name == parent)?;
                let mut fields = container.payloads.iter().filter(|p| p.offset == offset);
                let field = fields.next()?;
                if fields.next().is_some() {
                    return None;
                }
                let SummaryMovePath::Available { pointer, .. } = &field.state else {
                    return None;
                };
                if pointer.resource != Knowledge::Known(resource.name.clone()) {
                    return None;
                }
                sub.input_pointers
                    .insert(resource.name.clone(), (**pointer).clone());
            }
            // Slice entry allocations are virtual signature extents. Substitute
            // their length-bound view, never require u64::MAX bytes in a caller.
            // Only the exported slice footprint admits this restriction.
            let size = if payload_offsets.is_empty()
                && let SummaryValue::Pointer(pointer) = &summary.inputs.get(*parameter)?.value
                && let Some(range) = &pointer.slice_range
            {
                let range = sub.range(range, base)?;
                let (start, end) = range.bounds()?;
                if start.interval().exact_value()? != base {
                    return None;
                }
                let size = end.interval().upper().checked_sub(base)?;
                if size > resource.size {
                    return None;
                }
                size
            } else {
                resource.size
            };
            sub.names.get_mut(&resource.name)?.size = size;
            let extent = ByteRange::new(0, size).ok()?;
            let allocation = before.allocation(id)?;
            if base.checked_add(size)? > allocation.size_bytes()
                || allocation.liveness() != resource.liveness
                || resource.ownership == OwnershipState::Owned
                    && allocation.ownership() != OwnershipState::Owned
            {
                return None;
            }
            let relational_view = (|| {
                if !allow_relational {
                    return None;
                }
                // Stored cursors and logical certificates both feed the same
                // typed range query below. Presence only enables this attempt;
                // it never proves the input slice initialized by itself.
                if !allocation
                    .heap_prefixes()
                    .iter()
                    .any(|(p, _)| allocation.heap_prefix_valid(*p))
                    && !before.has_logical_initialization(id)
                {
                    return None;
                }
                let envelope = shift(extent, base)?;
                let complete = allocation.initialization().initialized().contains(envelope)
                    && allocation.valid_value_bytes().contains(envelope);
                if !payload_offsets.is_empty() {
                    return None;
                }
                let binding =
                    cx.target.abi.as_ref()?.parameters().iter().find(|b| {
                        b.parameter_slots().first().copied() == Some(*parameter as u32)
                    })?;
                let crate::VirAbiValue::Slice { element, .. } = binding.value() else {
                    return None;
                };
                if !binding.interface().transfer.is_borrow()
                    || !matches!(
                        memory.kind(element.ty),
                        Some(
                            crate::VirMemoryTypeKind::Bool
                                | crate::VirMemoryTypeKind::Integer(
                                    crate::VirIntegerType::U64 | crate::VirIntegerType::Usize
                                )
                        )
                    )
                {
                    return None;
                }
                let pointer = sub.input_pointers.get(&resource.name)?;
                let range = sub.range(pointer.slice_range.as_ref()?, base)?;
                let whole = ByteRange::new(0, resource.size).ok()?;
                if !resource.initialization.initialized().contains(whole)
                    || !resource.validity.contains(whole)
                    || (!complete
                        && !before
                            .initialized_prefix_covers(id, *element, range, cx.limits, cx.queries))
                {
                    return None;
                }
                let (start, end) = range.bounds()?;
                if start.interval().exact_value()? != base {
                    return None;
                }
                end.interval().lower().checked_sub(base)
            })();
            if relational_view.is_some() {
                sub.names.get_mut(&resource.name)?.relational_initialization = true;
            }
            for range in resource.initialization.initialized().ranges() {
                let Some(range) = range.intersection(extent) else {
                    continue;
                };
                if relational_view.is_none()
                    && !allocation
                        .initialization()
                        .initialized()
                        .contains(shift(range, base)?)
                {
                    return None;
                }
            }
            for range in resource.initialization.uninitialized().ranges() {
                let Some(range) = range.intersection(extent) else {
                    continue;
                };
                if !allocation
                    .initialization()
                    .uninitialized()
                    .contains(shift(range, base)?)
                {
                    return None;
                }
            }
            for (range, access, expected) in &resource.scalar_contents {
                if !extent.contains(*range) {
                    return None;
                }
                let actual = input_scalar(allocation, shift(*range, base)?, *access, memory)?;
                let matches = match (actual, *expected) {
                    (AbstractValue::U64(a), AbstractValue::U64(e)) => {
                        a.lower() >= e.lower() && a.upper() <= e.upper()
                    }
                    (AbstractValue::Bool(a), AbstractValue::Bool(e)) => {
                        e == super::AbstractBool::Unknown || a == e
                    }
                    _ => false,
                };
                if !matches {
                    return None;
                }
            }
            for range in resource.validity.ranges() {
                let Some(range) = range.intersection(extent) else {
                    continue;
                };
                if relational_view.is_none()
                    && !allocation.valid_value_bytes().contains(shift(range, base)?)
                {
                    return None;
                }
            }
        }
        Some(sub)
    }
    fn expression(&self, bound: &SummaryBound) -> Option<AffineExpression> {
        let mut result = AffineExpression::constant(bound.addend);
        for (index, scale) in &bound.terms {
            let id = *self.arguments.get(*index)?;
            let expr =
                self.before
                    .word_expression(id)
                    .or_else(|| match self.before.value(id)? {
                        AbstractValue::U64(interval) => {
                            interval.exact_value().map(AffineExpression::constant)
                        }
                        _ => None,
                    })?;
            result = result.checked_add(expr.checked_scale(*scale)?)?;
        }
        for (index, scale) in bound.result_terms.iter().chain(&bound.result_offset_terms) {
            let result_id = self.results.get(*index)?.id;
            result =
                result.checked_add(AffineExpression::identity(result_id).checked_scale(*scale)?)?;
        }
        Some(result)
    }
    fn bound_interval(&self, bound: &SummaryBound) -> Option<U64Interval> {
        if !bound.result_terms.is_empty() || !bound.result_offset_terms.is_empty() {
            // This is the checked callee range, not a caller input estimate.
            // The associated expression uses fresh actual result SSA identities.
            return Some(bound.interval);
        }
        let (mut low, mut high) = (bound.addend, bound.addend);
        for (index, scale) in &bound.terms {
            let AbstractValue::U64(value) = self.before.value(*self.arguments.get(*index)?)? else {
                return None;
            };
            low = low.checked_add(value.lower().checked_mul(*scale)?)?;
            high = high.checked_add(value.upper().checked_mul(*scale)?)?;
        }
        U64Interval::new(low, high)
            .ok()?
            .intersection(bound.interval)
    }
    fn range(&self, range: &SummaryRange, base: u64) -> Option<AbstractByteRange> {
        match range {
            SummaryRange::Exact(r) => Some(AbstractByteRange::Exact(shift(*r, base)?)),
            SummaryRange::Symbolic { start, end } => Some(AbstractByteRange::Symbolic {
                start: crate::verifier::SymbolicRangeBound::new(
                    self.expression(start)?.checked_add_constant(base)?,
                    add_interval(self.bound_interval(start)?, base)?,
                ),
                end: crate::verifier::SymbolicRangeBound::new(
                    self.expression(end)?.checked_add_constant(base)?,
                    add_interval(self.bound_interval(end)?, base)?,
                ),
            }),
            SummaryRange::Unknown => None,
        }
    }
    fn path(&self, path: &SummaryPath) -> Option<VirNominalPath> {
        let root = if let Some((index, role)) = path.parameter {
            let AbstractValue::Pointer(p) = self.before.value(*self.arguments.get(index)?)? else {
                return None;
            };
            match role {
                0 => p.paths().object?,
                1 => p.paths().domain?,
                2 => p.paths().selected().domain?,
                _ => return None,
            }
        } else {
            VirNominalPath::root(path.access)
        };
        root.extend(&path.steps)
    }
    fn pointer(&self, pointer: &SummaryPointer) -> Option<AbstractPointer> {
        let Knowledge::Known(name) = &pointer.resource else {
            return None;
        };
        let mapping = self.names.get(name)?;
        // An unchanged interface pointer denotes the caller's entire pointer
        // metadata, including its incoming arithmetic domain (which can be
        // wider than the borrowed permission). This is exact value substitution,
        // not the ABI skeleton overwriting an arbitrary derived result view.
        if self.input_pointers.get(name) == Some(pointer)
            && let Some(anchor) = mapping.anchor
        {
            return Some(anchor);
        }
        let inherited = mapping
            .anchor
            .filter(|p| {
                pointer.offset.exact_value() == Some(0)
                    && pointer.access == p.memory_access()
                    && pointer.object_path.is_none()
                    && pointer.domain_path.is_none()
            })
            .map(|p| p.paths())
            .unwrap_or_default();
        let mut p = AbstractPointer::new(
            AbstractProvenance::Known(mapping.id),
            pointer.offset_expression.as_ref().map_or_else(
                || add_interval(pointer.offset, mapping.base),
                |bound| add_interval(self.bound_interval(bound)?, mapping.base),
            )?,
            GuaranteedAlignment::new(mapping.anchor.map_or(pointer.alignment, |a| {
                pointer.alignment.min(a.alignment().bytes())
            }))
            .ok()?,
        )
        .with_memory_access(pointer.access)
        .with_paths(VirPointerPaths {
            object: pointer
                .object_path
                .as_ref()
                .and_then(|p| self.path(p))
                .or(inherited.object),
            domain: pointer
                .domain_path
                .as_ref()
                .and_then(|p| self.path(p))
                .or(inherited.domain),
        })
        .with_offset_expression(
            pointer
                .offset_expression
                .as_ref()
                .and_then(|bound| self.expression(bound))
                .and_then(|expression| expression.checked_add_constant(mapping.base)),
        )
        .with_domain(match &pointer.domain {
            SummaryDomain::Allocation => mapping
                .anchor
                .map_or(VirPointerDomain::Allocation, |p| p.domain()),
            SummaryDomain::Restricted(range) => {
                VirPointerDomain::Restricted(self.range(range, mapping.base)?)
            }
            SummaryDomain::Unknown => VirPointerDomain::Unknown,
        });
        if let Some(range) = &pointer.slice_range {
            let range = self.range(range, mapping.base)?;
            let access = pointer.access?;
            let bounds = range.bounds()?;
            p = p.with_slice_footprint(Some(crate::verifier::MemoryFootprint {
                provenance: p.provenance(),
                access,
                stride_bytes: self.memory.layout(access.layout)?.size_bytes,
                range,
                envelope: ByteRange::new(bounds.0.interval().lower(), bounds.1.interval().upper())
                    .ok()?,
            }));
        }
        Some(p)
    }
    fn permission(&self, permission: &SummaryPermission) -> Option<AbstractPermission> {
        let Knowledge::Known(name) = &permission.resource else {
            return None;
        };
        let mapping = self.names.get(name)?;
        let authority = match &permission.authority {
            SummaryAuthority::Owner => PermissionAuthority::Owner,
            SummaryAuthority::InputLoan(index) => {
                match self.before.value(*self.arguments.get(*index)?)? {
                    AbstractValue::Permission(p)
                        if p.provenance() == AbstractProvenance::Known(mapping.id)
                            && matches!(p.authority(), PermissionAuthority::Loan(_))
                            && p.free_capability() == FreeCapability::No
                            && permission.free == FreeCapability::No
                            && (p.access() == permission.access
                                || p.access() == AccessPermission::Write) =>
                    {
                        p.authority()
                    }
                    _ => return None,
                }
            }
            SummaryAuthority::InputPayloadLoan(path) => {
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
                let mut parent = payload_offsets.clone();
                let offset = parent.pop()?;
                let storage = self.names.get(&ResourceName::Input {
                    parameter: *parameter,
                    payload_offsets: parent,
                })?;
                let at = storage.base.checked_add(offset)?;
                let mut payloads = self
                    .before
                    .allocation(storage.id)?
                    .object_state()
                    .resource_payloads()
                    .iter()
                    .filter(|(key, _)| key.offset_bytes() == at);
                let (key, MovePathState::Available(payload)) = payloads.next()? else {
                    return None;
                };
                if payloads.next().is_some()
                    || !matches!(
                        self.memory.kind(key.access().ty),
                        Some(crate::VirMemoryTypeKind::Pointer {
                            kind: crate::VirPointerKind::Reference,
                            ..
                        })
                    )
                {
                    return None;
                }
                let p = payload.permission();
                if !super::borrow::stored_reference_shape(
                    self.memory,
                    key.access(),
                    payload.pointer().memory_access(),
                    p.access(),
                    p.free_capability(),
                ) {
                    return None;
                }
                let PermissionAuthority::Loan(id) = p.authority() else {
                    return None;
                };
                let loan = self.before.loan(id)?;
                if loan.activity() != crate::verifier::LoanActivity::Active
                    || p.access()
                        != if loan.kind() == crate::VirLoanKind::Shared {
                            AccessPermission::Read
                        } else {
                            AccessPermission::Write
                        }
                    || !loan.authorities().contains(
                        &crate::verifier::resource::AbstractLoanAuthority::stored(storage.id, *key),
                    )
                    || p.provenance() != AbstractProvenance::Known(mapping.id)
                    || payload.pointer().provenance() != p.provenance()
                    || loan.provenance() != p.provenance()
                    || loan.actual_range() != p.range()
                    || p.range() != self.range(&permission.range, mapping.base)?
                    || p.free_capability() != FreeCapability::No
                    || p.availability() != crate::verifier::PermissionAvailability::Available
                    || permission.free != FreeCapability::No
                    || (p.access() != permission.access && p.access() != AccessPermission::Write)
                {
                    return None;
                }
                p.authority()
            }
            SummaryAuthority::Unknown => return None,
        };
        Some(
            AbstractPermission::new(
                AbstractProvenance::Known(mapping.id),
                self.range(&permission.range, mapping.base)?,
                permission.access,
                permission.free,
            )
            .with_availability(permission.availability)
            .with_authority(authority),
        )
    }
    fn value(&self, value: &SummaryValue) -> Option<AbstractValue> {
        Some(match value {
            SummaryValue::Word {
                interval,
                expression,
            } => AbstractValue::U64(
                expression
                    .as_ref()
                    .and_then(|b| self.bound_interval(b))
                    .unwrap_or(*interval),
            ),
            SummaryValue::Bool(value) => AbstractValue::Bool(*value),
            SummaryValue::Pointer(p) => AbstractValue::Pointer(self.pointer(p)?),
            SummaryValue::Permission(p) => AbstractValue::Permission(self.permission(p)?),
        })
    }
    fn effects(&self, effects: &SummaryEffects) -> Option<MappedEffects> {
        let (Knowledge::Known(reads), Knowledge::Known(writes), Knowledge::Known(frees)) =
            (&effects.may_read, &effects.may_write, &effects.may_free)
        else {
            return None;
        };
        let mut changed = BTreeMap::<ResourceName, Vec<ByteRange>>::new();
        let mut events = Vec::new();
        for (kind, footprints) in [(EffectKind::Read, reads), (EffectKind::Write, writes)] {
            for footprint in footprints {
                let mapping = self.names.get(&footprint.resource)?;
                let range = if mapping.relational_initialization {
                    // Intersect may effects with the input slice's possible
                    // extent before shifting, so a virtual extent cannot overflow.
                    let SummaryRange::Exact(relative) = &footprint.range else {
                        return None;
                    };
                    let extent = ByteRange::new(0, mapping.size).ok()?;
                    let Some(relative) = relative.intersection(extent) else {
                        continue;
                    };
                    AbstractByteRange::Exact(shift(relative, mapping.base)?)
                } else {
                    self.range(&footprint.range, mapping.base)?
                };
                if kind == EffectKind::Write {
                    let AbstractByteRange::Exact(absolute) = range else {
                        return None;
                    };
                    changed.entry(footprint.resource.clone()).or_default().push(
                        ByteRange::new(
                            absolute.start().checked_sub(mapping.base)?,
                            absolute.end().checked_sub(mapping.base)?,
                        )
                        .ok()?,
                    );
                }
                events.push(EffectEvent {
                    kind,
                    pointer: Some(AbstractPointer::new(
                        AbstractProvenance::Known(mapping.id),
                        U64Interval::exact(mapping.base),
                        GuaranteedAlignment::one(),
                    )),
                    range,
                });
            }
        }
        for name in frees {
            let mapping = self.names.get(name)?;
            events.push(EffectEvent {
                kind: EffectKind::Free,
                pointer: Some(AbstractPointer::new(
                    AbstractProvenance::Known(mapping.id),
                    U64Interval::exact(mapping.base),
                    GuaranteedAlignment::one(),
                )),
                range: AbstractByteRange::Unknown,
            });
        }
        Some((changed, frees.iter().cloned().collect(), events))
    }
}
type MappedEffects = (
    BTreeMap<ResourceName, Vec<ByteRange>>,
    BTreeSet<ResourceName>,
    Vec<EffectEvent>,
);
fn known(p: AbstractProvenance) -> Option<AbstractAllocationId> {
    match p {
        AbstractProvenance::Known(id) => Some(id),
        _ => None,
    }
}
fn add_interval(value: U64Interval, base: u64) -> Option<U64Interval> {
    U64Interval::new(
        value.lower().checked_add(base)?,
        value.upper().checked_add(base)?,
    )
    .ok()
}

/// No content entry means an unknown value, provided the actual typed bytes
/// are initialized and valid. It is not an absent memory cell. Keep this
/// adaptation separate from scalar constraint comparison and origin transport.
fn input_scalar(
    allocation: &AbstractAllocation,
    range: ByteRange,
    access: crate::VirMemoryAccess,
    memory: &VirMemorySchema,
) -> Option<AbstractValue> {
    if let Some(value) = allocation.scalar_content(range, access) {
        return Some(value);
    }
    if memory.access(access.ty) != Some(access)
        || memory.layout(access.layout)?.size_bytes != range.length()
        || !allocation.initialization().initialized().contains(range)
        || !allocation.valid_value_bytes().contains(range)
    {
        return None;
    }
    match memory.kind(access.ty)? {
        crate::VirMemoryTypeKind::Integer(
            crate::VirIntegerType::U64 | crate::VirIntegerType::Usize,
        ) => Some(AbstractValue::U64(U64Interval::unknown())),
        crate::VirMemoryTypeKind::Bool => Some(AbstractValue::Bool(super::AbstractBool::Unknown)),
        _ => None,
    }
}

#[cfg(test)]
mod scalar_input_tests {
    use super::*;

    #[test]
    fn missing_contents_mean_unknown_only_for_initialized_valid_typed_scalars() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "scalar-input.nera",
            "fn main()->u64 { let flag=true; return 0; }",
        ));
        let memory = &output.vir().unwrap().as_unit().memory;
        for (access, expected) in memory.types.iter().filter_map(|ty| {
            let expected = match ty.kind {
                crate::VirMemoryTypeKind::Integer(
                    crate::VirIntegerType::U64 | crate::VirIntegerType::Usize,
                ) => AbstractValue::U64(U64Interval::unknown()),
                crate::VirMemoryTypeKind::Bool => {
                    AbstractValue::Bool(super::super::AbstractBool::Unknown)
                }
                _ => return None,
            };
            Some((memory.access(ty.id).unwrap(), expected))
        }) {
            let bytes = memory.layout(access.layout).unwrap().size_bytes;
            let range = ByteRange::new(0, bytes).unwrap();
            let mut allocation = AbstractAllocation::new_local(bytes, 8).unwrap();
            assert_eq!(input_scalar(&allocation, range, access, memory), None);
            allocation.mark_initialized(range).unwrap();
            assert_eq!(input_scalar(&allocation, range, access, memory), None);
            allocation.mark_valid(range).unwrap();
            let before = allocation.clone();
            assert_eq!(
                input_scalar(&allocation, range, access, memory),
                Some(expected)
            );
            assert_eq!(allocation, before);
            let wrong = crate::VirMemoryAccess {
                layout: crate::VirLayoutId::new(u32::MAX),
                ..access
            };
            assert_eq!(input_scalar(&allocation, range, wrong, memory), None);
            assert_eq!(
                input_scalar(
                    &allocation,
                    ByteRange::new(0, bytes + 1).unwrap(),
                    access,
                    memory
                ),
                None
            );
        }
    }
}

#[cfg(test)]
mod stored_loan_tests {
    use super::*;
    use crate::verifier::{AbstractLoan, LoanActivity};

    #[test]
    fn payload_loan_substitution_requires_the_actual_typed_stored_authority() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "stored-summary.nera",
            "fn read(p:&mut u64)->u64{return *p;} fn main()->u64{return 0;}",
        ));
        let memory = &output.vir().unwrap().as_unit().memory;
        let reference = memory
            .types
            .iter()
            .find_map(|ty| {
                matches!(
                    ty.kind,
                    crate::VirMemoryTypeKind::Pointer {
                        kind: crate::VirPointerKind::Reference,
                        ..
                    }
                )
                .then(|| memory.access(ty.id).unwrap())
            })
            .unwrap();
        let crate::VirMemoryTypeKind::Pointer { pointee, .. } = memory.kind(reference.ty).unwrap()
        else {
            unreachable!()
        };
        let pointee = memory.access(*pointee).unwrap();
        let storage = AbstractAllocationId::new(0);
        let referent = AbstractAllocationId::new(1);
        let provenance = AbstractProvenance::Known(referent);
        let range = ByteRange::new(0, 8).unwrap();
        let key = ResourcePayloadKey::new(0, reference);
        let id = crate::VirLoanId::new(7);
        let mut before = ResourceState::new();
        for allocation in [storage, referent] {
            before
                .define_allocation(allocation, AbstractAllocation::new_local(8, 8).unwrap())
                .unwrap();
        }
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
        loan.add_stored_authority(storage, key);
        before.define_loan(id, loan).unwrap();
        let permission = AbstractPermission::new(
            provenance,
            AbstractByteRange::Exact(range),
            AccessPermission::Write,
            FreeCapability::No,
        )
        .with_authority(PermissionAuthority::Loan(id));
        before
            .allocation_mut(storage)
            .unwrap()
            .set_resource_payload(
                key,
                MovePathState::available(TypedResourcePayload::new(
                    AbstractPointer::new(
                        provenance,
                        U64Interval::exact(0),
                        GuaranteedAlignment::new(8).unwrap(),
                    )
                    .with_memory_access(Some(pointee)),
                    permission,
                )),
            )
            .unwrap();
        let root = ResourceName::Input {
            parameter: 0,
            payload_offsets: vec![],
        };
        let child = ResourceName::Input {
            parameter: 0,
            payload_offsets: vec![0],
        };
        let names = BTreeMap::from([
            (
                root,
                ResourceMapping {
                    id: storage,
                    base: 0,
                    size: 8,
                    anchor: None,
                    relational_initialization: false,
                },
            ),
            (
                child.clone(),
                ResourceMapping {
                    id: referent,
                    base: 0,
                    size: 8,
                    anchor: None,
                    relational_initialization: false,
                },
            ),
        ]);
        let formal = SummaryPermission {
            resource: Knowledge::Known(child.clone()),
            range: SummaryRange::Exact(range),
            access: AccessPermission::Write,
            free: FreeCapability::No,
            availability: PermissionAvailability::Available,
            authority: SummaryAuthority::InputPayloadLoan(child),
        };
        let substitute = |state: &ResourceState, formal: &SummaryPermission| {
            Substitution {
                before: state,
                arguments: &[],
                results: &[],
                names: names.clone(),
                input_pointers: BTreeMap::new(),
                memory,
            }
            .permission(formal)
        };
        assert_eq!(substitute(&before, &formal), Some(permission));
        let mut no_footprint = before.clone();
        *no_footprint.loan_mut(id).unwrap() = before.loan(id).unwrap().clone().with_footprint(None);
        assert_eq!(substitute(&no_footprint, &formal), None);
        let mut missing = before.clone();
        assert!(
            missing
                .loan_mut(id)
                .unwrap()
                .remove_stored_authority(storage, key)
        );
        assert_eq!(substitute(&missing, &formal), None);
        let mut suspended = before.clone();
        suspended
            .loan_mut(id)
            .unwrap()
            .set_activity(LoanActivity::Suspended);
        assert_eq!(substitute(&suspended, &formal), None);
        let mut wider = formal.clone();
        wider.range = SummaryRange::Exact(ByteRange::new(0, 16).unwrap());
        assert_eq!(substitute(&before, &wider), None);
        let mut free = formal.clone();
        free.free = FreeCapability::Yes;
        assert_eq!(substitute(&before, &free), None);
        let mut wrong = formal.clone();
        wrong.authority = SummaryAuthority::InputPayloadLoan(ResourceName::Input {
            parameter: 0,
            payload_offsets: vec![8],
        });
        assert_eq!(substitute(&before, &wrong), None);
    }
}

fn intersect_bool(left: AbstractBool, right: AbstractBool) -> Option<AbstractBool> {
    match (left, right) {
        (AbstractBool::Unknown, value) | (value, AbstractBool::Unknown) => Some(value),
        (a, b) if a == b => Some(a),
        _ => None,
    }
}
