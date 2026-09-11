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
    pub preserved: BTreeSet<AbstractAllocationId>,
    pub events: Vec<EffectEvent>,
}
#[derive(Clone, Copy)]
struct ResourceMapping {
    id: AbstractAllocationId,
    base: u64,
    size: u64,
    anchor: Option<AbstractPointer>,
}
struct Substitution<'a> {
    before: &'a ResourceState,
    arguments: &'a [VirValueId],
    names: BTreeMap<ResourceName, ResourceMapping>,
    input_pointers: BTreeMap<ResourceName, SummaryPointer>,
    memory: &'a VirMemorySchema,
}

pub(crate) struct CallInstantiation<'a> {
    pub loss: &'a std::cell::Cell<Option<audit::MappingLoss>>,
    pub before: &'a ResourceState,
    pub consumed: &'a ResourceState,
    pub arguments: &'a [VirValueId],
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
            let Some(mut outcome) = instantiate_world(summary, world, &cx, &restricted)? else {
                return Ok(None);
            };
            outcome.audit.alternative = index;
            outcome.audit.guard = alternative.guard.clone();
            outcomes.push(outcome);
        }
    }
    // Missing/contradictory mappings do not prove that the call cannot return.
    Ok((!outcomes.is_empty()).then_some(outcomes))
}

fn instantiate_world(
    summary: &FunctionSummary,
    world: &ReturnWorld,
    cx: &CallInstantiation<'_>,
    restricted: &ResourceState,
) -> Result<Option<Instantiation>, TransferError> {
    let CallInstantiation {
        before,
        arguments,
        memory,
        site,
        ..
    } = *cx;
    // All fallible shape/alias mappings run on a clone. A failed attempt never
    // partially installs facts into the canonical caller state.
    let Some(mut sub) = Substitution::inputs(summary, before, arguments, memory) else {
        return Ok(None);
    };
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
    for (index, mapping) in world.values.iter().enumerate() {
        let Some(value) = sub.value(&mapping.value) else {
            return Ok(None);
        };
        values.push(value);
        if let SummaryValue::Word {
            expression: Some(bound),
            ..
        } = &mapping.value
            && let Some(expr) = sub.expression(bound)
        {
            expressions.insert(index, expr);
        }
    }
    if !super::borrow::validate_exports(world, cx, &values) {
        return Ok(None);
    }
    Ok(Some(Instantiation {
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
        preserved: sub.names.values().map(|r| r.id).collect(),
        events,
    }))
}

fn shift(range: ByteRange, base: u64) -> Option<ByteRange> {
    ByteRange::new(
        range.start().checked_add(base)?,
        range.end().checked_add(base)?,
    )
    .ok()
}
impl<'a> Substitution<'a> {
    fn inputs(
        summary: &FunctionSummary,
        before: &'a ResourceState,
        arguments: &'a [VirValueId],
        memory: &'a VirMemorySchema,
    ) -> Option<Self> {
        let mut sub = Self {
            before,
            arguments,
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
                },
            );
            if payload_offsets.is_empty()
                && let SummaryValue::Pointer(pointer) = &summary.inputs.get(*parameter)?.value
            {
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
            for range in resource.initialization.initialized().ranges() {
                let Some(range) = range.intersection(extent) else {
                    continue;
                };
                if !allocation
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
            for range in resource.validity.ranges() {
                let Some(range) = range.intersection(extent) else {
                    continue;
                };
                if !allocation.valid_value_bytes().contains(shift(range, base)?) {
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
        Some(result)
    }
    fn bound_interval(&self, bound: &SummaryBound) -> Option<U64Interval> {
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
        let authority = match permission.authority {
            SummaryAuthority::Owner => PermissionAuthority::Owner,
            SummaryAuthority::InputLoan(index) => {
                match self.before.value(*self.arguments.get(index)?)? {
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
                let range = self.range(&footprint.range, mapping.base)?;
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
