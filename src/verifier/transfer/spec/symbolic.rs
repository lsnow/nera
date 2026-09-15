//! Non-enumerating scalar ranges. Shares the ordinary domain/permission/loan
//! access rules, but observes initialized facts without executing a write.
use super::*;

#[derive(Clone, Copy)]
pub(in crate::verifier) struct SymbolicSpecMemoryQuery {
    pub pointer: VirValueId,
    pub authority: Option<VirValueId>,
    pub start: SymbolicRangeBound,
    pub end: SymbolicRangeBound,
    pub layout: VirMemoryAccess,
    pub access: AccessPermission,
    pub initialized: bool,
}

pub(in crate::verifier) fn query_symbolic_spec_memory(
    state: &ResourceState,
    memory: &VirMemorySchema,
    query: SymbolicSpecMemoryQuery,
    config: crate::CfgAnalysisConfig,
    budget: &mut VcQueryBudget,
) -> Option<(ObligationStatus, SpecFootprint)> {
    budget.begin_query()?;
    let pointer = pointer_fact(state, query.pointer).ok()?;
    let AbstractProvenance::Known(id) = pointer.provenance() else {
        return None;
    };
    let allocation = state.allocation(id)?;
    let source = pointer.memory_access()?;
    let element = match memory.kind(source.ty)? {
        VirMemoryTypeKind::Array { element, .. } => memory.access(*element)?,
        _ => source,
    };
    if element != query.layout
        || !matches!(
            memory.kind(element.ty),
            Some(
                VirMemoryTypeKind::Bool
                    | VirMemoryTypeKind::Integer(
                        crate::VirIntegerType::U64 | crate::VirIntegerType::Usize
                    )
            )
        )
    {
        return None;
    }
    let offset = pointer.offset_bytes().exact_value()?;
    let start = query.start.checked_add_constant(offset)?;
    let end = query.end.checked_add_constant(offset)?;
    let range = AbstractByteRange::from_bounds(start, end);
    let envelope = ByteRange::new(start.interval().lower(), end.interval().upper()).ok();
    let footprint = SpecFootprint {
        provenance: pointer.provenance(),
        range,
        access: query.access,
    };
    let shape = memory.object_shape(source).ok()?;
    let extent = ByteRange::from_start_and_length(offset, shape.size_bytes()).ok()?;
    let alignment = memory.object_shape(element).ok()?.alignment();
    let mut builder = TransferBuilder::new(state.clone(), ByteSpan::new(0, 0)?, memory, None, None);
    builder.relation_limits = budget.relation_limits;
    builder.relations.limit = config.max_region_pairs_per_instruction;
    builder.relations.queries = std::mem::take(&mut budget.relations);
    let aligned = start.expression().guaranteed_alignment().bytes() >= alignment
        && end.expression().guaranteed_alignment().bytes() >= alignment
        && allocation.alignment().bytes() >= alignment;
    let bounds = builder.relations.queries.contained(
        state,
        AbstractByteRange::Exact(extent),
        range,
        budget.relation_limits,
    );
    let ordered = builder
        .relations
        .queries
        .ordered(state, start, end, budget.relation_limits);
    builder.require_domain_range(query.pointer, pointer, range);
    let mut status = combine_statuses([
        bounds,
        ordered,
        liveness_status(allocation.liveness()),
        if extent.end() <= allocation.size_bytes() && aligned {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Unknown
        },
    ]);
    if let Some(authority) = query.authority {
        if let Ok(permission) = permission_fact(state, authority) {
            builder.permission_range_access_obligations(
                authority,
                permission,
                PermissionAccessContext {
                    allocation: Some(id),
                    envelope,
                    pointer,
                    required_access: query.access,
                    access_bytes: 0,
                },
                Some(range),
            );
        } else {
            status = ObligationStatus::Unknown;
        }
    }
    if query.initialized {
        let empty = start.expression() == end.expression()
            || start
                .interval()
                .exact_value()
                .zip(end.interval().exact_value())
                .is_some_and(|(a, b)| a == b);
        let known = empty
            || envelope.is_some_and(|range| {
                allocation.initialization().classify(range) == InitializationClass::Initialized
                    && allocation.valid_value_bytes().contains(range)
            })
            || state.initialized_prefix_covers(
                id,
                element,
                range,
                budget.relation_limits,
                &builder.relations.queries,
            );
        status = combine_statuses([
            status,
            if known {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
        ]);
    }
    status = builder
        .obligations
        .iter()
        .fold(status, |s, o| combine_statuses([s, o.status()]));
    budget.relations = std::mem::take(&mut builder.relations.queries);
    Some((status, footprint))
}
